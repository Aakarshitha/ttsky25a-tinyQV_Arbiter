# tests/test_pac_rr.py
import os, random
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles
from tqv import TinyQV

PERIPHERAL_NUM = 32  # 16 + 16 (your design index)

# --------- Tiny “task” shim that mirrors your SV TB ---------
class ArbiterTB:
    def __init__(self, dut, tqv: TinyQV):
        self.dut = dut
        self.tqv = tqv

    # SV: write_reg(addr,val) -> TinyQV
    async def write_reg(self, addr: int, val: int):
        await self.tqv.write_reg(addr & 0xF, val & 0xFF)

    # SV: read_reg(addr,val) -> TinyQV
    async def read_reg(self, addr: int) -> int:
        return (await self.tqv.read_reg(addr & 0xF)) & 0xFF

    # SV: cfg_weights(w0..w3) + commit @ 0x6
    async def cfg_weights(self, w0: int, w1: int, w2: int, w3: int):
        await self.write_reg(0x2, w0 & 0x7)
        await self.write_reg(0x3, w1 & 0x7)
        await self.write_reg(0x4, w2 & 0x7)
        await self.write_reg(0x5, w3 & 0x7)
        await self.write_reg(0x6, 0x01)   # commit shadow -> live
        await ClockCycles(self.dut.clk, 1)

    # SV: drive internal stubs (req_stub/ready_stub/valid_stub)
    async def drive_stubs(self, reqs: int, ready: int, valid: int):
        self.dut.req_stub.value   = reqs & 0xF
        self.dut.ready_stub.value = 1 if ready else 0
        self.dut.valid_stub.value = 1 if valid else 0
        await ClockCycles(self.dut.clk, 1)

    # SV: read_grant_idx + read_grant_vec from readback map
    async def read_grant_idx(self):
        rE = await self.read_reg(0xE)   # {5'b0, busy, gi[1:0]}
        gi   =  rE        & 0x3
        busy = (rE >> 2)  & 0x1
        return gi, busy

    async def read_grant_vec(self):
        rF = await self.read_reg(0xF)   # {4'b0, gv[3:0]}
        return rF & 0xF

    async def show_grant_status(self, tag="RB"):
        gi, busy = await self.read_grant_idx()
        gv = await self.read_grant_vec()
        self.dut._log.info(f"[{tag}] t={cocotb.utils.get_sim_time('ns')}  busy={busy}  gi={gi}  gv={gv:04b}")
        return gi, gv, busy

    # SV: trial_reset()
    async def trial_reset(self):
        self.dut.rst_n.value = 0
        await ClockCycles(self.dut.clk, 2)
        self.dut.rst_n.value = 1
        await ClockCycles(self.dut.clk, 1)


# Python port of your arbiter_cfg “randomize”
class ArbiterCfg:
    def __init__(self, rnd: random.Random):
        self.rnd = rnd

    def randomize(self, force_rv11=False):
        # weights in [0..4] with ~10% zeros, ~90% non-zero (like your dist)
        def w():
            return self.rnd.choices([0,1,2,3,4], weights=[1,9,9,9,9], k=1)[0]
        weights = [w(), w(), w(), w()]

        # reqs != 0
        reqs = 0
        while reqs == 0:
            reqs = self.rnd.randrange(1, 16)

        # rv_code distribution (70% 11, 10/01/00 = 10% each), or forced 11
        if force_rv11:
            ready = 1; valid = 1
        else:
            rv_choice = self.rnd.choices([0b11,0b10,0b01,0b00], weights=[70,10,10,10], k=1)[0]
            ready = (rv_choice >> 1) & 1
            valid = (rv_choice >> 0) & 1

        return dict(w=weights, reqs=reqs, ready=ready, valid=valid)

    @staticmethod
    def show(dut, tag, s):
        w = s["w"]; reqs = s["reqs"]; ready=s["ready"]; valid=s["valid"]
        dut._log.info(
            f"[{tag}] w={w[0]}:{w[1]}:{w[2]}:{w[3]}  reqs={reqs:04b} "
            f"(r0={reqs&1} r1={(reqs>>1)&1} r2={(reqs>>2)&1} r3={(reqs>>3)&1}) "
            f"ready={ready} valid={valid}"
        )


@cocotb.test()
async def test_project(dut):
    # Clock: template uses 100 ns; keep it unless you need 10 ns like SV TB
    cocotb.start_soon(Clock(dut.clk, 100, units="ns").start())

    # TinyQV bridge
    tqv = TinyQV(dut, PERIPHERAL_NUM)
    await tqv.reset()

    tb  = ArbiterTB(dut, tqv)

    # === Test 1: Equal Weights 1:1:1:1 (directed anchor) ===
    await tb.cfg_weights(1,1,1,1)
    await tb.drive_stubs(reqs=0b1111, ready=1, valid=1)
    for _ in range(12):
        await tb.show_grant_status("T1")

    # === Test 2: Weighted 2:1:1:2 (directed) ===
    await tb.cfg_weights(2,1,1,2)
    await tb.drive_stubs(reqs=0b1111, ready=1, valid=1)
    for _ in range(20):
        await tb.show_grant_status("T2")

    # === Test 3: Randomized Trials (Python RNG = your constraints) ===
    SEED   = int(os.getenv("SEED",   "2"))
    TRIALS = int(os.getenv("TRIALS", "8"))
    CYCLES = int(os.getenv("CYCLES", "10"))
    rnd = random.Random(SEED)
    cfg = ArbiterCfg(rnd)

    await ClockCycles(dut.clk, 5)
    for t in range(TRIALS):
        s = cfg.randomize(force_rv11=True)   # like your inline with { rv_code==2'b11; }
        ArbiterCfg.show(dut, f"RAND t={t}", s)

        await tb.cfg_weights(*s["w"])
        await tb.drive_stubs(s["reqs"], s["ready"], s["valid"])

        for _ in range(CYCLES):
            await tb.show_grant_status(f"T3 t={t}")
