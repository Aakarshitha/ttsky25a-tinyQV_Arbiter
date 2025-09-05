// Author: Aakarshitha Suresh

// ============================
// pac_rr_core.sv (MVP core logic)
// ============================
`timescale 1ns/1ps

module pac_rr_core import pac_rr_pkg::*; (
  input  logic                 clk_i,
  input  logic                 rst_ni,

  input  logic [N-1:0]         req_i,
  input  logic                 sink_ready_i,
  input  logic                 src_valid_i,

  output logic [N-1:0]         grant_o,
  output idx_t                 grant_idx_o,
  output logic                 busy_o,

  input  pac_cfg_t             cfg_i
);
  // Beat accepted when handshake succeeds
  wire beat_accepted = sink_ready_i & src_valid_i & grant_o[grant_idx_o];

  // Registered winner/current grant
  idx_t curr_q, curr_d;

  // RR pointer
  idx_t rr_ptr_q, rr_ptr_d;

  // FSM state
  typedef enum logic [1:0] {IDLE, PICK, SERVE, ROTATE} state_e;
  state_e st_q, st_d;

  // Contenders and selector
  logic [N-1:0] contenders;
  idx_t sel_idx;

  always_comb begin
    contenders = req_i;
    sel_idx    = rr_argmax(contenders, cfg_i.weight, rr_ptr_q);
  end

  // FSM
  always_comb begin
    st_d        = st_q;
    curr_d      = curr_q;
    rr_ptr_d    = rr_ptr_q;

    grant_o     = '0;
    grant_idx_o = curr_q;
    busy_o      = (st_q != IDLE);

    case (st_q)
      IDLE: begin
        if (|contenders) st_d = PICK;
      end

      PICK: begin
        if (|contenders) begin
          curr_d = sel_idx;
          st_d   = SERVE;
        end else begin
          st_d = IDLE;
        end
      end

	  SERVE: begin
        // only drive grant when it actually makes sense
        if (req_i[curr_q] && src_valid_i)
          grant_o[curr_q] = 1'b1;

        // leave SERVE if request vanished or a beat was accepted
        if (!req_i[curr_q] || (sink_ready_i && src_valid_i && grant_o[curr_q]))
          st_d = ROTATE;
      end


      ROTATE: begin
        rr_ptr_d = idx_t'((curr_q + 1) % N);
        st_d     = PICK;
      end
    endcase
  end

  // Registers
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      st_q     <= IDLE;
      curr_q   <= '0;
      rr_ptr_q <= '0;
    end else begin
      st_q     <= st_d;
      curr_q   <= curr_d;
      rr_ptr_q <= rr_ptr_d;
    end
  end

endmodule : pac_rr_core
