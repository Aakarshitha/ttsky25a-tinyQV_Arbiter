// Author: Aakarshitha Suresh

// ============================
// testbench_mvp.sv
// ============================

`timescale 1ns/1ps
import pac_rr_pkg::*;

typedef class arbiter_cfg;//forward declaration

module tb_pac_rr_mvp;

  // -------------------
  // Clock & Reset
  // -------------------
  logic clk, rst_n;
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // -------------------
  // Byte-peripheral bus signals
  // -------------------
  logic [7:0] ui_in;
  wire  [7:0] uo_out;
  logic [3:0] address;
  logic       data_write;
  logic [7:0] data_in;
  wire  [7:0] data_out;

  int SEED, TRIALS, CYCLES;

  // DUT
  tqvp_pac_rr dut (
    .clk(clk), .rst_n(rst_n),
    .ui_in(ui_in), .uo_out(uo_out),
    .address(address), .data_write(data_write),
    .data_in(data_in), .data_out(data_out)
  );

  // In tb_pac_rr_mvp (after DUT instantiation is fine)
  bind tqvp_pac_rr pac_rr_checker u_pac_rr_checker (
    .clk        (clk),
    .rst_n      (rst_n),

    // Connect to wrapper-internal signals by name
    .grant_vec  (grant_vec),
    .grant_idx  (grant_idx),
    .req_stub   (req_stub),
    .ready_stub (ready_stub),
    .valid_stub (valid_stub),

    // Weights (break out 4 scalars; avoids array-port tool quirks)
    .w0         (weight[0]),
    .w1         (weight[1]),
    .w2         (weight[2]),
    .w3         (weight[3])
  );


  // Include assertions + coverage here (references `dut.*`)
 // `include "pac_rr_asserts_cov.sv"

  // -------------------
  // Helper Tasks (unchanged)
  // -------------------
  task write_reg(input [3:0] addr, input [7:0] val);
    @(negedge clk);
    address    <= addr;
    data_in    <= val;
    data_write <= 1;
    //was @(negedge clk);
    @(posedge clk);
    data_write <= 0;
  endtask

  task automatic read_reg(input [3:0] addr, output [7:0] val);
    @(negedge clk);
    address <= addr;
    @(negedge clk);
    val = data_out;
  endtask

  task automatic trial_reset();
    rst_n = 1'b0;                 // assert reset
    repeat (2) @(posedge clk);    // hold for a couple of clocks
    rst_n = 1'b1;                 // deassert reset
    @(posedge clk);               // 1-cycle warmup
  endtask


  // Configure weights
  task automatic cfg_weights(input byte w0, w1, w2, w3);
    write_reg(4'h2, {5'b0,w0[2:0]});
    write_reg(4'h3, {5'b0,w1[2:0]});
    write_reg(4'h4, {5'b0,w2[2:0]});
    write_reg(4'h5, {5'b0,w3[2:0]});
    write_reg(4'h6, 8'h01);//coomit pulse value to be given as 1 to commi thw shadow reg weights to the act6ual weights(to make sure all weights get updated at same cycle.
  endtask

  // Read {5'b0, busy, grant_idx[1:0]} from 0xE
  task automatic read_grant_idx(output logic [1:0] gi,
                                output logic       busy);
    byte rd;
    read_reg(4'hE, rd);     // direct literal address
    gi   = rd[1:0];
    busy = rd[2];
  endtask

  // Read {4'b0, grant_vec[3:0]} from 0xF
  task automatic read_grant_vec(output logic [3:0] gv);
    byte rd;
    read_reg(4'hF, rd);     // direct literal address
    gv = rd[3:0];
  endtask

  // Convenience: read & print both (uses literals internally)
  task automatic show_grant_status(string tag="RB");
    byte rE, rF;
    read_reg(4'hE, rE);
    read_reg(4'hF, rF);
    $display("[%s] t=%0t  busy=%0b  gi=%0d  gv=%04b \n",
             tag, $time, rE[2], rE[1:0], rF[3:0]);
  endtask

  arbiter_cfg sc = new();//class arbiter_cfg is at the end

  // -------------------
  // Minimal Test Stimulus (+ random phase)
  // -------------------
  initial begin
    // Reset
    rst_n         = 0;
    ui_in         = 8'h00;
    address       = 4'h0;
    data_write    = 0;
    data_in       = 8'h00;
    dut.req_stub   = 0;
    dut.ready_stub = 0;
    dut.valid_stub = 0;

    repeat (5) @(negedge clk);
    rst_n = 1;
    repeat (2) @(negedge clk);

    
    //Commented for now//
    
    // === Test 1: Equal Weights (1:1:1:1) — Directed anchor ===
    /*$display("\n=== Test 1: Equal Weights 1:1:1:1 ===");
    cfg_weights(1,1,1,1);
    dut.req_stub   = 4'b1111; // all masters request (use 1111, not 1110)
    dut.ready_stub = 1;
    dut.valid_stub = 1;

   // repeat (12) begin
    //  @(negedge clk);
    //  $display("t=%0t gi=%0d gv=%b", $time, dut.grant_idx, dut.grant_vec);
    end
    
    
  // read & print busy/gi/gv a bunch of times
  repeat (12) begin
    show_grant_status("T1");
  end
    
    */

    //commented for now//
    
 /*   // === Test 2: Weighted (2:1:1:2) — Directed ===
    $display("\n=== Test 2: Weighted 2:1:1:2 ===");
    cfg_weights(2,1,1,2);
    dut.req_stub   = 4'b1111;
    dut.ready_stub = 1;
    dut.valid_stub = 1;

  //  repeat (20) begin
  //    @(negedge clk);
  //    $display("t=%0t gi=%0d gv=%b", $time, dut.grant_idx, dut.grant_vec);
  //  end
  
    repeat (2) @(negedge clk);
    repeat (20) begin
      show_grant_status("T2");
    end
  */



    // === Test 3: Seed-driven constrained-random trials ===

    
    if (!$value$plusargs("SEED=%d",   SEED))   SEED   = 2;
    if (!$value$plusargs("TRIALS=%d", TRIALS)) TRIALS = 3;//was 20
    if (!$value$plusargs("CYCLES=%d", CYCLES)) CYCLES = 10;

    $display("\n=== Test 3: Randomized Trials (SEED=%0d TRIALS=%0d CYCLES=%0d) ===", SEED, TRIALS, CYCLES);
   // void'($urandom(SEED));
    sc.srandom(SEED);  

    repeat (10) @(negedge clk);

    for (int t = 0; t < TRIALS; t++) begin
      // Generate a new scenario
      assert(sc.randomize()with { rv_code == 2'b11; })
        else $fatal(1, "[RAND] randomize failed at trial %0d", t);
      sc.apply();
      sc.show($sformatf("RAND t=%0d", t));

    // sample readback CYCLES times
    for (int c = 0; c < CYCLES; c++) begin
      show_grant_status($sformatf("T3 t=%0d c=%0d", t, c));
            //each show_grant_status() internally does two read_reg() calls; each read_reg() waits two negedges. so one show_grant_status() eats 4 negedges worth of sim time.
    end
      
    end
 	

    $finish;
  end

  // -------------------
  // Dump Waves
  // -------------------
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars(0, tb_pac_rr_mvp);
  end

endmodule



  // -------------------
  // Constrained-random scenario class
  // -------------------
  class arbiter_cfg;
    // Randomizable knobs (MVP: 4 masters, 3-bit weights)
    rand bit [2:0] w [4];    // weights: 0..7 (0 can be used to "mute" a master)
    rand bit [3:0] reqs;     // requester bitmap (at least one active)
    rand bit       ready;    // sink ready
    rand bit       valid;    // source valid

    // Constraints:
    //  - At least one requester active
    //  - Bias towards “useful” ready/valid (avoid always-0 deadlock)
    //  - Optionally keep some weights nonzero most of the time
    constraint c_reqs_nonzero { reqs != 4'b0000; }

	// weights: 10% zero, 90% non-zero
    constraint c_weight_range  { foreach (w[i]) w[i] inside {[0:4]}; }//was 0:7
    constraint c_weight_bias   { foreach (w[i]) w[i] dist { 3'd0 := 1, [3'd1:3'd7] := 9 }; }

    // joint ready/valid distribution via a 2-bit code
    rand bit [1:0] rv_code; // {ready,valid}
    constraint c_rv_code_dist {
      rv_code dist { 2'b11 := 70, 2'b10 := 10, 2'b01 := 10, 2'b00 := 10 };
    }
    constraint c_rv_map {
      ready == rv_code[1];
      valid == rv_code[0];
    }

    // Apply to DUT via existing tasks / TB signals
    task apply();
      tb_pac_rr_mvp.cfg_weights({5'b0,w[0]}[2:0], {5'b0,w[1]}[2:0], {5'b0,w[2]}[2:0], {5'b0,w[3]}[2:0]);
      tb_pac_rr_mvp.dut.req_stub   = reqs;
      tb_pac_rr_mvp.dut.ready_stub = ready;
      tb_pac_rr_mvp.dut.valid_stub = valid;
    endtask

    // Pretty-print for debug
    function void show(string tag="RAND");
      $display("\n=====> Pretty Print for Debug is this [%s] w = w[0]:%0d, w[1]:%0d, w[2]:%0d, w[3]:%0d  reqs=%b with reqs[0]=%b, reqs[1]=%b, reqs[2]=%b and reqs[3]=%b,  ready=%0b valid=%0b <=====",
               tag, w[0], w[1], w[2], w[3], reqs, reqs[0], reqs[1], reqs[2], reqs[3], ready, valid);
    endfunction

  endclass
