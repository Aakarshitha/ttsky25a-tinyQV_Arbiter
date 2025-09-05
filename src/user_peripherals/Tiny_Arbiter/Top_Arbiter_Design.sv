// Author: Aakarshitha Suresh

// =============================================================
// PAC‑RR Arbiter MVP — SystemVerilog Skeletons (EDA Playground Ready)
// Weighted RR + Burst Caps(later) + Simple Aging (later, +1 bump) + Optional Lock Cap(later)
// Backpressure‑safe (no ready comb loops)
// =============================================================


/////////////////////////
////TOP Module////

// ============================
// tqvp_pac_rr.sv (MVP wrapper)
// ============================
`default_nettype none
`timescale 1ns/1ps

module tqvp_pac_rr import pac_rr_pkg::*; (
    input         clk,
    input         rst_n,

    input  [7:0]  ui_in,
    output [7:0]  uo_out,

    input  [3:0]  address,
    input         data_write,
    input  [7:0]  data_in,
    output [7:0]  data_out
);

    // Config registers
    reg [2:0] weight [3:0];

    // Status wires
    logic [3:0] grant_vec;
    logic       busy;
    logic [1:0] grant_idx;


  	// Inside DUT
    logic [2:0] weight      [4];
    logic [2:0] weight_shad [4];
    logic       commit_pulse;   // write 1 to a CTRL reg to pulse this

    always_ff @(posedge clk or negedge rst_n) begin
      if (!rst_n) begin
        for (int k=0;k<4;k++) begin
          weight[k]      <= 3'd1;
          weight_shad[k] <= 3'd1;
        end
      end else begin
        // normal single-address writes update the SHADOW
        if (data_write) begin
          unique case (address)
            4'h2: weight_shad[0] <= data_in[2:0];
            4'h3: weight_shad[1] <= data_in[2:0];
            4'h4: weight_shad[2] <= data_in[2:0];
            4'h5: weight_shad[3] <= data_in[2:0];
            4'h6: commit_pulse   <= data_in[0]; // CTRL: write 1 to commit
            default: ;
          endcase
        end

        // one-cycle later, apply atomically
        if (commit_pulse) begin
          for (int k=0;k<4;k++) weight[k] <= weight_shad[k];
          commit_pulse <= 1'b0; // auto-clear (or clear via write)
        end
      end
    end

    // Config struct
    pac_cfg_t cfg;
    always @(*) begin
      for (int i = 0; i < 4; i++)
        cfg.weight[i] = weight[i];
    end

    // Test/SoC stubs (TB drives these hierarchically)
    logic [3:0] req_stub;
    logic       ready_stub;
    logic       valid_stub;

    pac_rr_core u_core (
      .clk_i(clk), .rst_ni(rst_n),
      .req_i(req_stub),
      .sink_ready_i(ready_stub), .src_valid_i(valid_stub),
      .grant_o(grant_vec), .grant_idx_o(grant_idx), .busy_o(busy),
      .cfg_i(cfg)
    );

    // Readback map
    assign data_out =
        (address == 4'h2) ? {5'b0, weight[0]} :
        (address == 4'h3) ? {5'b0, weight[1]} :
        (address == 4'h4) ? {5'b0, weight[2]} :
        (address == 4'h5) ? {5'b0, weight[3]} :
        (address == 4'hE) ? {5'b0, busy, grant_idx} :
        (address == 4'hF) ? {4'b0, grant_vec} :
        8'h0;

    assign uo_out = 8'h00; // unused PMOD pins

endmodule
