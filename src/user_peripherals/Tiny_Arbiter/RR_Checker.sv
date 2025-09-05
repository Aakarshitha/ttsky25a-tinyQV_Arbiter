// Author: Aakarshitha Suresh

// pac_rr_checker.sv
`timescale 1ns/1ps

module pac_rr_checker
(
  input  logic        clk,
  input  logic        rst_n,

  // DUT observability ports
  input  logic [3:0]  grant_vec,
  input  logic [1:0]  grant_idx,
  input  logic [3:0]  req_stub,
  input  logic        ready_stub,
  input  logic        valid_stub,

  // Weights (3-bit each) — pass as scalars for best tool compatibility
  input  logic [2:0]  w0,
  input  logic [2:0]  w1,
  input  logic [2:0]  w2,
  input  logic [2:0]  w3
);

  int unsigned wi;
  int unsigned n_active, max_w_act, tie_sz, bp_lvl;

  logic [3:0] elig_T, elig_T_d1;  // what the DUT actually gates on
  int         max_w_T;
  logic [3:0] gv_q;
  logic new_grant;

  logic [2:0] w_T     [4];  // weights as seen in cycle T
  logic [2:0] w_T_d1  [4];  // weights from previous cycle (T-1)

  logic [1:0] exp_idx_T, exp_idx_d1;
  logic [1:0] rr_ptr_sb;     // scoreboard mirror of RR pointer


/////////////////////////////////////////////////////////////////  
  // ---- helpers ---- //

// ---------- snapshots & expected-index pipeline ----------
  // Round-robin tie-breaker (same as scoreboard version)
  function automatic logic [1:0] rr_pick_first(input logic [3:0] mask,
                                               input logic [1:0] rr_ptr);
    for (int j = 0; j < 4; j++) begin
      logic [1:0] idx = (rr_ptr + j) % 4;  // was logic'(…)
      if (mask[idx]) return idx;
    end
    return rr_ptr; // shouldn't be used when mask==0
  endfunction

  // Expected index given eligibility and RR pointer
  function automatic logic [1:0] exp_idx(input logic [3:0] elig,
                                         input logic [1:0] rr_ptr);
    int unsigned maxw = 0;
    logic [3:0] tie = '0;
    // 1) find max among eligible
    for (int i = 0; i < 4; i++) begin
      if (elig[i]) begin
        int unsigned wi = f_weight(i); // uses w0..w3 via function below
        if (wi > maxw) maxw = wi;
      end
    end
    // 2) build tie mask
    for (int i = 0; i < 4; i++) begin
      tie[i] = elig[i] && (f_weight(i) == maxw);
    end
    // 3) RR among ties
    return rr_pick_first(tie, rr_ptr);
  endfunction

  // Snapshot every posedge; NBAs ensure preponed sees old values
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      // weights snapshot for f_weight_prev()
      for (int i=0;i<4;i++) begin
        w_T[i]    <= '0;
        w_T_d1[i] <= '0;
      end

      gv_q       <= '0;
      elig_T     <= '0;
      elig_T_d1  <= '0;
      max_w_T    <= '0;

      exp_idx_T  <= '0;
      exp_idx_d1 <= '0;
      rr_ptr_sb  <= '0;
    end else begin
      // weights as-seen-this-cycle (from ports)
      w_T_d1     <= w_T;
      w_T[0]     <= w0;
      w_T[1]     <= w1;
      w_T[2]     <= w2;
      w_T[3]     <= w3;

      // grant edge detect
      gv_q       <= grant_vec;

      // decision-time eligibility (match DUT gating)
      elig_T_d1  <= elig_T;
      // If selection also requires ready at pick time, use valid&ready:
      // elig_T     <= req_stub & {4{valid_stub & ready_stub}};
      elig_T     <= req_stub & {4{valid_stub}};

      // previous-cycle max weight (no $past needed)
      max_w_T    <= max_weight_elig(elig_T_d1);

      // expected index pipeline
      exp_idx_d1 <= exp_idx_T;
      exp_idx_T  <= exp_idx(elig_T, rr_ptr_sb);

      // mirror ROTATE rule: exit/advance when !req[curr] OR beat accepted

      if (grant_vec != 0) begin
        if (!req_stub[grant_idx] || (ready_stub && valid_stub))
          rr_ptr_sb <= (grant_idx + 1) % 4 ;  
      end
    end
  end


  function automatic int f_weight_prev (input int i);
    return (i>=0 && i<4) ? w_T_d1[i] : 0;
  endfunction

  function automatic int f_weight(input int i);
    case (i)
      0: return w0;
      1: return w1;
      2: return w2;
      3: return w3;
      default: return 0;
    endcase
  endfunction

  function automatic int max_weight_elig (logic [3:0] elig);
  	int mw = 0, wi;
    for (int i=0;i<4;i++) begin
       	if (elig[i]) begin
          //$display("\n elig[i] is true at i=%0d", i); //if(elig == 4'b0100)
          wi = f_weight(i); // <- DUT weights via the function above
          if (wi > mw) mw = wi;
        end
    end
  return mw;
  endfunction


  
  // compute new_grant from one-hot edge
  always_comb new_grant = (gv_q == 4'b0) && (grant_vec != 4'b0);


//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // ---- Assertions ----

  // New: expected-index check (decision@T → index@T+1)
  property p_gi_matches_expected_next;
    @(posedge clk) disable iff (!rst_n)
      $rose(new_grant) |=> (grant_idx == exp_idx_d1);
  endproperty

  assert property (p_gi_matches_expected_next)
    $display("[SB] OK PASSED Grant expectations t=%0t  gi=%0d  elig=%b  w={%0d,%0d,%0d,%0d}",
             $time, $sampled(grant_idx), $sampled(elig_T_d1),
             w0, w1, w2, w3);
  else
    $error("[SB] MISMATCH t=%0t  gi=%0d exp=%0d  elig=%b  w={%0d,%0d,%0d,%0d}",
           $time, $sampled(grant_idx), $sampled(exp_idx_d1), $sampled(elig_T_d1),
           w0, w1, w2, w3);
    
 /* property p_max_next;
      @(posedge clk) disable iff (!rst_n)
    $rose(new_grant) |=> ( f_weight_prev(grant_idx) == max_w_T );//was comparing to $past(max_w_T) before, was f_weight before
    endproperty
  assert property (p_max_next) $info("Passed This with fw1=%0d and sampled grant_idx=%0d \n", f_weight_prev(grant_idx), $sampled(grant_idx));//was f_weight before
    else begin
      automatic int gi1 = $sampled(grant_idx);//was $sampled(grant_idx)
      automatic int fw1 = f_weight_prev(gi1);
      $error("\n => Next-Cycle mismatch @%0t: gi1=%0d fw1=%0d mw_T(prev)=%0d elig_T(prev)=%b and current mw_T=%0d, current elig_T=%b",
             $time, gi1, fw1, $past(max_w_T), $past(elig_T), max_w_T, elig_T);
      $display("END");
     // $error("\n=> NEXT-CYCLE mismatch @%0t: gi=%0d fw1=%0d mw_T(prev)=%0d elig_T(prev)=%b ",
           //  $time, gi1, fw1, $past(max_w_T), $past(elig_T));
  end*/ //commented for now

  property p_no_x_on_grant_bus;
    @(posedge clk) disable iff (!rst_n)
      !(^grant_vec === 1'bx) && !(^grant_idx === 1'bx);
  endproperty
  assert property (p_no_x_on_grant_bus);

  property p_onehot_or_zero;
    @(posedge clk) disable iff (!rst_n)
      $countones(grant_vec) <= 1;
  endproperty
  assert property (p_onehot_or_zero);

  property p_vec_matches_idx;
    @(posedge clk) disable iff (!rst_n)
      (grant_vec == 4'b0) || (grant_vec == (4'b0001 << grant_idx));
  endproperty
  assert property (p_vec_matches_idx);

  property p_no_rotate_without_accept;
    @(posedge clk) disable iff (!rst_n)
      (grant_vec != 0 && !(ready_stub && valid_stub)) |=> $stable(grant_idx);
  endproperty
  assert property (p_no_rotate_without_accept);


    
///////////////////////////////////////////////////////////////////////////////////////////
  // ---- Coverage ----
 // ---------- Previous grant index & packed transition pair ----------
  logic [1:0] grant_idx_q;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)        grant_idx_q <= '0;
    else if (grant_vec != 0) grant_idx_q <= grant_idx;  // sample only when grant exists
  end

  logic [3:0] trans_pair;
  always_comb trans_pair = {grant_idx_q, grant_idx};     // {prev, curr}

  // ---------- Active requester count (context) ----------

  // ---------- Coverage: transitions + n_active context ----------
  covergroup cg_rr_trans_active @(posedge clk);
    option.per_instance = 1;

    // How many requesters are active this cycle
    cp_n_active : coverpoint n_active {
      bins one   = {1};
      bins two   = {2};
      bins three = {3};
      bins four  = {4};
    }

    // Transition bins using packed {prev,curr}; sample only when a grant exists
    cp_trans : coverpoint trans_pair iff (grant_vec != 0) {
      // Holds: 00->00, 01->01, 10->10, 11->11
      bins hold[]    = {4'b0000, 4'b0101, 4'b1010, 4'b1111};

      // Forward RR rotations (expected when all requesters are active & beats accepted)
      // 0->1, 1->2, 2->3, 3->0
      bins rot_fwd[] = {4'b0001, 4'b0110, 4'b1011, 4'b1100};

      // Everything else (skips, re-seeds, reverse, etc.)
      bins other     = default;
    }

    // Cross: which transitions occur under which active-set sizes
    cr_trans_active : cross cp_trans, cp_n_active;
  endgroup

  cg_rr_trans_active cov_rr_trans_active = new();

endmodule
