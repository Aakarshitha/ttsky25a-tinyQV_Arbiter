// Author: Aakarshitha Suresh

// ============================
// pac_rr_pkg.sv (MVP package)
// ============================
`timescale 1ns/1ps

package pac_rr_pkg;
  parameter int N = 4;   // number of requesters
  parameter int W = 3;   // weight width

  typedef logic [$clog2(N)-1:0] idx_t;

  // Rotate-first-one after rr_ptr (wrap around)
  function automatic idx_t rr_pick_first(
      input logic [N-1:0] mask,
      input idx_t         rr_ptr
  );
    logic [2*N-1:0] rot;
    rot = {mask, mask};

    for (int i = 0; i < N; i++) begin
      if (rot[rr_ptr + i])
        return idx_t'((rr_ptr + i) % N);
    end
    return rr_ptr;
  endfunction

  // Argmax with RR tie-break
  function automatic idx_t rr_argmax(
      input logic [N-1:0]           contenders,
      input logic [W-1:0]           weight [N],
      input idx_t                   rr_ptr
  );
    logic [W-1:0] max_w = '0;
    logic [N-1:0] tie_mask;

    for (int k = 0; k < N; k++) begin
      if (contenders[k] && (weight[k] > max_w))
        max_w = weight[k];
    end
    for (int k = 0; k < N; k++) begin
      tie_mask[k] = contenders[k] && (weight[k] == max_w);
    end
    return rr_pick_first(tie_mask, rr_ptr);
  endfunction

  // Simple config container
  typedef struct {
    logic [W-1:0] weight[N];
  } pac_cfg_t;

endpackage : pac_rr_pkg

