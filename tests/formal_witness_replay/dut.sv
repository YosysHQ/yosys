module dut (
    input  logic clk,
    input  logic req,
    input  logic ack
);

`ifdef FORMAL

  logic [1:0] reqs_seen;

  // Deterministic initial state for the internal counter.
  initial reqs_seen = 2'b00;

  always @ (posedge clk) begin
    if (req)
      reqs_seen <= reqs_seen + 1'b1;
  end

  // Req is only high for one cycle.
  assume property (@(posedge clk) req |-> ##1 !req);

  // Reqs are at least 8 cycles apart.
  assume property (@(posedge clk) req |-> ##1 (!req [*7]));

  // Ack comes exactly 4 cycles after req.
  assume property (@(posedge clk) req |-> ##4 ack);

  // Ack must remain low if no req 4 cycles ago.
  assume property (@(posedge clk) !$past(req,4) |-> !ack);

  // Phase 1: stop exactly when the second request is seen.
  always @ (posedge clk) begin
    (* phase = "1" *)
    cover(reqs_seen == 2);
  end

  // Phase 2: forbid more reqs and cover the pending ack.
  always @ (posedge clk) begin
    (* phase = "2" *)
    assume(!req);
    (* phase = "2" *)
    cover(ack);
  end

`endif

endmodule
