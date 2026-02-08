// Formal Verification Harness for 5-stage Pipeline
module pipeline_formal_check (
    input logic clk,
    input logic rst,
    input logic [31:0] instr,
    input logic [31:0] a,
    input logic [31:0] b,
    output logic [31:0] result
);

    picorv32_pipeline_5stage dut (.clk(clk), .rst(rst), .instr(instr), .a(a), .b(b), .result(result));
    assumptions env (.clk(clk), .rst(rst), .instr(instr), .a(a), .b(b), .result(result));

    // -------------------------
    // Assertions (design correctness)
    // -------------------------

    // ADD correctness
    assert property (@(posedge clk) instr[3:0] == 4'b0000 |-> result == a + b);

    // SUB correctness
    assert property (@(posedge clk) instr[3:0] == 4'b0001 |-> result == a - b);

    // Hazard detection: result must not be written before execute completes
    property hazard_free;
        @(posedge clk) disable iff (rst)
        (instr[3:0] == 4'b0000) |-> ##[3] (result == a + b); // 3 cycles latency
    endproperty
    assert property (hazard_free);

    // -------------------------
    // Advanced Checks
    // -------------------------

    // Reachability: pipeline must eventually produce a result after reset
    property reachability;
        @(posedge clk) disable iff (rst)
        ##[1:$] (result !== 32'h0);
    endproperty
    assert property (reachability);

    // Deadlock freedom: pipeline must not stall indefinitely
    property no_deadlock;
        @(posedge clk) disable iff (rst)
        always (instr[3:0] <= 4'b0100) |-> eventually (result !== 32'hDEAD_BEEF);
    endproperty
    assert property (no_deadlock);

    // Livelock freedom: pipeline must not loop without progress
    property no_livelock;
        @(posedge clk) disable iff (rst)
        (instr[3:0] <= 4'b0100) |-> ##[1:10] (result == a + b || result == a - b ||
                                              result == (a & b) || result == (a | b) ||
                                              result == (a ^ b));
    endproperty
    assert property (no_livelock);

endmodule