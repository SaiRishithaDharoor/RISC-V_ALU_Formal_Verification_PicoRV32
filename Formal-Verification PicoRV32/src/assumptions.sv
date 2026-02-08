// Environment constraints for formal verification
module assumptions (
    input logic clk,
    input logic rst,
    input logic [31:0] instr,
    input logic [31:0] a,
    input logic [31:0] b,
    output logic [31:0] result
);

    // Reset initializes pipeline correctly
    assume property (@(posedge clk) rst |-> result == 0);

    // Only valid ALU opcodes allowed (ADD, SUB, AND, OR, XOR)
    assume property (instr[3:0] <= 4'b0100);

    // Inputs stable during execution cycle
    assume property (@(posedge clk) !rst |-> $stable(a) && $stable(b));

endmodule