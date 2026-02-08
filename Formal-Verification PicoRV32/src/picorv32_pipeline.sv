module picorv32_pipeline (
    input  logic        clk,
    input  logic        rst,
    input  logic [31:0] instr,
    input  logic [31:0] a,
    input  logic [31:0] b,
    output logic [31:0] result
);

    logic [31:0] decode_op;
    logic [31:0] alu_out;

    // Decode stage
    always_ff @(posedge clk or posedge rst) begin
        if (rst) decode_op <= 0;
        else decode_op <= instr[6:0]; // simplified opcode extraction
    end

    // Execute stage (ALU)
    picorv32_alu alu (
        .a(a),
        .b(b),
        .alu_op(decode_op[3:0]),
        .result(alu_out)
    );

    // Writeback stage
    always_ff @(posedge clk or posedge rst) begin
        if (rst) result <= 0;
        else result <= alu_out;
    end

endmodule