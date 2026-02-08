// Simplified 5-stage RISC-V pipeline: Fetch, Decode, Execute, Memory, Writeback
module picorv32_pipeline_5stage (
    input  logic        clk,
    input  logic        rst,
    input  logic [31:0] instr,
    input  logic [31:0] a,
    input  logic [31:0] b,
    output logic [31:0] result
);

    logic [31:0] fetch_reg, decode_reg, execute_reg, mem_reg, wb_reg;
    logic [3:0] alu_op;
    logic [31:0] alu_out;

    // Fetch stage
    always_ff @(posedge clk or posedge rst) begin
        if (rst) fetch_reg <= 0;
        else fetch_reg <= instr;
    end

    // Decode stage
    always_ff @(posedge clk or posedge rst) begin
        if (rst) decode_reg <= 0;
        else decode_reg <= fetch_reg;
        alu_op <= fetch_reg[3:0]; // simplified opcode extraction
    end

    // Execute stage
    picorv32_alu alu (.a(a), .b(b), .alu_op(alu_op), .result(alu_out));
    always_ff @(posedge clk or posedge rst) begin
        if (rst) execute_reg <= 0;
        else execute_reg <= alu_out;
    end

    // Memory stage (pass-through for simplicity)
    always_ff @(posedge clk or posedge rst) begin
        if (rst) mem_reg <= 0;
        else mem_reg <= execute_reg;
    end

    // Writeback stage
    always_ff @(posedge clk or posedge rst) begin
        if (rst) wb_reg <= 0;
        else wb_reg <= mem_reg;
    end

    assign result = wb_reg;

endmodule