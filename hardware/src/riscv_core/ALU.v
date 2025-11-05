`include "opcode.vh"
`define ALU_OP_LEN 'd16
`define ALU_SEL_SIZE $clog2(`ALU_OP_LEN)
`define INST_LEN 'd32

module ALU (
    input [`INST_LEN-1:0] ALU_A,
    input [`INST_LEN-1:0] ALU_B,
    input [`ALU_SEL_SIZE-1:0] ALU_SEL,
    output reg [`INST_LEN-1:0] ALU_OUT
);

    localparam ADD = 4'd0;
    localparam SUB = 4'd1;
    localparam AND = 4'd2;
    localparam OR = 4'd3;
    localparam XOR = 4'd4;
    localparam SLL = 4'd5;
    localparam SLT = 4'd6;
    localparam SLTU = 4'd7;
    localparam SRA = 4'd8;
    localparam SRL = 4'd9;
    localparam PASS = 4'd10;
    localparam CSR_PASS = 4'd11;
    localparam DEFAULT = 4'b1111;

    always @(*) begin
	     case (ALU_SEL) 
		     ADD : ALU_OUT = ALU_A + ALU_B;
		     SUB : ALU_OUT = ALU_A - ALU_B;
		     AND : ALU_OUT = ALU_A & ALU_B;
		     OR : ALU_OUT = ALU_A | ALU_B;
		     XOR : ALU_OUT = ALU_A ^ ALU_B;
		     SLL : ALU_OUT = ALU_A << ALU_B[4:0];
		     SLT : ALU_OUT = ($signed(ALU_A) < $signed(ALU_B)) ? 1'b1 : 1'b0;
		     SLTU : ALU_OUT = (ALU_A < ALU_B) ? 1'b1 : 1'b0;
		     SRL : ALU_OUT = ALU_A >> ALU_B[4:0];
		     SRA : ALU_OUT = ($signed(ALU_A)) >>> ALU_B[4:0];
		     PASS : ALU_OUT = ALU_B;
		     CSR_PASS : ALU_OUT = ALU_A;
		     default : ALU_OUT = 0;
	     endcase
     end
endmodule
