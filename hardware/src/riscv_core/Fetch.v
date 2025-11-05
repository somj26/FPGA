
`define PC_Flush_Target 'h00000000
//`define PC_Reset_Target 'h10000000
`define NOP 'h00000000
`define INST_LEN 'd32

module Fetch #(
	parameter RESET_PC = 32'h4000_0000
)(
    input clk,
    input reset, 
    input [`INST_LEN-1:0] alu_in,
    input PCSel,
    input IFFlush, 
    input IFStall,
    output reg [`INST_LEN-1:0] IFID_PC,
    output [`INST_LEN-1:0] PC
);
    reg [`INST_LEN-1:0] pc;
    wire [`INST_LEN-1:0] pc_4;
    wire [`INST_LEN-1:0] pc_in;
    
    assign pc_4 = pc + 'd4;
    assign pc_in = (PCSel) ? alu_in : pc_4;

    always @(posedge clk) begin
	if (reset) begin 
		pc <= RESET_PC; 
		IFID_PC <= RESET_PC;
	end else if(IFFlush) begin 
		pc <= (PCSel) ? alu_in : pc_4; //Needs to be fixed to correct address
		IFID_PC <= `NOP;
	end else if(IFStall) begin
		pc <= pc;
		IFID_PC <= IFID_PC;
	end else begin 
		pc <= pc_in;
		IFID_PC <= pc;
        end
   end

   assign PC = pc; 

endmodule

