`define RESET_PIPELINE_REG 'h00000000
`define NOP 'h00000000
`define INST_LEN 'd32

//`include "ALU.v"
//`include "Branch_Comp.v"
//`include "Imm_Gen.v"
//`include "reg_file.v"
//`include "alu_control.v"

module Decode_Execute (
     input clk, 
     input reset,
     input [31:0] inst,
     input [31:0] wb_forward,
     input [31:0] alu_forward,
     input [31:0] pc,
     input BrUN,
     input [1:0] A_fwd_sel,
     input [1:0] B_fwd_sel,
     input A_Sel,
     input B_Sel,
     input DXFlush, 
     input DXStall, 
     input [31:0] dataA, 
     input [31:0] dataB, 
     input [31:0] imm,
     output reg [31:0] pc_DX,
     output reg [31:0] alu_DX,
     output reg [31:0] inst_DX,
     output BrEQ, 
     output BrLT,
     output UART_Tx_ON,
     output UART_Rx_ON,
     output UART_Control_ON,
     output UART_RESET_CLK,
     output UART_CLK_COUNT, 
     output UART_INS_COUNT, 
     output UART_BCC, 
     output UART_BCCS,
     output [31:0] alu_out_dx,
//     output reg [31:0] csr_write_data,
     output [13:0] addr_DMEM, 
     output [31:0] data_DMEM
);

     wire [4:0] addrA; 
     wire [4:0] addrB;
     wire [2:0] funct3; 
     wire [6:0] funct7; 
     wire [6:0] opcode; 
     wire [31:0] alu_out; 

     assign addrA = inst[19:15];
     assign addrB = inst[24:20]; 
     assign opcode = inst[6:0];
     assign funct3 = inst[14:12];
     assign funct7 = inst[31:25]; 

     reg [31:0] rs1;
     reg [31:0] rs2;
     wire [31:0] aluA;
     wire [31:0] aluB;
     reg [3:0] ALU_SEL;

     ALU_Control alu_control_inst(
	     .inst(inst),
	     .alu_ctrl(ALU_SEL)
     );

     always @(*) begin
	     case (A_fwd_sel) 
		     2'b00 : rs1 = dataA;
		     2'b01 : rs1 = alu_forward;
		     2'b10 : rs1 = wb_forward;
		     default : rs1 = 'd0;
	     endcase

	     case (B_fwd_sel)
		     2'b00 : rs2 = dataB;
		     2'b01 : rs2 = alu_forward;
		     2'b10 : rs2 = wb_forward;
		     default : rs2 = 'd0;
	     endcase
     end

     assign aluA = (A_Sel) ? pc : rs1;
     assign aluB = (B_Sel) ? imm : rs2; 

     // ALU(aluA, aluB, alu_out); 
     ALU alu_inst (
	     .ALU_A(aluA),
	     .ALU_B(aluB), 
	     .ALU_SEL(ALU_SEL), 
	     .ALU_OUT(alu_out)
     );

     // Branch_Comp(rs1, rs2, BrUN);
     Branch_Comparison BC_inst (
	     .regA(rs1), 
	     .regB(rs2), 
	     .BrUN(BrUN), 
	     .BrEQ(BrEQ), 
	     .BrLT(BrLT)
     ); 

     always @(posedge clk) begin
	     if (reset) begin
		     pc_DX <= `RESET_PIPELINE_REG;
		     alu_DX <= `RESET_PIPELINE_REG;
		     inst_DX <= `RESET_PIPELINE_REG;
	     end else if (DXFlush) begin
		     pc_DX <= `NOP;
		     alu_DX <= `NOP;
		     inst_DX <= `NOP;
	     end else if (DXStall) begin
		     pc_DX <= pc_DX;
		     alu_DX <= alu_DX;
		     inst_DX <= inst_DX;
	     end else begin 
	     	     pc_DX <= pc;
	     	     alu_DX <= alu_out;
	     	     inst_DX <= inst;
	     end
     end

//     assign csr_write = (opcode == 7'b1110011);
//
//     always @(*) begin
//	     if (csr_write) begin
//		     case (funct3) 
//			     3'b001 : csr_write_data = rs1;
//			     3'b101 : csr_write_data = inst[19:15];
//			     default : csr_write_data = 'b0;
//		     endcase
//	     end
//    end
     localparam UART_TX_ADDR = 32'h8000_0008;
     localparam UART_RX_ADDR = 32'h8000_0004;
     localparam UART_CONTROL_ADDR = 32'h8000_0000;
     localparam UART_CLK_COUNT_ADDR = 32'h8000_0010;
     localparam UART_INS_COUNT_ADDR = 32'h8000_0014;
     localparam UART_RESET_ADDR = 32'h8000_0018;
     localparam BCC_ADDR = 32'h8000_001c;
     localparam BCCS_ADDR = 32'h8000_0020;

     assign addr_DMEM = alu_out[13:0];
     assign data_DMEM = rs2;
     assign UART_Tx_ON = (alu_out == UART_TX_ADDR);
     assign UART_Rx_ON = (alu_out == UART_RX_ADDR);
     assign UART_Control_ON = (alu_out == UART_CONTROL_ADDR);
     assign UART_RESET_CLK = (alu_out == UART_RESET_ADDR);
     assign UART_CLK_COUNT = (alu_out == UART_CLK_COUNT_ADDR);
     assign UART_INS_COUNT = (alu_out == UART_INS_COUNT_ADDR);
     assign UART_BCC = (alu_out == BCC_ADDR);
     assign UART_BCCS = (alu_out == BCCS_ADDR);
     assign alu_out_dx = alu_out;

endmodule

     
