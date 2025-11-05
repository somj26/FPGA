`include "opcode.vh"

module control(
	input clk,
	input [31:0] inst_DX, 
	input [31:0] inst_MW,
	input BrLT, BrEQ,  
	output reg PCSel, A_Sel, B_Sel, 
	output reg [1:0] A_fwd_sel, B_fwd_sel, WBSel,
	output reg IFFlush, IFStall, DXStall, DXFlush,
	output reg dmem_en, dmem_write,
	output reg RegWEn, 
	output BrUN, 
	output reg [2:0] imm_type
);
	reg [6:0] opcode_DX = 7'b0; 
	reg [6:0] opcode_MW = 7'b0; 
	reg [4:0] inst_DX_rs1, inst_DX_rs2, inst_MW_rd;
	reg DXFlush_F;

	localparam I_TYPE = 3'd0;
	localparam S_TYPE= 3'd1; 
	localparam B_TYPE = 3'd2;
	localparam U_TYPE = 3'd3;
	localparam J_TYPE = 3'd4;

	assign BrUN = inst_DX[13];
	reg [2:0] funct3_EX, funct3_MW;

	always @(*) begin
		PCSel = 1'b0;
		A_Sel = 1'b0; 
		B_Sel = 1'b0;
		WBSel = 2'b00;
		A_fwd_sel = 2'b00;
		B_fwd_sel = 2'b00;
		imm_type = 3'b000;
		dmem_en = 1'b0;
		dmem_write = 1'b0;
		RegWEn = 1'b0;
		IFFlush = 1'b0;
		IFStall = 1'b0;
		DXFlush = 1'b0;
		DXStall = 1'b0;

		opcode_DX = inst_DX[6:0];
		opcode_MW = inst_MW[6:0];

		inst_DX_rs1 = inst_DX[19:15];
		inst_DX_rs2 = inst_DX[24:20];
		inst_MW_rd = inst_MW[11:7]; 
		funct3_EX = inst_DX[14:12];
		funct3_MW = inst_MW[14:12];

		case (opcode_DX) 
			`OPC_ARI_RTYPE : begin
				A_Sel = 1'b0;
				B_Sel = 1'b0;
				imm_type = 3'b000;
				if ((inst_DX_rs1 == inst_MW_rd) && (inst_DX_rs1 != 0) && (inst_MW[6:0] != (`OPC_STORE)) && (inst_MW[6:0] != (`OPC_BRANCH))) begin 
					A_fwd_sel = 2'b10;
				end
				if ((inst_DX_rs2 == inst_MW_rd) && (inst_DX_rs2 != 0) && (inst_MW[6:0] != (`OPC_STORE)) && (inst_MW[6:0] != (`OPC_BRANCH))) begin
					B_fwd_sel = 2'b10;
				end
			end
			`OPC_ARI_ITYPE : begin
				A_Sel = 1'b0;
				B_Sel = 1'b1;
				imm_type = I_TYPE; 
				if ((inst_DX_rs1 == inst_MW_rd) && (inst_DX_rs1 != 0) && (inst_MW[6:0] != ((`OPC_STORE))) && (inst_MW[6:0] != (`OPC_BRANCH))) begin
					A_fwd_sel = 2'b10;
				end
			end
			`OPC_LOAD : begin
				A_Sel = 1'b0;
				B_Sel = 1'b1;
				imm_type = I_TYPE; 
				if ((inst_DX_rs1 == inst_MW_rd) && (inst_DX_rs1 != 0) && (inst_MW[6:0] != ((`OPC_STORE))) && (inst_MW[6:0] != (`OPC_BRANCH))) begin
					A_fwd_sel = 2'b10;
				end
				dmem_en = 1'b1; 
			end
			`OPC_CSR : begin
				A_Sel = 1'b0;
				if ((inst_DX_rs1 == inst_MW_rd) && (inst_DX_rs1 != 0) && (inst_MW[6:0] != `OPC_STORE) && (inst_MW[6:0] != (`OPC_BRANCH))) begin
					A_fwd_sel = 2'b10;
				end
			end
			`OPC_STORE : begin
				A_Sel = 1'b0;
				B_Sel = 1'b1;
				imm_type = S_TYPE; 
				if ((inst_DX_rs1 == inst_MW_rd) && (inst_DX_rs1 != 0) && (inst_MW[6:0] != (`OPC_STORE)) && (inst_MW[6:0] != (`OPC_BRANCH))) begin
					A_fwd_sel = 2'b10;
				end 
				if ((inst_DX_rs2 == inst_MW_rd) && (inst_DX_rs2 != 0) && (inst_MW[6:0] != (`OPC_STORE)) && (inst_MW[6:0] != (`OPC_BRANCH))) begin
					B_fwd_sel = 2'b10;
				end
				dmem_en = 1'b1;
				dmem_write = 1'b1;
			end
			`OPC_JALR : begin
				A_Sel = 1'b0;
				B_Sel = 1'b1;
				imm_type = I_TYPE;
				if ((inst_DX_rs1 == inst_MW_rd) && (inst_DX_rs1 != 0) && (inst_MW[6:0] != (`OPC_STORE)) && (inst_MW[6:0] != (`OPC_BRANCH))) begin
					A_fwd_sel = 2'b10;
				end
			end
			`OPC_BRANCH : begin
				A_Sel = 1'b1;
				B_Sel = 1'b1;
				if ((inst_DX_rs1 == inst_MW_rd) && (inst_DX_rs1 != 0) && (inst_MW[6:0] != (`OPC_STORE)) && (inst_MW[6:0] != (`OPC_BRANCH))) begin
					A_fwd_sel = 2'b10;
				end
				if ((inst_DX_rs2 == inst_MW_rd) && (inst_DX_rs2 != 0) && (inst_MW[6:0] != (`OPC_STORE)) && (inst_MW[6:0] != (`OPC_BRANCH))) begin
					B_fwd_sel = 2'b10;
				end
				imm_type = B_TYPE;
//				case (funct3_EX) 
//					3'b000 : PCSel = BrEQ;              
//					3'b001 : PCSel = ~BrEQ;             
//					3'b100 : PCSel = BrLT;              
//					3'b101 : PCSel = ~BrLT;             
//					3'b110 : PCSel = BrLT;             
//					3'b111 : PCSel = ~BrLT;             
//					default : PCSel = 0;
//				endcase
			end
			`OPC_JAL : begin
				A_Sel = 1'b1;
				B_Sel = 1'b1;
				imm_type = J_TYPE;
			end
			`OPC_LUI : begin
				imm_type = U_TYPE;
				B_Sel = 1'b1;
			end
			`OPC_AUIPC : begin
				imm_type = U_TYPE;
				A_Sel = 1'b1;
				B_Sel = 1'b1;
			end
		endcase

		case (opcode_MW) 
			`OPC_ARI_RTYPE : begin
				PCSel = 1'b0;
				WBSel = 2'b01;
				RegWEn = 1'b1;
			end
			`OPC_ARI_ITYPE : begin
				PCSel = 1'b0;
				WBSel = 2'b01;
				RegWEn = 1'b1;
			end
			`OPC_LOAD : begin 
				PCSel = 1'b0;
				WBSel = 2'b10;
				RegWEn = 1'b1;
			end
			`OPC_STORE : begin
				PCSel = 1'b0;
				WBSel = 2'b00;
				RegWEn = 1'b0;
			end
			`OPC_JALR : begin
				PCSel = 1'b1;
				WBSel = 2'b00;
				RegWEn = 1'b1;
			end
			`OPC_BRANCH : begin
				WBSel = 2'b00;
				RegWEn = 1'b0;
				case (funct3_MW) 
					3'b000 : PCSel = BrEQ;              
					3'b001 : PCSel = ~BrEQ;             
					3'b100 : PCSel = BrLT;              
					3'b101 : PCSel = ~BrLT;             
					3'b110 : PCSel = BrLT;             
					3'b111 : PCSel = ~BrLT;             
					default : PCSel = 0;
				endcase
			end
			`OPC_JAL : begin
				PCSel = 1'b1;
				WBSel = 2'b00;
				RegWEn = 1'b1;
			end
			`OPC_LUI : begin
				PCSel = 1'b0;
				WBSel = 2'b01; 
				RegWEn = 1'b1;
			end
			`OPC_AUIPC : begin
				PCSel = 1'b0;
				WBSel = 2'b01;
				RegWEn = 1'b1;
			end
		endcase

		IFFlush = PCSel;
		DXFlush = (PCSel) ? PCSel : DXFlush_F;
		//No Stall Logic Required since no stalls are expected?
	end


	always @(posedge clk) begin
		DXFlush_F <= IFFlush;
	end
//	always @(posedge clk) begin
//		if (DXFlush) RegWEn <= 0;
//	end
//	always @(posedge clk or posedge PCSel) begin
//		if (PCSel) begin
//			IFFlush <= 1'b1;
//			DXFlush <= 1'b1;
//		end else begin
//			IFFlush <= 1'b0;
//			DXFlush <= IFFlush;
//		end
//	end

endmodule


		
