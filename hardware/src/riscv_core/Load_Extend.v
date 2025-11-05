module LDXtend(
	input [31:0] inst, 
	input [31:0] in, 
	input [31:0] alu_DX,
	output reg [31:0] out
);
	wire [2:0] funct3;
	wire [11:0] imm; 
	
	assign funct3 = inst[14:12];
	assign imm = inst[31:20];

	always @(*) begin
		case (funct3)
			3'b000 : begin
				case (alu_DX[1:0]) 
					2'b00 : out = {{24{in[7]}}, in[7:0]}; 
					2'b01 : out = {{24{in[15]}}, in[15:8]};
					2'b10 : out = {{24{in[23]}}, in[23:16]};
					2'b11 : out = {{24{in[31]}}, in[31:24]}; 
					default : out = {32{1'b0}}; 
				endcase
			end
			3'b001 : begin
				case (alu_DX[1:0])
					2'b00 : out = {{16{in[15]}}, in[15:0]};
					2'b10 : out = {{16{in[31]}}, in[31:16]};
					default : out = {32{1'b0}};
				endcase
			end
			3'b010 : begin
				case (alu_DX[1:0]) 
					2'b00 : out = in;
					default : out = {32{1'b0}};
				endcase
			end
			3'b100 : begin
				case (alu_DX[1:0]) 
					2'b00 : out = {{24{1'b0}}, in[7:0]}; 
					2'b01 : out = {{24{1'b0}}, in[15:8]};
					2'b10 : out = {{24{1'b0}}, in[23:16]};
					2'b11 : out = {{24{1'b0}}, in[31:24]}; 
					default : out = {32{1'b0}}; 
				endcase
			end
			3'b101 : begin
				case (alu_DX[1:0])
					2'b00 : out = {{16{1'b0}}, in[15:0]};
					2'b10 : out = {{16{1'b0}}, in[31:16]};
					default : out = {32{1'b0}};
				endcase
			end
			default : begin
				out = {32{1'b0}};
			end
		endcase
	end
endmodule

