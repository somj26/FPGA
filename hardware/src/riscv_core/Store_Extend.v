module SXtend (
	input [31:0] inst, 
	input [31:0] in,
	input [31:0] alu_in,
	input mem_wr,
	output reg [3:0] wr_en,
	input UART_TX_ON,
	input UART_RESET_CLK, 
	output reg [31:0] out1
);
	wire [2:0] funct3;
	wire [11:0] imm;
	reg [31:0] out;
	assign funct3 = inst[14:12];
	assign imm = {inst[31:25], inst[11:7]};

	always @(*) begin
		wr_en = 4'b0000;
		out = 31'b0;
		if (mem_wr) begin
			case (funct3)
				3'b000 : begin
					case (alu_in[1:0]) 
						2'b00 : begin
							out = in;
							wr_en = 4'b0001;
						end
						2'b01 : begin
							out = in << 8;
							wr_en = 4'b0010;
						end 
						2'b10 : begin
							out = in << 16;
							wr_en = 4'b0100;
						end
						2'b11 : begin 
							out = in << 24;
							wr_en = 4'b1000;
						end 
						default : begin
							out = {32{1'b0}};
							wr_en = 4'b0;
						end
					endcase
				end
				3'b001 : begin
					case (alu_in[1:0])
						2'b00 : begin
							out = in;
							wr_en = 4'b0011;
						end
						2'b10 : begin
							out = in << 16;
							wr_en = 4'b1100;
						end
						default : begin 
							out = {32{1'b0}};
							wr_en = 4'b0;
						end
					endcase
				end
				3'b010 : begin
					case (alu_in[1:0])
						2'b00 : begin
							out = in;
							wr_en = 4'b1111;
						end 
						default : begin
							out = {32{1'b0}};
							wr_en = 4'b0;
						end 
					endcase
				end
				default : begin
					out = {32{1'b0}};
					wr_en = 4'b0;
				end
			endcase
		end
		out1 = (UART_RESET_CLK) ? {31'b0, 1'b1} : ((UART_TX_ON) ? {24'b0, out[7:0]} : out);
	end
endmodule





	

