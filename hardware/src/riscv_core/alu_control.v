module ALU_Control(
	input [31:0] inst, 
	output reg [3:0] alu_ctrl
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

	wire [6:0] funct7;
	wire [2:0] funct3;
	wire [6:0] opcode; 

	assign funct7 = inst[31:25];
	assign funct3 = inst[14:12];
	assign opcode = inst[6:0];

	always @(*) begin
	alu_ctrl = DEFAULT;
  	      case (opcode)
        	  7'b0110011, 7'b0010011 : begin 
     						case (funct3)
							3'b000 : begin 
                       						 if (opcode == 7'b0110011) begin 
                           						 if (funct7[5] == 1'b1) alu_ctrl = SUB; 
									 else alu_ctrl = ADD; 
								 end else begin
								 alu_ctrl = ADD; 
                        				         end
							end
							3'b001 : alu_ctrl = SLL;  
							3'b010 : alu_ctrl = SLT;  
							3'b011 : alu_ctrl = SLTU; 
							3'b100 : alu_ctrl = XOR;  
							3'b101 : begin 
                        					if (funct7[5] == 1'b1) alu_ctrl= SRA;  
                        					else alu_ctrl = SRL;  
							end
							3'b110 : alu_ctrl = OR;   
							3'b111 : alu_ctrl = AND;  
							default : alu_ctrl = DEFAULT;
						endcase
					    end

            	   7'b0000011, 7'b0100011 : alu_ctrl = ADD; 
		   7'b0110111 : alu_ctrl = PASS;
		   7'b1100011 : alu_ctrl = ADD;
            	   7'b1100111 : alu_ctrl = ADD; 
            	   7'b1101111 : alu_ctrl = ADD;
		   7'b0010111 : alu_ctrl = ADD; 
		   7'b1110011 : alu_ctrl = CSR_PASS;

         //   	   default: alu_ctrl = DEFAULT;
 
            endcase

       end

endmodule




