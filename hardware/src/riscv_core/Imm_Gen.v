module Immediate_Generator(
     input [31:0] inst,
     input [2:0] imm_type,
     output reg [31:0] immediate
); 
     localparam IMM_I = 3'd0;
     localparam IMM_S = 3'd1; 
     localparam IMM_B = 3'd2;
     localparam IMM_U = 3'd3;
     localparam IMM_J = 3'd4;

     always @(*) begin
	     case (imm_type) 
		     IMM_I : begin
			     immediate = {{20{inst[31]}}, inst[31:20]};
		     end 
		     IMM_S : begin
			     immediate = {{20{inst[31]}}, inst[31:25], inst[11:7]};
		     end 
		     IMM_B : begin
			     immediate = {{19{inst[31]}}, inst[31], inst[7], inst[30:25], inst[11:8], 1'b0};
		     end 
		     IMM_U : begin
			     immediate = {inst[31:12], 12'b0};
		     end
		     IMM_J : begin
			     immediate = {{11{inst[31]}}, inst[31], inst[19:12], inst[20], inst[30:21], 1'b0};
		     end
		     default : immediate = 32'b0; 
	     endcase
     end

endmodule




