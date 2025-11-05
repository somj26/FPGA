//`include "Load_Extend.v"

module MemWB (
      input clk, 
      input reset,
      input [31:0] data_DMEM,
      input [31:0] pc,
      input [31:0] alu, 
      input [31:0] inst, 
      input [1:0] WBSel, 
      output reg [31:0] wb
);
      wire [31:0] data_X_DMEM;
      LDXtend ldx_inst(
	      .inst(inst), 
	      .in(data_DMEM), 
	      .alu_DX(alu),
	      .out(data_X_DMEM)
      );

      wire [31:0] pc_4;
      assign pc_4 = pc + 'd4;

      always @(*) begin
          case (WBSel)
	     	 2'b00 : wb = pc_4;
	    	 2'b01 : wb = alu;
	     	 2'b10 : wb = data_X_DMEM;
	    	 default : wb = 'd0;
	  endcase
      end

endmodule

