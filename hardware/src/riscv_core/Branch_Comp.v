`define INST_LEN 'd32

module Branch_Comparison (
      input [`INST_LEN-1:0] regA,
      input [`INST_LEN-1:0] regB,
      input BrUN,
      output BrEQ,
      output BrLT
);
      assign BrEQ = (regA == regB);
      assign BrLT = (BrUN) ? ($unsigned(regA) < $unsigned(regB)) : ($signed(regA) < $signed(regB));
endmodule
