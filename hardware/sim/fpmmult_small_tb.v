`timescale 1ns/1ns
`include "mem_path.vh"

// This testbench consolidates all the software tests that relies on the CSR check.
// A software test is compiled to a hex file, then loaded to the testbench for simulation.
// All the software tests have the same CSR check: if the expected result matches
// the generated result, 1 is written to the CSR which indicates a passing status.

module fpmmult_small_tb();
  reg clk, rst;
  parameter CPU_CLOCK_PERIOD = 20;
  parameter CPU_CLOCK_FREQ   = 1_000_000_000 / CPU_CLOCK_PERIOD;

  localparam TIMEOUT_CYCLE = 1_000_000;
  localparam BAUD_RATE       = 10_000_000;
  localparam BAUD_PERIOD     = 1_000_000_000 / BAUD_RATE; // 8680.55 ns

  initial clk = 0;
  always #(CPU_CLOCK_PERIOD/2) clk = ~clk;

  reg bp_enable = 1'b0;
  wire serial_out;

  cpu # (
    .CPU_CLOCK_FREQ(CPU_CLOCK_FREQ),
    .RESET_PC(32'h1000_0000),
    .BAUD_RATE(BAUD_RATE)
  ) cpu (
    .clk(clk),
    .rst(rst),
    .bp_enable(bp_enable),
    .serial_in(1'b1), // input
    .serial_out(serial_out)     // output
  );

  reg [31:0] cycle;
  always @(posedge clk) begin
    if (rst === 1)
      cycle <= 0;
    else
      cycle <= cycle + 1;
  end

  reg [9:0] char_out;
  integer j;

  reg [7:0] msg_out [156:0];
  integer char_i = 0;

  integer i;

  // Host off-chip UART <-- FPGA on-chip UART (transmitter)
  // The host (testbench) expects to receive a character from the CPU via the serial line
  task fpga_to_host;
    begin
      // Wait until serial_out is LOW (start of transaction)
      wait (serial_out === 1'b0);

      for (j = 0; j < 10; j = j + 1) begin
        // sample output half-way through the baud period to avoid tricky edge cases
        #(BAUD_PERIOD / 2);
        char_out[j] = serial_out;
        #(BAUD_PERIOD / 2);
      end

      msg_out[char_i][7:0] = char_out[8:1];
      char_i = char_i + 1;
    end
  endtask

  reg [255:0] MIF_FILE;
  string output_string;
  initial begin

    $readmemh("../../software/fpmmult_small/fpmmult.hex", `IMEM_PATH.mem, 0, 16384-1);
    $readmemh("../../software/fpmmult_small/fpmmult.hex", `DMEM_PATH.mem, 0, 16384-1);

    `ifndef IVERILOG
      $vcdpluson;
    `endif
    `ifdef IVERILOG
      $dumpfile("fpmmult_small.fst");
      $dumpvars(0, c_tests_tb);
    `endif

    rst = 1;

    // Hold reset for a while
    repeat (10) @(posedge clk);

    @(negedge clk);
    rst = 0;

    // Delay for some time
    repeat (1000) @(posedge clk);

    repeat (156) fpga_to_host();

    $display("[TEST] This test multiplies a 4x4 identity matrix (A) by a 4x4 matrix (B) where B[i, j] = j. The result is stored in S");
    $display("[TEST] Expecting result of 41c00000");
    $display("[TEST] BIOS output...\n");

    output_string = "";
    for (i = 0; i < 156; i = i + 1) begin
      output_string = {output_string, $sformatf("%s", msg_out[i][7:0])};
    end
    $display("%s", output_string);

    $display("\n[TEST] Memory dump:\n");

    for (i = 0; i < 4; i = i + 1) begin
      for (j = 0; j < 4; j = j + 1) begin
        $display("A: %d, %d: %x", i, j, `DMEM_PATH.mem[2160/4 + i * 4 + j]);
      end
    end
    $display("");
    for (i = 0; i < 4; i = i + 1) begin
      for (j = 0; j < 4; j = j + 1) begin
        $display("B: %d, %d: %x", i, j, `DMEM_PATH.mem[2288/4 + i * 4 + j]);
      end
    end
    $display("");
    for (i = 0; i < 4; i = i + 1) begin
      for (j = 0; j < 4; j = j + 1) begin
        $display("S: %d, %d: %x", i, j, `DMEM_PATH.mem[2224/4 + i * 4 + j]);
      end
    end
    $finish();
  end

  initial begin
    repeat (TIMEOUT_CYCLE) @(posedge clk);
    $display("Timeout!");
    $finish();
  end

endmodule
