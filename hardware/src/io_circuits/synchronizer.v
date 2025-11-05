module synchronizer #(parameter WIDTH = 1) (
    input [WIDTH-1:0] async_signal,
    input clk,
    output [WIDTH-1:0] sync_signal
);
	reg [WIDTH-1:0] q_temp_1 = 0;
	reg [WIDTH-1:0] q_temp_2 = 0;

	always @(posedge clk) begin
		q_temp_1 <= async_signal;
	        q_temp_2 <= q_temp_1;
	end

	assign sync_signal = q_temp_2;
endmodule
