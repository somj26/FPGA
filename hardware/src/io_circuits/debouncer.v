module debouncer #(
    parameter WIDTH              = 1,
    parameter SAMPLE_CNT_MAX     = 62500,
    parameter PULSE_CNT_MAX      = 200,
    parameter WRAPPING_CNT_WIDTH = $clog2(SAMPLE_CNT_MAX),
    parameter SAT_CNT_WIDTH      = $clog2(PULSE_CNT_MAX) + 1
) (
    input clk,
    input [WIDTH-1:0] glitchy_signal,
    output [WIDTH-1:0] debounced_signal
);

    reg [WRAPPING_CNT_WIDTH-1:0] wrapping_counter = 0;
    reg [SAT_CNT_WIDTH-1:0] saturating_counter [WIDTH-1:0];
    integer i;
 
    /*initial begin
	    for (i = 0; i < WIDTH; i = i + 1) begin
		    saturating_counter[i] <= 'b0;
	    end 
    end
    */
    always @(posedge clk) begin
	    if (wrapping_counter == SAMPLE_CNT_MAX-1) begin
		    wrapping_counter <= 0; 
		    for (i = 0; i < WIDTH; i = i + 1) begin
			    if (glitchy_signal[i] == 0) begin 
				    saturating_counter[i] <= 0;
			    end else begin
				    if (saturating_counter[i] == PULSE_CNT_MAX) begin
					    saturating_counter[i] <= saturating_counter[i];
				    end else begin
					    saturating_counter[i] <= saturating_counter[i] + 1'b1;
				    end
			    end
		    end
	    end else begin
		    wrapping_counter <= wrapping_counter + 1'b1;
	    end
    end

    genvar j;
    generate
	    for (j = 0; j < WIDTH; j = j + 1) begin
		    assign debounced_signal[j] = (saturating_counter[j] == PULSE_CNT_MAX);
	    end
    endgenerate

endmodule
