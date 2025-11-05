module edge_detector #(
    parameter WIDTH = 1
)(
    input clk,
    input [WIDTH-1:0] signal_in,
    output [WIDTH-1:0] edge_detect_pulse
);
    reg [WIDTH-1:0] signal_state;
    reg [WIDTH-1:0] posedge_detect;
    always @(posedge clk) begin
	    signal_state <= signal_in;
	    posedge_detect <= (~signal_state) & signal_in;
    end
    assign edge_detect_pulse = posedge_detect;
endmodule
