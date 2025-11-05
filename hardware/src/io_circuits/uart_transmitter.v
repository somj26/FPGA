// Somil Jethra
module uart_transmitter #(
    parameter CLOCK_FREQ = 125_000_000,
    parameter BAUD_RATE = 115_200)
(
    input clk,
    input reset,

    input [7:0] data_in,
    input data_in_valid,
    output data_in_ready,

    output serial_out
);
    // See diagram in the lab guide
    localparam  SYMBOL_EDGE_TIME    =   CLOCK_FREQ / BAUD_RATE;
    localparam  CLOCK_COUNTER_WIDTH =   $clog2(SYMBOL_EDGE_TIME);
    localparam  FRAME_BITS       = 10; 

    reg [FRAME_BITS-1:0] shift_reg;
    reg [$clog2(FRAME_BITS):0] bit_count;
    reg [CLOCK_COUNTER_WIDTH-1:0] clk_count;
    reg transmitting;

    // Defaults
    assign data_in_ready = !transmitting;
    assign serial_out    = transmitting ? shift_reg[0] : 1'b1;

    always @(posedge clk) begin
        if (reset) begin
            transmitting <= 1'b0;
            shift_reg    <= 1'b1;
            bit_count    <= 1'b0;
            clk_count    <= 1'b0;
        end else begin
            if (!transmitting) begin
                if (data_in_valid) begin
                    shift_reg    <= {1'b1, data_in, 1'b0};
                    transmitting <= 1'b1;
                    bit_count    <= 1'b0;
                    clk_count    <= 1'b0;
                end
            end else begin
                if (clk_count == SYMBOL_EDGE_TIME-1) begin
                    clk_count <= 1'b0;
                    shift_reg <= {1'b1, shift_reg[FRAME_BITS-1:1]}; 
                    bit_count <= bit_count + 1;

                    if (bit_count == FRAME_BITS-1) begin
                        transmitting <= 1'b0; 
                    end
                end else begin
                    clk_count <= clk_count + 1;
                end
            end
        end
    end
    /*
    property p_idle_ready_high;
        @(posedge clk) disable iff (reset)
            (!transmitting) |-> (data_in_ready && serial_out);
    endproperty
    assert property (p_idle_ready_high)
        else $error("Idle violated: ready/serial_out not high");

    localparam int FRAME_CYCLES = SYMBOL_EDGE_TIME * FRAME_BITS;

    property p_ready_low_duration;
        @(posedge clk) disable iff (reset)
            (data_in_valid && data_in_ready) |-> ##1
            (!data_in_ready[*FRAME_CYCLES]) ##1 data_in_ready;
    endproperty
    assert property (p_ready_low_duration)
        else $error("data_in_ready did not stay low for one frame length");
    */ 
endmodule
