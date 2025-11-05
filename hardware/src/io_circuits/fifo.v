module fifo #(
    parameter WIDTH = 8,
    parameter DEPTH = 32,
    parameter POINTER_WIDTH = $clog2(DEPTH)
) (
    input clk, rst,

    // Write side
    input wr_en,
    input [WIDTH-1:0] din,
    output full,

    // Read side
    input rd_en,
    output [WIDTH-1:0] dout,
    output empty
);
    reg [POINTER_WIDTH-1:0] wptr = 0;
    reg [POINTER_WIDTH-1:0] rptr = 0;
    reg [WIDTH-1:0] d_out;
    reg [WIDTH-1:0] FIFO[DEPTH-1:0];
    reg [POINTER_WIDTH:0] counter = 0;

    always @(posedge clk) begin
        if (rst) begin
            wptr <= 0;
            rptr <= 0;
            counter <= 0;
        end else begin
            if (wr_en && !full) begin
                FIFO[wptr] <= din;
                wptr <= wptr + 1'b1;
            end
            
            if (rd_en && !empty) begin
                d_out <= FIFO[rptr];
                rptr <= rptr + 1'b1; 
            end
            
            if (wr_en && !full && (!rd_en || empty)) begin
                counter <= counter + 1;
            end else if (rd_en && !empty && !wr_en) begin
                counter <= counter - 1;
            end
        end
    end

    assign full = (counter == DEPTH);
    assign empty = (counter == 0);
    assign dout = d_out;

//    property wr_full;
//         @(posedge clk) disable iff (!rst) (full && wr_en) |-> $stable(wptr); 
//    endproperty
//    assert_write_when_full: assert property(wr_full);

//    property rd_empty;
//         @(posedge clk) disable iff (!rst) (empty && rd_en) |-> $stable(rptr);
//    endproperty
//    assert_read_when_empty: assert property(rd_empty);

//    property check_reset;
//         @(posedge clk) (rst) |=> (wptr == 0) && (rptr == 0) && (!full);
//    endproperty
//    assert_reset_check: assert property(check_reset);

endmodule
