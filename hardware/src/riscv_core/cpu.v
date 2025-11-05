//`include "Fetch.v"
//`include "Decode_Execute.v"
//`include "Memory_Write.v"
//`include "reg_file.v"
//`include "Branch_Comp.v"
//`include "ALU.v"
//`include "control.v"
//`include "Imm_Gen.v"
//`include "Store_Extend.v" //Check name

module cpu #(
    parameter CPU_CLOCK_FREQ = 50_000_000,
    parameter RESET_PC = 32'h4000_0000,
    parameter BAUD_RATE = 115200
) (
    input clk,
    input rst,
    input bp_enable,
    input serial_in,
    output serial_out
);
    // BIOS Memory
    // Synchronous read: read takes one cycle
    // Synchronous write: write takes one cycle


    wire [11:0] bios_addra, bios_addrb;
    wire [31:0] bios_douta, bios_doutb;
    wire bios_ena, bios_enb;
    assign bios_ena = 1'b1;
    assign bios_enb = 1'b1;

    wire PCSel,  A_Sel, B_Sel;
    wire [1:0] A_fwd_sel, B_fwd_sel, WBSel;
    wire IFFlush, IFStall, DXStall, DXFlush; 
    wire BrUN, BrLT, BrEQ; 
    reg BrUN_MW, BrLT_MW, BrEQ_MW;
    wire [2:0] imm_type;

    // Pipeline Registers for inst, PC and ALU 
    reg [31:0] inst_DX, inst_MW; // Inst in DX and MW phase respectively
    reg [31:0] PC_F, PC_DX; // PC value in DX and MW phase respectively (after F and DX phases respectively)
    reg [31:0] alu_DX;  // ALU value in the MW phase (after the DX phase)
    reg PCSel_reg; 

    // wb signal and immediate signal 
    wire [31:0] wb;
    wire [31:0] imm;

    // Singals to interface with the memory (IMEM and DMEM)
    wire [31:0] PC_IMEM; 
    wire [31:0] imem_dina, dmem_din, dmem_dout;
    wire [13:0] imem_addra, imem_addrb, dmem_addr1, dmem_addr;
    wire [3:0] imem_wea;
    wire [3:0] dmem_we;
    wire imem_ena, dmem_en, dmem_we_en;
    wire [31:0] stx_in, stx_out;
    wire [31:0] alu_out_dx;
    // Register File Interfacing Signals
    wire we;
    wire [4:0] ra1, ra2, wa;
    wire [31:0] wd;
    wire [31:0] rd1, rd2;

    wire csr_write;
    reg [31:0] csr_data; 
    wire [31:0] imem_dmem_dout, dmem_dmem_dout, bios_dmem_dout;

    assign ra1 = inst_DX[19:15];
    assign ra2 = inst_DX[24:20]; 
    assign wa = inst_MW[11:7];
    assign wd = wb;

    always @(posedge clk) begin
	    if (rst | DXStall) begin
//		    PCSel_reg <= 1'b0;
//		    BrUN_MW <= 1'b0;
		    BrEQ_MW <= 1'b0;
		    BrLT_MW <= 1'b0;
	    end else begin
//		    PCSel_reg <= PCSel;
//		    BrUN_MW <= BrUN;
		    BrLT_MW <= BrLT;
		    BrEQ_MW <= BrEQ;
	    end
  end

    //Pipeline the control signals such as flush to the next stage to resolve
    //hazards. 
    control control_inst (
    	    .clk(clk),
	    .inst_DX(inst_DX), 
	    .inst_MW(inst_MW), 
	    .BrLT(BrLT_MW), 
	    .BrEQ(BrEQ_MW),
	    .PCSel(PCSel), 
	    .A_Sel(A_Sel), 
	    .B_Sel(B_Sel), 
	    .A_fwd_sel(A_fwd_sel),
	    .B_fwd_sel(B_fwd_sel), 
	    .WBSel(WBSel), 
	    .IFFlush(IFFlush), 
	    .IFStall(IFStall), 
	    .DXStall(DXStall), 
	    .DXFlush(DXFlush), 
	    .dmem_en(dmem_en), 
	    .dmem_write(dmem_we_en),
	    .RegWEn(we),  
	    .BrUN(BrUN), 
	    .imm_type(imm_type)
    );

    wire [31:0] imem_doutb;
    wire [3:0] imem_dmem_we;
    assign imem_dmem_we = dmem_we;
    assign imem_wea = PC_F[30];

    // Fetch (F) Stage Initialization
    Fetch #(
	    .RESET_PC(RESET_PC)
    ) fetch (
      .clk(clk),
      .reset(rst),
      .alu_in(alu_DX), 
      .PCSel(PCSel), 
      .IFFlush(IFFlush), 
      .IFStall(IFStall), 
      .IFID_PC(PC_F), 
      .PC(PC_IMEM)  
    );

    assign bios_addra = PC_IMEM[13:2];
    assign bios_addrb = alu_out_dx[13:2];

    bios_mem bios_mem (
      .clk(clk),
      .ena(bios_ena),
      .addra(bios_addra),
      .douta(bios_douta),
      .enb(bios_enb),
      .addrb(bios_addrb),
      .doutb(bios_dmem_dout)
    );

    //wire [31:0] alu_out_dx;

    // Instruction Memory Initialization
    assign imem_addra = alu_out_dx[15:2];
    assign imem_addrb = PC_IMEM[15:2];

    imem imem (
      .clk(clk),
      .ena(imem_ena && !IFFlush),
      .wea(imem_dmem_we),
      .addra(imem_addra),
      .dina(dmem_din),
      .addrb(imem_addrb),
      .doutb(imem_doutb)
    );

    always @(*) begin
	    inst_DX = (PC_F[30]) ? bios_douta : imem_doutb; 
    end
    
    wire UART_TX_ON, UART_RX_ON, UART_CONTROL, UART_RESET_CLK, UART_CLK_COUNT, UART_INS_COUNT, UART_BCC, UART_BCCS;
    //wire [31:0] alu_out_dx;
    // Decode and Execute (DX) Initialization
    Decode_Execute DecodeExecute (
	    .clk(clk), 
	    .reset(rst), 
	    .inst(inst_DX), 
	    .wb_forward(wb), 
	    .alu_forward(alu_DX), 
	    .pc(PC_F),
	    .BrUN(BrUN),
	    .A_fwd_sel(A_fwd_sel), 
	    .B_fwd_sel(B_fwd_sel), 
	    .A_Sel(A_Sel), 
	    .B_Sel(B_Sel), 
	    .DXFlush(DXFlush),
	    .DXStall(DXStall),
	    .dataA(rd1),
	    .dataB(rd2), 
	    .imm(imm), 
	    .pc_DX(PC_DX), 
	    .alu_DX(alu_DX), 
	    .inst_DX(inst_MW),
	    .BrEQ(BrEQ), 
	    .BrLT(BrLT),
	    .UART_Tx_ON(UART_TX_ON),
	    .UART_Rx_ON(UART_RX_ON),
	    .UART_Control_ON(UART_CONTROL),
	    .UART_RESET_CLK(UART_RESET_CLK),
	    .UART_CLK_COUNT(UART_CLK_COUNT), 
	    .UART_INS_COUNT(UART_INS_COUNT), 
	    .UART_BCC(UART_BCC), 
	    .UART_BCCS(UART_BCCS),
//	    .csr_write(csr_write), 
//	    .csr_write_data(csr_data),
	    .alu_out_dx(alu_out_dx),
	    .addr_DMEM(dmem_addr), 
	    .data_DMEM(stx_in)
    );

    Immediate_Generator IG_inst (
	    .inst(inst_DX),
	    .imm_type(imm_type),
	    .immediate(imm)
    );

    reg_file rf (
        .clk(clk),
        .we(we),
        .ra1(ra1), .ra2(ra2), 
	.wa(wa), .wd(wd),
        .rd1(rd1), .rd2(rd2)
    );

    MemWB MW_inst (
	    .clk(clk), 
	    .reset(rst),
	    .data_DMEM(dmem_dout), 
	    .pc(PC_DX),  
	    .alu(alu_DX), 
	    .inst(inst_MW), 
	    .WBSel(WBSel), 
	    .wb(wb)
    );

    
    SXtend stx_inst(
	    .inst(inst_DX), 
	    .in(stx_in), 
	    .alu_in(dmem_addr),
	    .mem_wr(dmem_we_en), 
	    .wr_en(dmem_we),
	    .UART_TX_ON(UART_TX_ON),
	    .UART_RESET_CLK(UART_RESET_CLK),
	    .out1(stx_out)
    );

    //assign dmem_din = (UART_TX_ON) ? {24'b0, uart_tx_data_in} : stx_out; 
    //assign dmem_dout = imem_dmem_dout; 
    assign csr_write = (inst_MW[6:0] == 7'b1110011);
    always @(*) begin
	    if (csr_write) begin 
		    case(inst_MW[14:12]) 
			    3'b001 : csr_data = alu_DX;
			    3'b101 : csr_data = inst_MW[19:15];
			    default : csr_data = 'b0;
		    endcase 
	    end
    end

   dmem dmem (
	    .clk(clk), 
	    .en(dmem_en && !DXFlush), 
	    .we(dmem_we), 
	    .addr(alu_out_dx[15:2]), 
	    .din(dmem_din), 
	    .dout(dmem_dmem_dout)
   );

//    wire [31:0] imem_dmem_dout, dmem_dmem_dout, bios_dmem_dout;
//    bios_mem dmem(
//	    .clk(clk), 
//	    .ena(bios_ena), 
//	    .addra(),
//	    .douta(), 
//	    .enb(bios_enb), 
//	    .addrb(dmem_addr >> 2), 
//	    .doutb(bios_dmem_dout)
// );

    //assign dmem_dout = (alu_DX[31] == 1) ? uart_data : ((alu_DX[30] == 1) ? bios_dmem_dout : dmem_dmem_dout);
    //Floating Point Unit Intiialization (CHECKPOINT3)
    wire fp_we;
    wire [4:0] fp_ra1, fp_ra2, fp_ra3, fp_wa;
    wire [31:0] fp_wd;
    wire [31:0] fp_rd1, fp_rd2, fp_rd3;
    fp_reg_file fprf (
        .clk(clk),
        .we(fp_we),
        .ra1(fp_ra1), .ra2(fp_ra2), .ra3(fp_ra3), .wa(fp_wa),
        .wd(fp_wd),
        .rd1(fp_rd1), .rd2(fp_rd2), .rd3(fp_rd3)
    );

    // On-chip UART
    //// UART Receiver
    wire [7:0] uart_rx_data_out;
    wire uart_rx_data_out_valid;
    wire uart_rx_data_out_ready;
    //// UART Transmitter
    wire [7:0] uart_tx_data_in;
    wire uart_tx_data_in_valid;
    wire uart_tx_data_in_ready;

//    reg [31:0] clk_count, ins_count, bcc_count, bccs_count;
    reg dmem_we_en_delayed, dmem_en_delayed, UARTCP, UART_CLK_D, UART_INS_D;
    always @(posedge clk) begin
	    dmem_we_en_delayed <= dmem_we_en;
	    dmem_en_delayed <= dmem_en;
	    UARTCP <= UART_CONTROL;
//	    UART_RD <= UART_RESET_CLK;
	    UART_CLK_D <= UART_CLK_COUNT;
	    UART_INS_D <= UART_INS_COUNT;
    end

    //reg [31:0] uart_map = 32'h8000_0008;
    //reg [29:0] uart_shift_map = uart_map >> 2;
    localparam UART_TX_ADDR = 32'h8000_0008;
    localparam UART_RX_ADDR = 32'h8000_0004;

//    wire uart_rx_data_out_ready_t;
//    reg uart_rx_data_out_ready_t1;
    assign uart_tx_data_in_valid = ((dmem_we_en) && UART_TX_ON);
    assign uart_rx_data_out_ready = ((dmem_en_delayed) && (alu_DX == UART_RX_ADDR));
    assign dmem_din = stx_out;
//    always @(*) begin
//	    if (UART_CLK_D) clk_count = dmem_dout;
//	    if (UART_INS_D) ins_count = dmem_dout;
//    end
//    always @(posedge clk) begin
//	    uart_rx_data_out_ready_t1 <= uart_rx_data_out_ready_t;
//    end 
//    assign uart_rx_data_out_ready = uart_rx_data_out_ready_t1;
    assign uart_tx_data_in = dmem_din[7:0];
//    assign dmem_din = (UART_TX_ON) ? {24'b0, uart_tx_data_in} : stx_out;

    uart #(
        .CLOCK_FREQ(CPU_CLOCK_FREQ),
        .BAUD_RATE(BAUD_RATE)
    ) on_chip_uart (
        .clk(clk),
        .reset(rst),

        .serial_in(serial_in),
        .data_out(uart_rx_data_out),
        .data_out_valid(uart_rx_data_out_valid),
        .data_out_ready(uart_rx_data_out_ready),

        .serial_out(serial_out),
        .data_in(uart_tx_data_in),
        .data_in_valid(uart_tx_data_in_valid),
        .data_in_ready(uart_tx_data_in_ready)
    );

    reg [31:0] clk_counter = 0;
    reg [31:0] ins_counter = 0; 

    always @(posedge clk) begin
	    clk_counter <= (rst) ? 32'b0 : clk_counter + 1'b1;
	    ins_counter <= (rst) ? 32'b0 : (DXFlush) ? ins_counter : ins_counter + 1'b1;
    end

    localparam UART_CONTR_ADDR = 32'h8000_0000;
    localparam UART_CLK_ADDR = 32'h8000_0010;
    localparam UART_INS_ADDR = 32'h8000_0014;
    localparam UART_BCC_A = 32'h8000_001c;
    localparam UART_BCCS_A = 32'h8000_0020; 
    
    reg [31:0] uart_data;
    always @(*) begin
	    if (alu_DX == UART_CONTR_ADDR) uart_data = {30'b0, uart_rx_data_out_valid, uart_tx_data_in_ready};
	    else if (alu_DX == UART_CLK_ADDR) uart_data = clk_counter;
	    else if (alu_DX == UART_INS_ADDR) uart_data = ins_counter;
//	    else if (UART_CLK_COUNT || UART_INS_COUNT) uart_data = {24'b0, uart_rx_data_out};
	    else if (uart_rx_data_out_ready) uart_data = {24'b0, uart_rx_data_out};
	    else uart_data = 32'b0;
    end
    //assign dmem_dout = dmem_dmem_dout;
    assign dmem_dout = (alu_DX[31] == 1) ? uart_data : ((alu_DX[30] == 1) ? bios_dmem_dout : dmem_dmem_dout);

    reg [31:0] tohost_csr = 0;

    always @(posedge clk) begin
	    if (csr_write) tohost_csr <= csr_data;
    end
    
//    property p_reset_assert;
//        @(posedge clk)
//            rst |=> (PC_IMEM == RESET_PC);
//    endproperty

//    assert property (p_reset_assert)
//        else $error("PC is not RESET_PC when doing reset.");
	
//    property p_ra1_rd1_zero;
//        @(posedge clk) disable iff (rst)
//           (ra1 == 0) |-> (rd1 == 0);
//    endproperty
    
//    assert property (p_ra1_rd1_zero)
//        else $error("ra1=0 but rd1 != 0");
    
//    property p_ra2_rd2_zero;
//        @(posedge clk) disable iff (rst)
//           (ra2 == 0) |-> (rd2 == 0);
//    endproperty

//    assert property (p_ra2_rd2_zero)
//        else $error("ra2=0 but rd2 != 0");	
 		   
    wire [2:0] sum_dmem_we;
    wire [2:0] store_func3;
    assign sum_dmem_we = dmem_we[3] + dmem_we[2] + dmem_we[1] + dmem_we[0];
      
//    property p_check_store_byte;
//        @(posedge clk) disable iff (rst)
//            (inst_DX[6:0] == `OPC_STORE && dmem_we_en && inst_DX[14:12] == `FNC_SB) |-> (sum_dmem_we == 1);
//    endproperty

//    assert property (p_check_store_byte)
//        else $error("Instruction is SB but the number of ones in write enable mask is not 1");

  //  property p_check_store_halfword;
//	@(posedge clk) disable iff (rst)
//            (inst_DX[6:0] == `OPC_STORE && dmem_we_en && inst_DX[14:12] == `FNC_SH) |-> (sum_dmem_we == 2);
//    endproperty

//    assert property (p_check_store_halfword)
//        else $error("Instruction is SH but the number of ones in write enable mask is not 2");

  //  property p_check_store_word;
  //      @(posedge clk) disable iff (rst)
  //          (inst_DX[6:0] == `OPC_STORE && dmem_we_en && inst_DX[14:12] == `FNC_SW) |-> (sum_dmem_we == 4);
  //  endproperty

   // assert property (p_check_store_word)
  //      else $error("Instruction is SW but the number of ones in write enable mask is not 4");

  //  property p_check_load_byte;
  //      @(posedge clk) disable iff (rst)
  //          (inst_MW[6:0] == `OPC_LOAD && inst_MW[14:12] == `FNC_LB) |-> ((wb[31:8] == {24{1'b1}}) || (wb[31:8] == {24{1'b0}}));
 //   endproperty

 //   assert property (p_check_load_byte)
 //       else $error("Instruction is LB but upper 24 bits are not all 1s nor all 0s");
   
 //   property p_check_load_halfword;
 //       @(posedge clk) disable iff (rst)
  //          (inst_MW[6:0] == `OPC_LOAD && inst_MW[14:12] == `FNC_LH) |-> ((wb[31:16] == {16{1'b1}}) || (wb[31:16] == {16{1'b0}}));
 //   endproperty

 //   assert property (p_check_load_halfword)
 //       else $error("Instruction is LH but upper 16 bits are not all 1s nor all 0s");

	
    // TODO: Your code to implement a fully functioning RISC-V core
    // Add as many modules as you want
    // Feel free to move the memory modules around
endmodule
