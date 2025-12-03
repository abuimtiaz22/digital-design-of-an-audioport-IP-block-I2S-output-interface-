`include "audioport.svh"

import audioport_pkg::*;

module control_unit
  (
   input logic 			       clk,
   input logic 			       rst_n,
   input logic 			       PSEL,
   input logic 			       PENABLE,
   input logic 			       PWRITE,
   input logic [31:0] 		       PADDR,
   input logic [31:0] 		       PWDATA,
   input logic 			       req_in,
   output logic [31:0] 		       PRDATA,
   output logic 		       PSLVERR,
   output logic 		       PREADY,
   output logic 		       irq_out,
   output logic [31:0] 		       cfg_reg_out,
   output logic [31:0] 		       level_reg_out,
   output logic [DSP_REGISTERS*32-1:0] dsp_regs_out,
   output logic 		       cfg_out,
   output logic 		       clr_out,
   output logic 		       level_out,
   output logic 		       tick_out,
   output logic [23:0] 		       audio0_out,
   output logic [23:0] 		       audio1_out,
   output logic 		       play_out
   );



// Signal Declarations
logic apbwrite;
logic apbread;
logic [$clog2(AUDIOPORT_REGISTERS+2)+1:2] rindex;


// apb_decoder
always_comb begin:apb_decoder

    apbwrite = PREADY && PWRITE && PSEL && PENABLE;

    apbread = !PWRITE && PSEL && PENABLE && PREADY;
end:apb_decoder

// address_decoder
always_comb begin:address_decoder
    if (PSEL)
        rindex = PADDR[$clog2(AUDIOPORT_REGISTERS+2)+1:2]; 
    else
        rindex = 0;
end:address_decoder

//play_control
logic start;
logic stop;
logic play_r;
logic req_r;
// play_r Logic
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        play_r <= 0;
    else if (start)
        play_r <= 1;  
    else if (stop)
        play_r <= 0; 
end

// req_r Logic
always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n)
        req_r <= 0;
    else if (play_r)
        req_r <= req_in;
    else
        req_r <= 0; 
end

// command_decoder
logic irqack;

always_comb begin: command_decoder
    
    
    cfg_out = apbwrite && rindex == CMD_REG_INDEX && PWDATA == CMD_CFG;

    start = apbwrite && rindex == CMD_REG_INDEX && PWDATA == CMD_START;

    stop = apbwrite && rindex == CMD_REG_INDEX && PWDATA == CMD_STOP;

    level_out = apbwrite && rindex == CMD_REG_INDEX && PWDATA == CMD_LEVEL;

    irqack = apbwrite && rindex == CMD_REG_INDEX && PWDATA == CMD_IRQACK;
end: command_decoder

// standby_command_decoder
logic clr;

always_comb begin: standby_command_decoder
    clr = !play_r && apbwrite && rindex == CMD_REG_INDEX && PWDATA == CMD_CLR;

end: standby_command_decoder

// apb_driver
logic [23:0] lfifo, rfifo;
logic [AUDIOPORT_REGISTERS-1:0] [31:0] rbank_r ;  

always_comb begin: apb_driver
PREADY = 1'b1;
PSLVERR =1'b0;
PRDATA = 32'd0;

    if (PSEL) begin
      
        if (rindex < AUDIOPORT_REGISTERS) begin
            PRDATA = rbank_r[rindex][31:0];
        end
        else if (rindex == LEFT_FIFO_INDEX) begin
            PRDATA = {8'd0,lfifo};           
        end
        else if (rindex == RIGHT_FIFO_INDEX) begin
            PRDATA = {8'd0,rfifo};
        end
    end
        
  
end: apb_driver



// tick_out_logic
always_comb begin:tick_out_logic
    if (play_r)
        tick_out = req_r; 
    else
        tick_out = 0;      
end: tick_out_logic

//register_bank (style 1)

always_ff @(posedge clk or negedge rst_n) begin:register_bank
        if (!rst_n) begin
            rbank_r <= '0;
        end else begin
            if (apbwrite && rindex < AUDIOPORT_REGISTERS)
                rbank_r[rindex][31:0] <= PWDATA;
            
            if (start)
                rbank_r[STATUS_REG_INDEX][STATUS_PLAY] <= 1'b1;
            
            if (stop)
                rbank_r[STATUS_REG_INDEX][STATUS_PLAY] <= 1'b0;
        end
    end:register_bank

//left_fifo (Style 2)

    // Register Declaration
logic [AUDIO_FIFO_SIZE-1:0] [23:0] ldata_r;  
logic [$clog2(AUDIO_FIFO_SIZE)-1:0] ltail_r;
logic [$clog2(AUDIO_FIFO_SIZE)-1:0] lhead_r; 
logic [AUDIO_FIFO_SIZE-1:0] [23:0] ldata_ns;
logic [$clog2(AUDIO_FIFO_SIZE)-1:0] lhead_ns;
logic [$clog2(AUDIO_FIFO_SIZE)-1:0]  ltail_ns;  
logic lempty;
logic llooped_r;
logic llooped_ns;
logic lfull;


    // Sequential Logic (One always_ff for all registers)
    always_ff @(posedge clk or negedge rst_n) begin:left_fifo
        if (!rst_n) begin
            ldata_r  <= '0;
            lhead_r  <= '0;
            ltail_r  <= '0;
            llooped_r <= '0;
        end 
        else begin
            ldata_r  <= ldata_ns;
            lhead_r  <= lhead_ns;
            ltail_r  <= ltail_ns;
            llooped_r <= llooped_ns;
        end
    end:left_fifo

    // Combinational Next-State Logic
    always_comb begin:left_fifo_ns
        
        ldata_ns = ldata_r;
        lhead_ns = lhead_r;
        ltail_ns = ltail_r;
        llooped_ns = llooped_r;


        // Write Operation
        if (apbwrite && rindex == LEFT_FIFO_INDEX && !lfull) begin
            ldata_ns[lhead_r]={ PWDATA[23:0]};
            if (lhead_r != AUDIO_FIFO_SIZE-1)
                lhead_ns = lhead_r + 1;
            else begin
                lhead_ns = 0;
                llooped_ns = 1;
            end
        end

        // Read Operation
        if (apbread && rindex == LEFT_FIFO_INDEX && !lempty) begin
            if (ltail_r != AUDIO_FIFO_SIZE-1)
                ltail_ns = ltail_r + 1;
            else begin
                ltail_ns = 0;
                llooped_ns = 0; 
            end
        end

        // Play Request
        if (play_r && req_r && !lempty) begin
            if (ltail_r != AUDIO_FIFO_SIZE-1)
                ltail_ns = ltail_r + 1;
            else begin
                ltail_ns = 0;
                llooped_ns = 0;
            end
        end

        // Clear FIFO
        if (clr) begin
            ldata_ns  = '0;
            lhead_ns  = '0;
            ltail_ns  = '0;
            llooped_ns = '0;
        end
    end:left_fifo_ns


// lfifo_mux

always_comb begin:lfifo_mux
 if (!lempty)
        lfifo = ldata_r[ltail_r][23:0];
    else
        lfifo = 0;
end: lfifo_mux

//lfifo_decoder


always_comb begin:lfifo_decoder
 
    if (lhead_r == ltail_r && !llooped_r)
        lempty = 1'b1;
    else
        lempty = 1'b0;

    if (lhead_r == ltail_r && llooped_r)
        lfull = 1'b1;
    else
        lfull = 1'b0;
end:lfifo_decoder


//right_fifo (Style 2)

    // Register Declaration
logic [AUDIO_FIFO_SIZE-1:0] [23:0] rdata_r; 
logic [$clog2(AUDIO_FIFO_SIZE)-1:0] rtail_r;
logic [$clog2(AUDIO_FIFO_SIZE)-1:0] rhead_r; 
logic [AUDIO_FIFO_SIZE-1:0] [23:0] rdata_ns;
logic [$clog2(AUDIO_FIFO_SIZE)-1:0] rhead_ns;
logic [$clog2(AUDIO_FIFO_SIZE)-1:0]  rtail_ns; 
logic rempty;
logic rlooped_r;
logic rlooped_ns;
logic rfull;


    // Sequential Logic (One always_ff for all registers)
    always_ff @(posedge clk or negedge rst_n) begin:right_fifo
        if (!rst_n) begin
            rdata_r  <= '0;
            rhead_r  <= '0;
            rtail_r  <= '0;
            rlooped_r <= '0;
        end 
        else begin
            rdata_r  <= rdata_ns;
            rhead_r  <= rhead_ns;
            rtail_r  <= rtail_ns;
            rlooped_r <= rlooped_ns;
        end
    end:right_fifo

    // Combinational Next-State Logic
    always_comb begin:right_fifo_ns
        
        rdata_ns = rdata_r;
        rhead_ns = rhead_r;
        rtail_ns = rtail_r;
        rlooped_ns = rlooped_r;


        // Write Operation
        if (apbwrite && rindex == RIGHT_FIFO_INDEX && !rfull) begin
            rdata_ns[rhead_r] = {PWDATA[23:0]};
            if (rhead_r != AUDIO_FIFO_SIZE-1)
                rhead_ns = rhead_r + 1;
            else begin
                rhead_ns = 0;
                rlooped_ns = 1;
            end
        end

        // Read Operation
        if (apbread && rindex == RIGHT_FIFO_INDEX && !rempty) begin
            if (rtail_r != AUDIO_FIFO_SIZE-1)
                rtail_ns = rtail_r + 1;
            else begin
                rtail_ns = 0;
                rlooped_ns = 0; 
            end
        end

        // Play Request
        if (play_r && req_r && !rempty) begin
            if (rtail_r != AUDIO_FIFO_SIZE-1)
                rtail_ns = rtail_r + 1;
            else begin
                rtail_ns = 0;
                rlooped_ns = 0;
            end
        end

        // Clear FIFO
        if (clr) begin
            rdata_ns  = '0;
            rhead_ns  = '0;
            rtail_ns  = '0;
            rlooped_ns = '0;
        end
    end:right_fifo_ns


// rfifo_mux

always_comb begin:rfifo_mux
 if (!rempty)
        rfifo = rdata_r[rtail_r][23:0];
    else
        rfifo =0;
end:rfifo_mux

//rfifo_decoder


always_comb begin:rfifo_decoder
 
    if (rhead_r == rtail_r && !rlooped_r)
        rempty = 1'b1;
    else
        rempty = 1'b0;

    if (rhead_r == rtail_r && rlooped_r)
        rfull = 1'b1;
    else
        rfull = 1'b0;
end:rfifo_decoder

//interrupt_control
logic irq_r;

always_ff @(posedge clk or negedge rst_n) begin:interrupt_control
    if (!rst_n) 
        irq_r <= 1'b0;
    else if (stop)
        irq_r <= 1'b0;
    else if (irqack)
        irq_r <= 1'b0;
    else if (!stop && !irqack && play_r && lempty && rempty)
        irq_r <= 1'b1;
    
end:interrupt_control

//register_bank_reader



        assign cfg_reg_out = rbank_r[CFG_REG_INDEX];  
        assign level_reg_out = rbank_r[LEVEL_REG_INDEX]; 
        assign dsp_regs_out = rbank_r[DSP_REGS_END_INDEX:DSP_REGS_START_INDEX];







// Assign Interconnections
assign audio0_out = lfifo;           
assign audio1_out = rfifo;         
assign irq_out = irq_r;       
assign clr_out = clr;               
assign play_out = play_r;


endmodule
