//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//
// sva_bindings.svh: SVA assertion module bindings for RTL simulation and formal verification.
//
// - The macro 'design_top_is_*' is defined in the RTL simulation script based on
//
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////

// This macro is defined in project-file include file audioport.svh

`ifndef DISABLE_ASSERTIONS

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//  1.1. control_unit
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////

`ifdef design_top_is_control_unit

//       Example: Binding an assertion module to all instances of a design module
//
//     .------------------------------------------- Name of module bound to (design module)
//     |           .------------------------------- Name of module to be bound (assertion module)
//     |           |                   .----------- Instance name of module to be bound (assertion module)
//     |           |                   |
//     V           V                   V

bind control_unit control_unit_svamod CHECKER_MODULE 
  (
   .clk(clk),
   .rst_n(rst_n),
   .PSEL(PSEL),
   .PENABLE(PENABLE),
   .PWRITE(PWRITE),
   .PADDR(PADDR),
   .PWDATA(PWDATA),
   .req_in(req_in),
   .PRDATA(PRDATA),
   .PSLVERR(PSLVERR),
   .PREADY(PREADY),
   .irq_out(irq_out),
   .cfg_reg_out(cfg_reg_out),
   .level_reg_out(level_reg_out),
   .dsp_regs_out(dsp_regs_out),
   .cfg_out(cfg_out),
   .clr_out(clr_out),
   .level_out(level_out),
   .tick_out(tick_out),
   .audio0_out(audio0_out),
   .audio1_out(audio1_out),
   .play_out(play_out)
 `ifndef SYSTEMC_DUT
   ,
   .play_r(play_r),
   .rindex(rindex),
   .rbank_r(rbank_r),
   .apbwrite(apbwrite),
   .apbread(apbread),
   .clr(clr),
   .start(start),
   .stop(stop),
   .irqack(irqack),
   .req_r(req_r),
   .irq_r(irq_r),
   .ldata_r(ldata_r),
   .lhead_r(lhead_r),
   .ltail_r(ltail_r), 
   .llooped_r(llooped_r),
   .lempty(lempty),
   .lfull(lfull),
   .lfifo(lfifo),
   .rdata_r(rdata_r),
   .rhead_r(rhead_r),
   .rtail_r(rtail_r), 
   .rlooped_r(rlooped_r),
   .rempty(rempty),
   .rfull(rfull),
   .rfifo(rfifo) 
 `endif
   );

`endif


/////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//  1.2. dsp_unit
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////

`ifdef design_top_is_dsp_unit
bind dsp_unit dsp_unit_svamod CHECKER_MODULE
  (.clk(clk), 
   .rst_n(rst_n), 
   .audio0_in(audio0_in),
   .audio1_in(audio1_in), 
   .tick_in(tick_in),
   .cfg_in(cfg_in),
   .level_in(level_in),     
   .clr_in(clr_in),
   .cfg_reg_in(cfg_reg_in),
   .level_reg_in(level_reg_in),
   .tick_out(tick_out),         
   .dsp_regs_in(dsp_regs_in),
   .audio0_out(audio0_out),
   .audio1_out(audio1_out)     
   );

`endif

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//  1.3. cdc_unit
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////

`ifdef design_top_is_cdc_unit

bind cdc_unit cdc_unit_svamod CHECKER_MODULE 
  (
   .clk(clk),
   .rst_n(rst_n),
   .test_mode_in(test_mode_in),
   .audio0_in(audio0_in),
   .audio1_in(audio1_in),
   .play_in(play_in),
   .tick_in(tick_in),
   .req_out(req_out),
   .mclk(mclk),
   .muxclk_out(muxclk_out),
   .muxrst_n_out(muxrst_n_out),
   .audio0_out(audio0_out),
   .audio1_out(audio1_out), 
   .play_out(play_out),
   .tick_out(tick_out),
   .req_in(req_in)
 `ifndef SYSTEMC_DUT
   ,
   .mrst_n(mrst_n)
`endif
   );

`endif

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//  1.4. i2s_unit
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////

`ifdef design_top_is_i2s_unit

`ifndef SYNOPSYS_VCS
bind i2s_unit i2s_unit_svamod  CHECKER_MODULE 
  (.clk(clk),
   .rst_n(rst_n),
   .play_in(play_in),
   .tick_in(tick_in),
   .audio0_in(audio0_in),
   .audio1_in(audio1_in),
   .req_out(req_out),
   .ws_out(ws_out),
   .sck_out(sck_out),
   .sdo_out(sdo_out)
`ifndef SYSTEMC_DUT
,
   .*
`endif
       );
`else
bind i2s_unit i2s_unit_svamod  CHECKER_MODULE 
  (
   .clk(CLK),
   .rst_n(RST_N),
   .play_in(PLAY_IN),
   .tick_in(TICK_IN),
   .audio0_in(AUDIO0_IN),
   .audio1_in(AUDIO1_IN), 
   .req_out(REQ_OUT),
   .ws_out(WS_OUT),
   .sck_out(SCK_OUT),
   .sdo_out(SDO_OUT)
   );
`endif
`endif

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//  1.5. audioport
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////

`ifdef design_top_is_audioport

bind audioport audioport_svamod CHECKER_MODULE
  (.clk(clk),
   .rst_n(rst_n),
   .mclk(mclk),
   .PSEL(PSEL),
   .PENABLE(PENABLE),
   .PWRITE(PWRITE),
   .PADDR(PADDR),	      
   .PWDATA(PWDATA),
   .PRDATA(PRDATA),
   .PREADY(PREADY),
   .PSLVERR(PSLVERR),
   .irq_out(irq_out),   
   .sck_out(sck_out),   
   .ws_out(ws_out),
   .sdo_out(sdo_out),
   .test_mode_in(test_mode_in),
   .scan_en_in(scan_en_in)
 `ifndef SYSTEMC_DUT
,      
   .tick(tick),
   .play(play),
   .cfg(cfg),
   .level(level),
   .clr(clr),
   .audio0(audio0),
   .audio1(audio1),
   .cfg_reg(cfg_reg),
   .level_reg(level_reg),
   .dsp_regs(dsp_regs),
   .daudio0(daudio0),
   .daudio1(daudio1),
   .dtick(dtick),
   .muxclk(muxclk),      
   .muxrst_n(muxrst_n),
   .mtick(mtick),
   .mplay(mplay),
   .mreq(mreq),
   .maudio0(maudio0),
   .maudio1(maudio1), 
   .req(req)
`endif
   );


`ifndef SYSTEMC_DUT

bind control_unit control_unit_svamod CHECKER_MODULE
  (
   .clk(clk),
   .rst_n(rst_n),
   .PSEL(PSEL),
   .PENABLE(PENABLE),
   .PWRITE(PWRITE),
   .PADDR(PADDR),
   .PWDATA(PWDATA),
   .req_in(req_in),
   .PRDATA(PRDATA),
   .PSLVERR(PSLVERR),
   .PREADY(PREADY),
   .irq_out(irq_out),
   .cfg_reg_out(cfg_reg_out),
   .level_reg_out(level_reg_out),
   .dsp_regs_out(dsp_regs_out),
   .cfg_out(cfg_out),
   .clr_out(clr_out),
   .level_out(level_out),
   .tick_out(tick_out),
   .audio0_out(audio0_out),
   .audio1_out(audio1_out),
   .play_out(play_out),
   .play_r(play_r),
   .rindex(rindex),
   .rbank_r(rbank_r),
   .apbwrite(apbwrite),
   .apbread(apbread),
   .clr(clr),
   .start(start),
   .stop(stop),
   .irqack(irqack),
   .req_r(req_r),
   .irq_r(irq_r),
   .ldata_r(ldata_r),
   .lhead_r(lhead_r),
   .ltail_r(ltail_r), 
   .llooped_r(llooped_r),
   .lempty(lempty),
   .lfull(lfull),
   .lfifo(lfifo),
   .rdata_r(rdata_r),
   .rhead_r(rhead_r),
   .rtail_r(rtail_r), 
   .rlooped_r(rlooped_r),
   .rempty(rempty),
   .rfull(rfull),
   .rfifo(rfifo) 
   );


bind dsp_unit dsp_unit_svamod CHECKER_MODULE
  (.clk(clk), 
   .rst_n(rst_n), 
   .audio0_in(audio0_in),
   .audio1_in(audio1_in), 
   .tick_in(tick_in),
   .cfg_in(cfg_in),
   .level_in(level_in),     
   .clr_in(clr_in),
   .cfg_reg_in(cfg_reg_in),
   .level_reg_in(level_reg_in),
   .tick_out(tick_out),         
   .dsp_regs_in(dsp_regs_in),
   .audio0_out(audio0_out),
   .audio1_out(audio1_out)     
   );

bind cdc_unit cdc_unit_svamod CHECKER_MODULE 
  (
   .clk(clk),
   .rst_n(rst_n),
   .test_mode_in(test_mode_in),
   .audio0_in(audio0_in),
   .audio1_in(audio1_in),
   .play_in(play_in),
   .tick_in(tick_in),
   .req_out(req_out),
   .mclk(mclk),
   .muxclk_out(muxclk_out),
   .muxrst_n_out(muxrst_n_out),
   .audio0_out(audio0_out),
   .audio1_out(audio1_out), 
   .play_out(play_out),
   .tick_out(tick_out),
   .req_in(req_in)
 `ifndef SYSTEMC_DUT
   ,
   .mrst_n(mrst_n)
`endif
   );

 `ifndef SYNOPSYS_VCS

bind i2s_unit i2s_unit_svamod  CHECKER_MODULE 
  (.clk(clk),
   .rst_n(rst_n),
   .play_in(play_in),
   .tick_in(tick_in),
   .audio0_in(audio0_in),
   .audio1_in(audio1_in),
   .req_out(req_out),
   .ws_out(ws_out),
   .sck_out(sck_out),
   .sdo_out(sdo_out),
   .*
   );

`else
bind i2s_unit i2s_unit_svamod  CHECKER_MODULE 
  (
   .clk(CLK),
   .rst_n(RST_N),
   .play_in(PLAY_IN),
   .tick_in(TICK_IN),
   .audio0_in(AUDIO0_IN),
   .audio1_in(AUDIO1_IN), 
   .req_out(REQ_OUT),
   .ws_out(WS_OUT),
   .sck_out(SCK_OUT),
   .sdo_out(SDO_OUT)
   );

`endif


`endif //  `ifndef SYSTEMC_DUT

`endif //  `ifdef design_top_is_audioport

`endif //  `ifdef INCLUDE_ASSERTIONS






