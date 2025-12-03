////////////////////////////////////////////////////////////////////////////////////////////
//
// SystemVerilog assertion module file for audioport
//
//    Contents:
//    1. X-Checks
//    2. Blackbox (functional) assumptions and assertions
//    3. Whitebox assertions
//    4. Covergroups
//
////////////////////////////////////////////////////////////////////////////////////////////

`include "audioport.svh"

`ifndef SYNTHESIS

import audioport_pkg::*;
import audioport_util_pkg::*;

module audioport_svamod
  
  (input logic clk,
   input logic 			      rst_n,
   input logic 			      mclk,
   input logic 			      PSEL,
   input logic 			      PENABLE,
   input logic 			      PWRITE,
   input logic [31:0] 		      PADDR,
   input logic [31:0] 		      PWDATA,
   input logic [31:0] 		      PRDATA,
   input logic 			      PREADY,
   input logic 			      PSLVERR,
   input logic 			      irq_out,
   input logic 			      ws_out,
   input logic 			      sck_out, 
   input logic 			      sdo_out,
   input logic 			      test_mode_in,
   input logic 			      scan_en_in
 `ifndef SYSTEMC_DUT
,
   input logic 			      tick,
   input logic 			      play,
   input logic 			      cfg,
   input logic 			      level,
   input logic 			      clr,
   input logic [23:0] 		      audio0,
   input logic [23:0] 		      audio1,
   input logic [31:0] 		      cfg_reg,
   input logic [31:0] 		      level_reg,
   input logic [DSP_REGISTERS*32-1:0] dsp_regs,

   // dsp_unit

   input logic [23:0] 		      daudio0,
   input logic [23:0] 		      daudio1,
   input logic 			      dtick,

   // cdc_unit   

   input logic 			      muxclk,      
   input logic 			      muxrst_n,
   input logic 			      mtick,
   input logic 			      mplay,
   input logic 			      mreq,
   input logic [23:0] 		      maudio0,
   input logic [23:0] 		      maudio1, 
   
   // i2s_unit   

   input logic 			      req
`endif
   );

   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 1. X-checks
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   
   `xcheck(PSEL);
   `xcheck(PENABLE);
   `xcheck(PWRITE);
   `xcheck(PADDR);
   `xcheck(PWDATA);
   `xcheck(PRDATA);
   `xcheck(PREADY);
   `xcheck(PSLVERR);
   `xcheck(irq_out);
   `xcheck(test_mode_in);   
   `xcheck(scan_en_in);   
`ifndef SYSTEMC_DUT
   `xcheckm(sck_out); // xcheckm use mrst_n, which is an internal signal
   `xcheckm(ws_out);
   `xcheckm(sdo_out);   
   `xcheck(tick);
   `xcheck(play);
   `xcheck(req);
   `xcheck(cfg);
   `xcheck(level);
   `xcheck(clr);
   `xcheck(audio0);
   `xcheck(audio1);   
   `xcheck(daudio0);
   `xcheck(daudio1);
   `xcheck(dtick);
   `xcheck(cfg_reg);
   `xcheck(level_reg);
   `xcheck(dsp_regs);
   `xcheckm(mtick);
   `xcheckm(mplay);
   `xcheckm(mreq);
   `xcheckm(maudio0);
   `xcheckm(maudio1);
 `endif //  `ifndef SYSTEMC_DUT
   
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 2. Blackbox (functional) assumptions and assertions
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   
 `include "apb_assumes.svh"

   property f_start_stop_interval;
      @(posedge clk) disable iff (rst_n == '0)
	(PSEL && PWRITE && PENABLE && PREADY && (PADDR == CMD_REG_ADDRESS) && (PWDATA == CMD_START)) |->
	  !(PSEL && PWRITE && PENABLE && PREADY && (PADDR == CMD_REG_ADDRESS) && (PWDATA == CMD_STOP)) [* CLK_DIV_48000];
    endproperty

   mf_start_stop_interval: assume property(f_start_stop_interval);   

   property f_clear_rule;
      @(posedge clk) disable iff (rst_n == '0)
	(PSEL && PWRITE && PENABLE && PREADY && (PADDR == CMD_REG_ADDRESS) && (PWDATA == CMD_START)) |=>
	   !(PSEL && PWRITE && PENABLE && PREADY && (PADDR == CMD_REG_ADDRESS) && (PWDATA == CMD_CLR)) until
	   (PSEL && PWRITE && PENABLE && PREADY && (PADDR == CMD_REG_ADDRESS) && (PWDATA == CMD_STOP));
   endproperty
      
   mf_clear_rule: assume property(f_clear_rule);
      
   property f_irq_out_rise;
      @(posedge clk) disable iff (rst_n == '0)
        (!(PSEL && PWRITE && PENABLE && PREADY && (PADDR == CMD_REG_ADDRESS) && (PWDATA == CMD_STOP)) throughout ($rose(ws_out) ##1 ($rose(ws_out) [-> AUDIO_FIFO_SIZE]))) 
	implies 
	(($rose(ws_out) ##1 ($rose(ws_out) [-> AUDIO_FIFO_SIZE]) ) intersect ($rose(irq_out) [= 1]));
   endproperty
      
   af_irq_out_rise: assert property(f_irq_out_rise);
   cf_irq_out_rise: cover property(f_irq_out_rise);   

   property f_enter_play_mode;
      @(posedge clk) disable iff (rst_n == '0)
        PSEL && PWRITE && PENABLE && PREADY && (PADDR == CMD_REG_ADDRESS) && (PWDATA == CMD_START) |=>
					 1 [* 0:CLK_DIV_48000] ##1 sck_out;
   endproperty
      
   af_enter_play_mode: assert property(f_enter_play_mode);
   cf_enter_play_mode: cover property(f_enter_play_mode);   

   property f_enter_standby_mode;
      @(posedge clk) disable iff (rst_n == '0)
        PSEL && PWRITE && PENABLE && PREADY && (PADDR == CMD_REG_ADDRESS) && (PWDATA == CMD_STOP) |=>
					 1 [* 0:CLK_DIV_48000] ##1 !sck_out;
   endproperty
      
   af_enter_standby_mode: assert property(f_enter_standby_mode);
   cf_enter_standby_mode: cover property(f_enter_standby_mode);   



   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 3. Whitebox (RTL) assertions
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

 `ifndef SYSTEMC_DUT   
   property r_data_roundtrip;
      @(posedge mclk) disable iff (muxrst_n == '0)
	(play throughout ($fell(ws_out) ##1 $fell(ws_out) [-> 1]))
	implies
        ($fell(ws_out) ##1 $fell(ws_out) [-> 1]) intersect ($rose(mreq) [= 1] ##1 $rose(mtick) [= 1]);
   endproperty

   ar_data_roundtrip: assert property ( r_data_roundtrip )
     else $error("roundtripfailure.");
   cr_data_roundtrip: cover property ( r_data_roundtrip );
 `endif

   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 4. Covergroups
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   
`ifndef SYSTEMC_DUT
   
   covergroup cg_active_config with function sample(logic cfgbit);
      configs: coverpoint cfgbit
	{ 
         bins cfgmodes[]= { 1'b0, 1'b1 };
      }
   endgroup

   cg_active_config cg_active_config_inst = new;

   property f_active_config;
      @(posedge clk ) disable iff (rst_n == '0)
	cfg ##1 (!cfg throughout $rose(play) [-> 1]) |-> (1, cg_active_config_inst.sample(cfg_reg[0]));
   endproperty      
   
   cf_active_config: cover property(f_active_config);

`endif //  `ifndef SYSTEMC_DUT

endmodule

`endif
