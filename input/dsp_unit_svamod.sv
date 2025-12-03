////////////////////////////////////////////////////////////////////////////////////////////
//
// SystemVerilog assertion module file for dsp_unit
//
//    Contents:
//    1. X-Checks
//    2. Blackbox (functional) assumptions and assertions
//    3. Whitebox assertions
//    4. Covergroups
//
////////////////////////////////////////////////////////////////////////////////////////////

`include "audioport.svh"

import audioport_pkg::*;
import audioport_util_pkg::*;

module dsp_unit_svamod(
		       input logic 			  clk,
		       input logic 			  rst_n,
		       input logic 			  tick_in,
		       input logic 			  cfg_in,
		       input logic 			  level_in,
		       input logic 			  clr_in, 
		       input logic [23:0] 		  audio0_in,
		       input logic [23:0] 		  audio1_in, 
		       input logic [DSP_REGISTERS*32-1:0] dsp_regs_in,
		       input logic [31:0] 		  level_reg_in,
		       input logic [31:0] 		  cfg_reg_in,
		       input logic [23:0] 		  audio0_out,
		       input logic [23:0] 		  audio1_out,
		       input logic 			  tick_out		
		       );


   // ---------------------------------------------------------------------------      
   // Check for unknown 'x states (see xcheck macro definitions in audioport.svh)
   // ---------------------------------------------------------------------------      
   
   `xcheck(tick_in);
   `xcheck(cfg_in);
   `xcheck(level_in);
   `xcheck(clr_in);
   `xcheck(audio0_in);
   `xcheck(audio1_in);   
   `xcheck(dsp_regs_in);
   `xcheck(level_reg_in);
   `xcheck(cfg_reg_in);      
   `xcheck(audio0_out);
   `xcheck(audio1_out);
   `xcheck(tick_out);         

   //////////////////////////////////////////////////////////////////////////////
   //
   // 1. Assumptions for formal verification
   //
   //////////////////////////////////////////////////////////////////////////////

 `ifdef design_top_is_dsp_unit

   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 2. Blackbox (functional) assumptions and assertions
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


   // clr_in : f_tick_clr_mutex

   property f_tick_clr_mutex;
    @(posedge clk ) disable iff (rst_n == '0)
      !(tick_in && clr_in);
 endproperty

   mf_tick_clr_mutex: assume property(f_tick_clr_mutex) else assert_error("mf_tick_clr_mutex");


   // tick_in : f_tick_in_pulse

   property f_tick_in_pulse;
      @(posedge clk ) disable iff (rst_n == '0)
	$rose(tick_in) |=> $fell(tick_in) ##1 !tick_in [* DSP_UNIT_MAX_LATENCY];
   endproperty

   mf_tick_in_pulse: assume property(f_tick_in_pulse) else assert_error("mf_tick_in_pulse");


   // cfg_in : f_cfg_in_pulse

   property f_cfg_in_pulse;
      @(posedge clk ) disable iff (rst_n == '0)
	$rose(cfg_in) |=> $fell(cfg_in);
   endproperty

   mf_cfg_in_pulse: assume property(f_cfg_in_pulse) else assert_error("mf_cfg_in_pulse");


   // clr_in : f_clr_in_pulse

   property f_clr_in_pulse;
      @(posedge clk ) disable iff (rst_n == '0)
	$rose(clr_in) |=> $fell(clr_in);
   endproperty

   mf_clr_in_pulse: assume property(f_clr_in_pulse) else assert_error("mf_clr_in_pulse");


   // level_in : f_level_in_pulse

   property f_level_in_pulse;
      @(posedge clk ) disable iff (rst_n == '0)
	$rose(level_in) |=> $fell(level_in);
   endproperty

   mf_level_in_pulse: assume property(f_level_in_pulse) else assert_error("mf_level_in_pulse");
   
 `endif


   // tick_out : f_tick_out_pulse

   property f_tick_out_pulse;
      @(posedge clk ) disable iff (rst_n == '0)
	$rose(tick_out) |=> $fell(tick_out);
   endproperty

   af_tick_out_pulse: assert property(f_tick_out_pulse) else assert_error("af_tick_out_pulse");
   cf_tick_out_pulse: cover property(f_tick_out_pulse);

   // max_latency : f_max_latency

   property f_max_latency;
      @(posedge clk ) disable iff (rst_n == '0)
	$rose(tick_in)  |=> !tick_out [* 0:DSP_UNIT_MAX_LATENCY] ##1 tick_out;
   endproperty

   af_max_latency: assert property(f_max_latency) else assert_error("af_max_latency");
   cf_max_latency: cover property(f_max_latency);

   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 3. Whitebox (RTL) assertions
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 4. Covergroups
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   
`ifndef SYSTEMC_DUT
   
   // ---------------------------------------------------------------------------      
   // cg_dsp_modes
   // ---------------------------------------------------------------------------      
   
   covergroup cg_dsp_modes with function sample(logic cfgbit);
      coverpoint cfgbit
	{ 
	 bins modes[] = { 1'b0, 1'b1 }; 
      }
   endgroup
   cg_dsp_modes cg_dsp_modes_inst = new;   

   property f_dsp_config;
      logic 					  cfgbit;
      @(posedge clk) disable iff (rst_n == '0)
	($rose(cfg_in), cfgbit = cfg_reg_in[CFG_FILTER]) ##1 (!cfg_in throughout tick_in [-> 1]) ##1 tick_out [-> 1] 
	|-> (1, cg_dsp_modes_inst.sample(cfgbit));
   endproperty

   cf_dsp_config: cover property (f_dsp_config);

`endif
   
endmodule


