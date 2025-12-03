////////////////////////////////////////////////////////////////////////////////////////////
//
// SystemVerilog assertion module file for cdc_unit
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

module cdc_unit_svamod
  (
   input logic 	      clk,
   input logic 	      rst_n,
   input logic 	      test_mode_in,
   input logic [23:0] audio0_in,
   input logic [23:0] audio1_in,
   input logic 	      play_in,
   input logic 	      tick_in,
   input logic 	      req_out,
		
   input logic 	      mclk,
   input logic 	      muxclk_out, 
   input logic 	      muxrst_n_out,
   input logic [23:0] audio0_out,
   input logic [23:0] audio1_out, 
   input logic 	      play_out,
   input logic 	      tick_out,
   input logic 	      req_in
`ifndef SYSTEMC_DUT
,
   input logic 	      mrst_n   
`endif
   );

   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 1. X-checks
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

   `xcheck(test_mode_in);
   `xcheck(audio0_in);
   `xcheck(audio1_in);
   `xcheck(tick_in);
   `xcheck(play_in);
   `xcheck(req_in);
   `xcheck(audio0_out);
   `xcheck(audio1_out);
   `xcheck(tick_out);
   `xcheck(play_out);
   `xcheck(req_out);

   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 2. Blackbox (functional) assumptions and assertions
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

   //  : f_tick_pulse

   property f_tick_pulse;
      @(posedge clk ) disable iff (rst_n == '0)
	$rose(tick_in) |=> !tick_in;
   endproperty

   mf_tick_pulse: assume property(f_tick_pulse) else assert_error("mf_tick_pulse");


   //  : f_tick_interval

   property f_tick_interval;
      @(posedge clk ) disable iff (rst_n == '0)
	$rose(tick_in) |=> $fell(tick_in) ##1 !tick_in [* CDC_DATASYNC_INTERVAL-2];
   endproperty

   mf_tick_interval: assume property(f_tick_interval) else assert_error("mf_tick_interval");


   //  : f_play_length

   property f_play_length;
      @(posedge clk ) disable iff (rst_n == '0)
	!$stable(play_in) |=>  $stable(play_in) [* CDC_BITSYNC_INTERVAL-1];
   endproperty

   mf_play_length: assume property(f_play_length) else assert_error("mf_play_length");

   //  : f_req_pulse

   property f_req_pulse;
      @(posedge muxclk_out ) disable iff (muxrst_n_out == '0)
	$rose(req_in) |=> !req_in;
   endproperty

   mf_req_pulse: assume property(f_req_pulse) else assert_error("mf_req_pulse");



   
   // reset_sync : f_reset_sync_01
   
   property f_reset_sync_01;
//      @(posedge clk) (!test_mode_in && $rose(rst_n))|-> @(posedge muxclk_out) !muxrst_n_out [* 1:2] ##1 muxrst_n_out;
      @(posedge muxclk_out) (!test_mode_in && $rose(rst_n)) |-> !muxrst_n_out[*1:2] ##1 muxrst_n_out;      
   endproperty

   af_reset_sync_01: assert property(f_reset_sync_01) else assert_error("af_reset_sync_01");
   cf_reset_sync_01: cover property(f_reset_sync_01);

   // reset_sync : f_reset_sync_10

   property f_reset_sync_10;
//      @(posedge clk) (!test_mode_in && $fell(rst_n)) |-> @(posedge muxclk_out) !muxrst_n_out;
      @(posedge clk) (!test_mode_in && $fell(rst_n)) |-> !muxrst_n_out;      
   endproperty

   af_reset_sync_10: assert property(f_reset_sync_10) else assert_error("af_reset_sync_10");
   cf_reset_sync_10: cover property(f_reset_sync_10);

   // play_sync : f_play_sync

   property f_play_sync;
      logic    txdata;      
      disable iff (rst_n == '0 || muxrst_n_out == '0)       
	@(posedge clk) (1, txdata = play_in) |=> @(posedge muxclk_out) 1 [* 0:CDC_BITSYNC_LATENCY] ##1 (txdata == play_out);
   endproperty

   af_play_sync: assert property(f_play_sync) else assert_error("af_play_sync");
   cf_play_sync: cover property(f_play_sync);

   // req_sync : f_req_sync

   property f_req_sync;
      @(posedge clk ) disable iff (rst_n == '0)
	$rose(req_in) |=> !req_out [* 1:CDC_PULSESYNC_LATENCY-1] ##1 req_out;
   endproperty

   af_req_sync: assert property(f_req_sync) else assert_error("af_req_sync");
   cf_req_sync: cover property(f_req_sync);


   // req_sync : f_req_out_pulse

   property f_req_out_pulse;
      @(posedge clk) disable iff (rst_n == '0)
        $rose(req_out) |=> !req_out        ;
   endproperty

   af_req_out_pulse: assert property(f_req_out_pulse) else assert_error("af_req_out_pulse");
   cf_req_out_pulse: cover property(f_req_out_pulse);


   // audio_sync : f_audio_sync

   property f_audio_sync;
      logic [1:0][23:0] txdata;
      disable iff (rst_n == '0 || muxrst_n_out == '0)
	@(posedge clk) ($rose(tick_in), txdata = {audio0_in, audio1_in}) |=> @(posedge muxclk_out) (!tick_out [* 0:CDC_DATASYNC_LATENCY]) ##1  tick_out && (txdata == {audio0_out, audio1_out}) ##1 !tick_out;
   endproperty

   af_audio_sync: assert property(f_audio_sync) else assert_error("af_audio_sync");
   cf_audio_sync: cover property(f_audio_sync);



   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 3. Whitebox (RTL) assertions
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 4. Covergroups
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////



endmodule




