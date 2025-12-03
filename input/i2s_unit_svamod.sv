////////////////////////////////////////////////////////////////////////////////////////////
//
// SystemVerilog assertion module file for control_unit
//
//    Contents:
//    1. X-Checks
//    2. Assumptions fro formal verification
//    3. Blackbox assertions
//    4. Whitebox assertions
//    5. Covergroups
//
////////////////////////////////////////////////////////////////////////////////////////////

`include "audioport.svh"

import audioport_pkg::*;
import audioport_util_pkg::*;

module i2s_unit_svamod
  (
   input logic 	      clk,
   input logic 	      rst_n,
   input logic 	      play_in,
   input logic [23:0] audio0_in,
   input logic [23:0] audio1_in,
   input logic 	      tick_in,
   input logic 	      req_out,
   input logic 	      sck_out,
   input logic 	      ws_out,
   input logic 	      sdo_out
`ifndef SYSTEMC_DUT
,
   input logic [8:0]  counter,        // 9-bit counter for timing
   input logic [47:0] input_reg,      // 48-bit input register
   input logic [47:0] shift_reg,      // 48-bit shift register
   input logic        play_r,
   input logic        load_enable,    // Enable loading of input and shift registers
   input logic        shift_enable,    // Enable shifting of shift register
input logic        sck_out_logic,
input logic        ws_out_logic,
input logic        end_s		      
`endif
   );

   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 1. X-checks
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

   `xcheck(play_in);
   `xcheck(audio0_in);
   `xcheck(audio1_in);
   `xcheck(tick_in);
   `xcheck(req_out);
   `xcheck(sck_out);
   `xcheck(ws_out);
   `xcheck(sdo_out);
`ifndef SYSTEMC_DUT
 // X-Checks for internal signals
   `xcheck(counter);
   `xcheck(play_r);
   `xcheck(input_reg);
   `xcheck(shift_reg);
   `xcheck(load_enable);
   `xcheck(shift_enable);
`xcheck(sck_out_logic);
`xcheck(ws_out_logic);
`xcheck(end_s);

`endif   
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 2. Blackbox (functional) assumptions and assertions
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

`ifdef design_top_is_i2s_unit // Assumptions enabled only in i2s_unit verification

   // play_in_length : f_play_in_stable

   property f_play_in_stable;
   @(posedge clk ) disable iff (rst_n == '0)
     !$stable(play_in) |=> $stable(play_in) [* 384];
   endproperty

   mf_play_in_stable: assume property(f_play_in_stable) else assert_error("mf_play_in_stable");
   cf_play_in_stable: cover property(f_play_in_stable);

   // tick_in_length : f_tick_in_pulse

   property f_tick_in_pulse;
      @(posedge clk ) disable iff (rst_n == '0)
	$rose(tick_in) |=> $fell(tick_in);
   endproperty

   mf_tick_in_pulse: assume property(f_tick_in_pulse) else assert_error("mf_tick_in_pulse");
   cf_tick_in_pulse: cover property(f_tick_in_pulse);

   // tick_in_length : f_tick_in_play_only

   property f_tick_in_play_only;
      @(posedge clk ) disable iff (rst_n == '0)
	!play_in |-> !tick_in;
   endproperty

   mf_tick_in_play_only: assume property(f_tick_in_play_only) else assert_error("mf_tick_in_play_only");
   cf_tick_in_play_only: cover property(f_tick_in_play_only);

`endif //  `ifdef design_top_is_i2s_unit


   
   // data_request : f_req_out_pulse

   property f_req_out_pulse;
      @(posedge clk ) disable iff (rst_n == '0)
	$rose(req_out) |=> $fell(req_out);
   endproperty

   af_req_out_pulse: assert property(f_req_out_pulse) else assert_error("af_req_out_pulse");
   cf_req_out_pulse: cover property(f_req_out_pulse);


   
   // mode_control : f_sck_start
   
   property f_sck_start;
      @(posedge clk ) disable iff (rst_n == '0)
	$rose(play_in)  |=> $rose(sck_out);
   endproperty
   
   af_sck_start: assert property(f_sck_start) else assert_error("af_sck_start");
   cf_sck_start: cover property(f_sck_start);
   
   // data_request : f_req_sck_align

   property f_req_sck_align;
      @(posedge clk ) disable iff (rst_n == '0)
	$fell(req_out) |-> $fell(sck_out);
   endproperty

   af_req_sck_align: assert property(f_req_sck_align) else assert_error("af_req_sck_align");
   cf_req_sck_align: cover property(f_req_sck_align);

   // data_request : f_req_out_seen

   property f_req_out_seen;
      @(posedge clk ) disable iff (rst_n == '0)
	($rose(play_in) || (play_in && $fell(ws_out))) ##1 (play_in throughout ($fell(sck_out) [-> 1])) |-> $past(req_out);
   endproperty

   af_req_out_seen: assert property(f_req_out_seen) else assert_error("af_req_out_seen");
   cf_req_out_seen: cover property(f_req_out_seen);

   

   // ws_wave : f_ws_change

   property f_ws_change;
      @(posedge clk ) disable iff (rst_n == '0)
	!$stable(ws_out) |-> $fell(sck_out);
   endproperty

   af_ws_change: assert property(f_ws_change) else assert_error("af_ws_change");
   cf_ws_change: cover property(f_ws_change);

   // ws_wave : f_ws_wave

   property f_ws_wave;
      @(posedge clk ) disable iff (rst_n == '0)
	!ws_out throughout $rose(sck_out) [-> 24] |=> $rose(ws_out) [-> 1] ##1 (ws_out throughout $rose(sck_out) [-> 24]) ;
   endproperty

   af_ws_wave: assert property(f_ws_wave) else assert_error("af_ws_wave");
   cf_ws_wave: cover property(f_ws_wave);

   // serial_data : f_sdo_change

   property f_sdo_change;
      @(posedge clk ) disable iff (rst_n == '0)
	!$stable(sdo_out) && play_in |-> $fell(sck_out);
   endproperty

   af_sdo_change: assert property(f_sdo_change) else assert_error("af_sdo_change");
   cf_sdo_change: cover property(f_sdo_change);

// sck_wave : f_sck_wave

   property f_sck_wave;
      @(posedge clk ) disable iff (rst_n == '0)
    $rose(sck_out) |=> (sck_out [*3] ##1 !sck_out[*4])  
   endproperty

   af_sck_wave: assert property(f_sck_wave) else assert_error("af_sck_wave");
   cf_sck_wave: cover property(f_sck_wave);

   // sck_wave : f_sck_last

   property f_sck_last;
      @(posedge clk ) disable iff (rst_n == '0)
    $fell(ws_out) |=> !sck_out [*3] ##1 sck_out[*4] ##1 !sck_out;
   endproperty

   af_sck_last: assert property(f_sck_last) else assert_error("af_sck_last");
   cf_sck_last: cover property(f_sck_last);


   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 3. Whitebox (RTL) assertions
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

 `ifndef SYSTEMC_DUT

 // Shift register Behavior
property f_shift_reg_behavior;
    @(posedge clk) disable iff (rst_n == '0)
      (shift_enable) |=> (shift_reg == { $past(shift_reg,1) << 1 });
endproperty
af_shift_reg_behavior: assert property(f_shift_reg_behavior) else assert_error("af_shift_reg_behavior");
 cf_shift_reg_behavior: cover property(f_shift_reg_behavior);

// Shift register Reset
  property f_shift_reg_reset;
    @(posedge clk ) disable iff (rst_n == '0)
    (!play_r) |=> ##1 (shift_reg == 48'b0);
  endproperty

  af_shift_reg_reset: assert property (f_shift_reg_reset) else assert_error("af_shift_reg_reset");
  cf_shift_reg_reset: cover property(f_shift_reg_reset);

// Play Mode Control
property f_play_r_control;
    @(posedge clk) disable iff (!rst_n)
    play_in |=> play_r;
  endproperty
  af_play_r_control: assert property(f_play_r_control) else assert_error("af_play_r_control");
  cf_play_r_control: cover property(f_play_r_control);

//Counter Reset at 383
property f_counter_reset_at_383;
  @(posedge clk) disable iff (!rst_n)
  (counter == 383) |=> (counter == 0);
endproperty

af_counter_reset_at_383: assert property(f_counter_reset_at_383) else assert_error("af_counter_reset_at_383");
cf_counter_reset_at_383: cover property(f_counter_reset_at_383);

//Word Select mid frame behavior
property f_ws_out_mid_behavior;
  @(posedge clk) disable iff (!rst_n)
  ((counter > 187) && (counter < 380)) |-> (ws_out_logic == 1);
endproperty

af_ws_out_mid_behavior: assert property(f_ws_out_mid_behavior) else assert_error("af_ws_out_mid_behavior");
cf_ws_out_mid_behavior: cover property(f_ws_out_mid_behavior);




 `endif

   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 4. Covergroups
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////




endmodule

