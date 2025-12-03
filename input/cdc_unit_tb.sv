`ifndef SYNTHESIS

`include "audioport.svh"

import audioport_pkg::*;
import audioport_util_pkg::*;

module cdc_unit_tb   #(parameter DUT_VS_REF_SIMULATION = 0);
   
   logic clk = '0;
   logic rst_n;
   logic test_mode_in;
   logic [23:0] audio0_in;
   logic [23:0] audio1_in;   
   logic 	play_in;
   logic 	tick_in;
   logic 	req_out;
   
   logic 	mclk ='0;
   logic 	muxclk_out;
   logic 	muxrst_n_out;
   logic [23:0] audio0_out;
   logic [23:0] audio1_out;   
   logic 	play_out;
   logic 	tick_out;
   logic 	req_in;
   
   logic 	     ref_muxclk_out;
   logic 	     ref_muxrst_n_out;
   logic [23:0]      ref_audio0_out;
   logic [23:0]      ref_audio1_out;
   logic 	     ref_play_out;
   logic 	     ref_tick_out;
   logic 	     ref_req_out;
   
   ////////////////////////////////////////////////////////////////////////////
   //
   // Clock, reset generation
   //
   ////////////////////////////////////////////////////////////////////////////
   
   initial
     begin
	realtime delay;
	int counter;
	counter = 0;
	clk = '0;
	forever
	  begin 
	     #(CLK_PERIOD/2) clk = ~clk;
	     ++counter;
	     if (counter == 101)
	       begin
		  // Insert random delay to make clk and mclk start out of synch		  
		  delay = real'($urandom_range(0, CLK_PERIOD/2))/23.0;
		  #(delay);
		  counter = 0;
	       end
	  end
     end
   
   initial
     begin
	realtime delay;
	mclk = '0;
	// Insert random delay to make clk and mclk start out of synch
	delay = real'($urandom_range(0, MCLK_PERIOD/2))/11.0;
	#(delay);
	forever begin
	   #(MCLK_PERIOD/2) mclk = ~mclk;
	end
     end
   
   ////////////////////////////////////////////////////////////////////////////
   //
   // Instantiation of DUT and test program
   //
   ////////////////////////////////////////////////////////////////////////////

   cdc_unit DUT_INSTANCE (
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
			  );
   
   cdc_unit_test TEST (.*);

   ////////////////////////////////////////////////////////////////////////////
   //
   // Include SVA assertion module bindings only in RTL simulation
   //
   ////////////////////////////////////////////////////////////////////////////

`include "sva_bindings.svh"

   ////////////////////////////////////////////////////////////////////////////
   //
   // Reference model instantiation
   //
   ////////////////////////////////////////////////////////////////////////////
   
   generate
      if (DUT_VS_REF_SIMULATION) begin : REF_MODEL

	    cdc_unit REF_INSTANCE
	      (.clk(clk),
	       .rst_n(rst_n),
	       .test_mode_in(test_mode_in),
	       .mclk(mclk),
	       .muxclk_out(ref_muxclk_out),
	       .muxrst_n_out(ref_muxrst_n_out),
	       .audio0_out(ref_audio0_out),
	       .audio1_out(ref_audio1_out),	       
	       .play_out(ref_play_out),
	       .tick_out(ref_tick_out),
	       .req_out(ref_req_out),
	       .*
	       );

      end 

      
   endgenerate
   
   initial
     begin
	save_test_parameters("reports/3_vsim_cdc_unit_test_parameters.txt");	
     end
   
endmodule // cdc_unit_tb


`endif
