`ifndef SYNTHESIS

`include "audioport.svh"

import audioport_pkg::*;
import audioport_util_pkg::*;

module i2s_unit_tb;
   logic 	   clk;
   logic 	   rst_n;
   logic 	   play_in;
   logic 	   tick_in;   
   logic [23:0]    audio0_in;
   logic [23:0]    audio1_in;   
   logic 	   req_out;
   logic  ws_out;
   logic  sck_out;
   logic  sdo_out;

   i2s_if i2s(rst_n);
   assign i2s.sdo = sdo_out;
   assign i2s.sck = sck_out;
   assign i2s.ws  = ws_out;
   
   ////////////////////////////////////////////////////////////////////////////
   //
   // Clock, reset generation
   //
   ////////////////////////////////////////////////////////////////////////////
   
   initial
     begin
	clk = '0;
	forever #(MCLK_PERIOD/2) clk = ~clk;
     end
   
   initial
     begin
	rst_n = '0;
	@(negedge clk) rst_n = '0;
	@(negedge clk) rst_n = '1;	
     end

   ////////////////////////////////////////////////////////////////////////////
   //
   // Instantiation of DUT and test program
   //
   ////////////////////////////////////////////////////////////////////////////
   
   i2s_unit DUT_INSTANCE (
			  .clk(clk),
			  .rst_n(rst_n),
			  .play_in(play_in),
			  .tick_in(tick_in),
			  .audio0_in(audio0_in),
			  .audio1_in(audio1_in),
			  .req_out(req_out),
			  .ws_out(ws_out),
			  .sck_out(sck_out),
			  .sdo_out(sdo_out)
			  );

   i2s_unit_test TEST    (
			  .clk(clk),
			  .rst_n(rst_n),
			  .play_in(play_in),
			  .tick_in(tick_in),
			  .audio0_in(audio0_in),
			  .audio1_in(audio1_in),
			  .req_out(req_out),
			  .ws_out(ws_out),
			  .sck_out(sck_out),
			  .sdo_out(sdo_out),
			  .i2s(i2s)
			  );

   ////////////////////////////////////////////////////////////////////////////
   //
   // Include SVA assertion module bindings
   //
   ////////////////////////////////////////////////////////////////////////////

`include "sva_bindings.svh"

    initial 
      begin
	 int file;
	 int cycle;
	 cycle = 0;
	 file = $fopen("reports/i2s_unit_simulation.txt", "w");
	 $fdisplay(file, "%6s %7s %7s %9s %9s  %7s %6s %7s %7s", "CYCLE", "play_in", "tick_in", "audio0_in", "audio1_in", "req_out", "ws_out", "sck_out", "sdo_out");
	 wait(rst_n);
	 forever
	   begin
	      @(negedge clk iff rst_n == '1);
	      $fdisplay(file, "%6d       %1b       %1b %9d %9d        %1b      %1b       %1b       %1b", cycle, play_in, tick_in, audio0_in, audio1_in, req_out, ws_out, sck_out, sdo_out);
	      ++cycle;
	   end
      end
   
   initial
     begin
	save_test_parameters("reports/3_vsim_i2s_unit_test_parameters.txt");	
     end
   
endmodule 


`endif
