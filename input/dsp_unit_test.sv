`include "audioport.svh"

import audioport_pkg::*;
import audioport_util_pkg::*;

program  dsp_unit_test(
		       input logic 			   clk,
		       input logic 			   rst_n,
		       output logic 			   tick_in,
		       output logic 			   cfg_in,
		       output logic 			   level_in,
		       output logic 			   clr_in, 
		       output logic [23:0] 		   audio0_in,
		       output logic [23:0] 		   audio1_in, 
		       output logic [DSP_REGISTERS*32-1:0] dsp_regs_in,
		       output logic [31:0] 		   level_reg_in,
		       output logic [31:0] 		   cfg_reg_in,
		       input logic [23:0] 		   audio0_out,
		       input logic [23:0] 		   audio1_out,
		       input logic 			   tick_out
		       );

   logic [15:0] 					   level;
   
   // To do: Declare a clocking block ---------------------------------------
   default clocking cb @(posedge clk);
      input 						   audio0_out, audio1_out;
      output 						   tick_in, cfg_in, level_in, clr_in, audio0_in, audio1_in, dsp_regs_in, cfg_reg_in, level_reg_in;
   endclocking 
   // ----------------------------------------------------------------------


   initial
     begin

	fork
	   begin
	      logic [2*FILTER_TAPS-1:0][31:0] filter_taps;
	      if (read_filter_taps(filter_taps) == 0)
		begin
		   $info("Using default filter coefficients.");
		end
	      
	      // Initialize inputs directly before reset
	      tick_in = '0;
	      cfg_in = '0;
	      level_in = '0;
	      clr_in = '0;		
	      audio0_in = '0;
	      audio1_in = '0;
	      level_reg_in = '0;
	      cfg_reg_in = '0;
	      dsp_regs_in = '0;
	      
	      // Wait for rst_n to go high
	      wait (rst_n);

	      $info("T1: Program filter");

	      ##1;
	      
	      for (int i=0; i < 2*FILTER_TAPS; ++i)
		begin
		   cb.dsp_regs_in[32*i +: 32] <= filter_taps[i];
		end
	      
	      ##1;
	      cb.cfg_in <= '1;
	      ##1;
	      cb.cfg_in <= '0;
	      ##10;

	      $info("T2: Set level");

	      level = 16'h8000;
	      cb.level_reg_in <= { level, level };
	      
	      cb.level_in <= '1;
	      ##1;
	      cb.level_in <= '0;	
	      ##10;

	      $info("T3: Impulse, filter enabled");	

	      cb.cfg_reg_in <= 32'b00000000_00000000_00000000_00000001;
	      cb.cfg_in <= '1;
	      ##1;
	      cb.cfg_in <= '0;
	      ##10;

	      audio0_in = 24'h7FFFFF;
	      audio1_in = 24'h800000;
	      cb.tick_in <= '1;
	      ##1;
	      cb.tick_in <= '0;
	      ##(CLK_DIV_48000);

	      repeat(FILTER_TAPS)
		begin
		   audio0_in = 24'h000000;
		   audio1_in = 24'h000000;
		   cb.tick_in <= '1;
		   ##1;
		   cb.tick_in <= '0;
		   ##(CLK_DIV_48000);
		end
	      
	      ##10;

	      $info("T4: Impulse, filter disabled");		
	      
	      cb.cfg_reg_in <= 32'b00000000_00000000_00000000_00000001;
	      cb.cfg_in <= '1;
	      ##1;
	      cb.cfg_in <= '0;
	      ##10;

	      audio0_in = 24'h7FFFFF;
	      audio1_in = 24'h800000;
	      cb.tick_in <= '1;
	      ##1;
	      cb.tick_in <= '0;
	      ##(CLK_DIV_48000);

	      repeat(FILTER_TAPS)
		begin
		   audio0_in = 24'h000000;
		   audio1_in = 24'h000000;
		   cb.tick_in <= '1;
		   ##1;
		   cb.tick_in <= '0;
		   ##(CLK_DIV_48000);
		end	


	      ##10;

	      $info("T5: Continuous play, filter enabled, level changes");
	      
	      cb.cfg_reg_in <= 32'b00000000_00000000_00000000_00000001;
	      cb.cfg_in <= '1;
	      ##1;
	      cb.cfg_in <= '0;
	      ##10;

	      audio0_in = 2**22-1;
	      audio1_in = -2**21-1;
	      for (int i = 0; i < 128; ++i) 
		begin

		   if (i % 10 == 0)
		     audio0_in = -audio0_in;
		   if (i % 5 == 0)
		     audio1_in = -audio1_in;

		   cb.tick_in <= '1;
		   ##1;
		   cb.tick_in <= '0;
		   ##(CLK_DIV_48000/20);	     
		   level = level - 256;
		   cb.level_reg_in <= { level, level };
		   cb.level_in <= '1;
		   ##1;
		   cb.level_in <= '0;	
		   ##(CLK_DIV_48000 - CLK_DIV_48000/20 -1);		     
		end 

	      ##10;

	      $info("T6: Clear audio data");
	      
	      cb.clr_in <= '1;
	      ##1;
	      cb.clr_in <= '0;	
	      ##10;
	      
	      $finish;
	   end
	   begin
	      #(WATCHDOG_TIME);
	      $error("WATCHDOG_TIME exceeded!");
	      $finish;
	   end
	join_any	   
     end
   

endprogram
   
