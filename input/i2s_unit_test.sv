//
//  i2s_unit.sv: test program for i2s_unit.
//
//

`include "audioport.svh"

import audioport_pkg::*;
import audioport_util_pkg::*;

program i2s_unit_test(
		      input logic 	  clk,
		      input logic 	  rst_n,
		      output logic 	  play_in,
		      output logic 	  tick_in,
		      output logic [23:0] audio0_in,
		      output logic [23:0] audio1_in,		      
		      input logic 	  req_out,
		      input logic 	  ws_out,
		      input logic 	  sck_out,
		      input logic 	  sdo_out,
					  i2s_if i2s
		      );
   localparam int 			  TEST_LENGTH = 5;
   
   logic 			  tx_done = '0;
   logic 			  rx_done = '0;
   int 				  frame_number;
   logic [23:0] 		  LEFT_PATTERNS[TEST_LENGTH];
   logic [23:0] 		  RIGHT_PATTERNS[TEST_LENGTH];
   logic [1:0][23:0] 		  fifo[$];
   logic [1:0][23:0] 		  input_pattern;
   logic [1:0][23:0] 		  reference_pattern;      
   int 				  sample_counter;
   int 				  cycle_counter;
   
   int 				  test_samples;
   int 				  deadlock_counter;
   
   default clocking cb @(posedge clk);
      input sck_out, ws_out, sdo_out, req_out;
      output audio0_in, audio1_in, tick_in, play_in;
   endclocking

   initial
     begin
	reset_test_stats; 

	tick_in = '0;
	play_in = '0;
	audio0_in = '0;
	audio1_in = '0;	      	      
	
	wait (rst_n);
	@(posedge clk);
	
	////////////////////////////////////////////////////////////////
	//
	// Transmitter side
	//
	////////////////////////////////////////////////////////////////

	fork
	   begin : data_generator
	      int 				  clock_divider;
	      logic [11:0] 			  counter;
	      
	      ///////////////////////////////////////////////////////////////////
	      // Test 1: Directed Test
	      ////////////////////////////////////////////////////////////////////

	      $info("T1: Regular Pattern Test");
	      
	      // Initialize test variables
	      sample_counter = 0;		   
	      frame_number = 0;
	      rx_done = '0;
	      test_samples = TEST_LENGTH;
	      fifo.delete();
	      
	      input_pattern[0] = '0;
	      input_pattern[1] = '0;
	      fifo.push_back(input_pattern);
	      
	      ##16;		   
	      
	      // Enable playback
	      cb.play_in <= '1;
	      ##1;
	      
	      // Sample generator loop
	      sample_counter = 0;
	      deadlock_counter = 0;
	      while (sample_counter < TEST_LENGTH)
		begin
		   if(cb.req_out)
		     begin
			if (sample_counter == 0)
			  begin
			     input_pattern[0] = '1;
			     input_pattern[1] = '0;
			  end
			else if (sample_counter == TEST_LENGTH-1)
			  begin
			     input_pattern[0] = '0;
			     input_pattern[1] = '1;
			  end
			else
			  begin
			     input_pattern[0] = 24'hfff000;
			     input_pattern[1] = 24'hf0f0f0;
			  end
			fifo.push_back(input_pattern);
			cb.tick_in <= '1;
			cb.audio0_in <= input_pattern[0];
			cb.audio1_in <= input_pattern[1];
			++sample_counter;
			##1;
			cb.tick_in <= '0;			     
		     end
		   ##1;
		   assert ( deadlock_counter < 100000 ) else begin
		      $error("Deadlock detected: req_out did not rise in 100000 cycles!");
		      break;
		   end
		   ++deadlock_counter;
		end

	      cb.play_in <= '0;

	      update_test_stats;	      


	      ///////////////////////////////////////////////////////////////////
	      // Test 2: Stop Test
	      ////////////////////////////////////////////////////////////////////

	      // Wait some time between tests
	      ##(2*2*24*MCLK_DIV_48000);
	      
	      $info("T2: Stop Test");
	      
	      // Initialize test variables
	      sample_counter = 0;		   
	      cycle_counter = 0;
	      frame_number = 0;
	      rx_done = '0;
	      test_samples = TEST_LENGTH;
	      fifo.delete();
	      
	      input_pattern[0] = '0;
	      input_pattern[1] = '0;
	      fifo.push_back(input_pattern);
	      
	      ##16;		   
	      
	      // Enable playback
	      cb.play_in <= '1;
	      ##1;
	      
	      // Sample generator loop
	      sample_counter = 0;
	      deadlock_counter = 0;
	      while (sample_counter < TEST_LENGTH)
		begin
		   if(cb.req_out)
		     begin
			cycle_counter = 0;
			if (sample_counter == 0)
			  begin
			     input_pattern[0] = '1;
			     input_pattern[1] = '0;
			  end
			else if (sample_counter == TEST_LENGTH-1)
			  begin
			     input_pattern[0] = '0;
			     input_pattern[1] = '1;
			  end
			else
			  begin
			     input_pattern[0] = 24'hfff000;
			     input_pattern[1] = 24'hf0f0f0;
			  end
			fifo.push_back(input_pattern);
			cb.tick_in <= '1;
			cb.audio0_in <= input_pattern[0];
			cb.audio1_in <= input_pattern[1];
			++sample_counter;
			##1;
			cb.tick_in <= '0;			     
		     end // if (cb.req_out)
		   else
		     begin
			++cycle_counter;
			if (sample_counter == TEST_LENGTH-1 && cycle_counter == 24*MCLK_DIV_48000)
			  begin
			     $info("T2: STOP");
			     break;
			  end
		     end
		   ##1;
		   assert ( deadlock_counter < 100000 ) else begin
		      $error("Deadlock detected: req_out did not rise in 100000 cycles!");
		      break;
		   end
		   ++deadlock_counter;
		end

	      cb.play_in <= '0;

	      update_test_stats;	      
	      
	      
	      
	      ///////////////////////////////////////////////////////////////////
	      // Test 3: Random Pattern Test
	      ////////////////////////////////////////////////////////////////////

	      // Wait some time between tests
	      ##(4*2*24*MCLK_DIV_48000);
	      
	      $info("T3: Random");

	      // Initialize test variables
	      
	      sample_counter = 0;		   
	      frame_number = 0;
	      rx_done = '0;
	      test_samples = TEST_LENGTH;
	      fifo.delete();
	      
	      input_pattern[0] = '0;
	      input_pattern[1] = '0;
	      fifo.push_back(input_pattern);
	      
	      ##1;
	      
	      // Enable playback
	      cb.play_in <= '1;
	      ##1;
	      
	      // Sample generator loop
	      sample_counter = 0;
	      deadlock_counter = 0;
	      while (sample_counter < TEST_LENGTH)
		begin
		   if(cb.req_out)
		     begin
			input_pattern[0] = $urandom;
			input_pattern[1] = $urandom;			
			fifo.push_back(input_pattern);
			cb.tick_in <= '1;
			cb.audio0_in <= input_pattern[0];
			cb.audio1_in <= input_pattern[1];
			++sample_counter;
			##1;
			cb.tick_in <= '0;	
		     end
		   ##1;
		   assert (deadlock_counter < 100000) else begin
		      $error("Deadlock detected: req_out did not rise in 100000 cycles!");
		      break;
		   end
		   ++deadlock_counter;
		end
	      
	      
	      cb.play_in <= '0;
	      
	      tx_done = '1;

	      #10us;
	      
	      $info("Test end");
	      
	   end : data_generator

	////////////////////////////////////////////////////////////////
	//
	// Receiver side
	//
	////////////////////////////////////////////////////////////////

	   begin : data_checker
	      logic tx_ok;
	      logic [1:0][23:0] audio;

	      while (!tx_done)
		begin 
		   i2s.monitor(tx_ok, audio);
		   reference_pattern = fifo.pop_front();
		   
		   ia_i2s_txrx_check: assert(audio[0] == reference_pattern[0] && audio[1] == reference_pattern[1])
			  else 
			    begin
			       $error("tx error: left pattern: %h => %h right pattern: %h => %h", 
				      reference_pattern[0], audio[0], reference_pattern[1], audio[1]);
			       assert_error("ia_i2s_txrx_check");
			    end
		   frame_number = frame_number + 1;
		   if (frame_number == test_samples) rx_done = '1;			     
		end

	   end : data_checker
	   
	   begin
	      #(WATCHDOG_TIME);
	      $error("WATCHDOG_TIME exceeded!");
	      $finish;
	   end
	   
	join_any
	disable fork;
	
	// 7. Report results

	update_test_stats;
	
	$display("#####################################################################################################");	
	$display("i2s_unit_test results: PASSED: %d / FAILED: %d", tests_passed, tests_failed);
	$display("#####################################################################################################");	

	$finish;
	
     end
endprogram
