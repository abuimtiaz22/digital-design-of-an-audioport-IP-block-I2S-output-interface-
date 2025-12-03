`include "audioport.svh"

import audioport_pkg::*;
import audioport_util_pkg::*;

program audioport_test
  
  (input logic clk,
   input logic 	rst_n,
   input logic 	mclk,
		apb_if apb,
		irq_out_if irq,
		i2s_if i2s, 
   output logic test_mode_in,
   output logic scan_en_in, 
   input logic 	sck_out,
   input logic 	ws_out,
   input logic 	sdo_out
   );

   localparam int DFT_CYCLES = 1000;
   
   initial
     begin : test_program
	logic         fail;
	logic [31:0]  addr;
	logic [31:0]  wdata;
	logic [31:0]  rdata;
	
	scan_en_in = '0;
	test_mode_in = '0;	
	apb.init;
	wait(rst_n);
	repeat(20) @(negedge clk);
	
	fork
	   begin
	      	      
	      
	      /////////////////////////////////////////////////////////////////
	      // Register access
	      /////////////////////////////////////////////////////////////////	

	      addr = CFG_REG_ADDRESS;
	      wdata = 32'b00000000_00000000_00000000_00000001;
	      apb.write(addr, wdata, fail);
	      apb.read(addr, rdata, fail);	 		      
	      
	      repeat(10) @(negedge clk);

	      /////////////////////////////////////////////////////////////////
	      // Test mode
	      /////////////////////////////////////////////////////////////////	
	      
	      $assertoff;
	      
	      scan_en_in = '1;
	      test_mode_in = '1;	

	      #10us;
	      
	      repeat(DFT_CYCLES) begin
		 apb.set(32'hffffffff, 32'hffffffff, '1, '1, '1);	     	   
		 @(negedge clk);
	      end
	      
	      repeat(DFT_CYCLES) begin
		 apb.set(32'h00000000, 32'h00000000, '0, '0, '0);
		 @(negedge clk);
	      end

	      repeat(DFT_CYCLES) begin
		 apb.set(32'hffffffff, 32'hffffffff, '1, '1, '1);	     	   
		 @(negedge clk);
	      end
	      
	      $asserton;
	   end // fork begin

	   begin
	      #(WATCHDOG_TIME);
	      $error("WATCHDOG_TIME exceeded!");
	      $finish;
	   end

	join_any
	
	$finish;
	
     end : test_program

endprogram
   
