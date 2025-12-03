`include "audioport.svh"

import audioport_pkg::*;

///////////////////////////////////////////////////////////////////////////////
//
// i2s_if: SystemVerilog interface and Functional model for I2S bus.
//
///////////////////////////////////////////////////////////////////////////////

interface i2s_if 
   (input logic rst_n);

   // ----------------------------------------------------------------------------------
   // Interface signal declarations
   // ----------------------------------------------------------------------------------
   
   logic sck;
   logic ws;
   logic sdo;
   // ------------------------------------------------------------

   // ----------------------------------------------------------------------------------
   // Interface modport declarations
   // ----------------------------------------------------------------------------------
   
   modport master (input  sck, ws, sdo);
   modport slave  (output  sck, ws, sdo);
   // ------------------------------------------------------------
   
`ifndef SYNTHESIS


   // ----------------------------------------------------------------------------------
   // reset task: Makes testbench wait for reset to rise
   // ----------------------------------------------------------------------------------
   
   task reset;
      @(posedge rst_n);
   endtask

   
   // ----------------------------------------------------------------------------------
   // monitor task: Extracts L+R 24-bit data words from serial audio signals
   // ----------------------------------------------------------------------------------
   
   task monitor(output logic tx_ok,
		output logic [1:0][23:0] audio_out
		);      

      localparam int 					     LEFT = 0;
      localparam int 					     RIGHT = 1;      
      
      // Shift registers
      logic [47:0] 	 srg;

      // Bit counters for error checking
      logic [4:0] 			 lctr;
      logic [4:0] 			 rctr;      
      lctr = 0;
      rctr = 0;
      
      // Read data to shift registers until WS goes up

      do
	begin
	   @(posedge sck)
	     begin
		lctr = lctr+1;
		
		srg[47:1] = srg[46:0];
		srg[0] = sdo;

	     end
	end while (ws == '0);
      

      // Read data to shift registers until WS goes down afain
      do
	begin
	   @(posedge sck)
	     begin
		rctr = rctr+1;

		srg[47:1] = srg[46:0];
		srg[0] = sdo;

	     end
	end while (ws == '1);
      
      audio_out[LEFT] = srg[47:24];
      audio_out[RIGHT] = srg[23:0];

      // Counter values should be lctr == 24 and rctr == 23
      if (rctr < 23 || lctr < 24)
	tx_ok = 0;
      else
	tx_ok = 1;
      
   endtask

`endif
   
endinterface


///////////////////////////////////////////////////////////////////////////////
//
// Testbench for i2s_if
//
///////////////////////////////////////////////////////////////////////////////

`ifndef SYNTHESIS

module i2s_if_tb;
   logic clk;
   logic rst_n;
   logic       sck, ws;
   logic [1:0] sck_ctr;
   logic [5:0] ws_ctr;
   logic [47:0] tx_data;
   logic 	tx_bit;
   logic 	rx_ok = '0;

   logic [1:0][23:0] audio_out;

   i2s_if i2s_bus(rst_n);
   assign i2s_bus.sck = sck;
   assign i2s_bus.ws = ws;
   assign i2s_bus.sdo = tx_bit;
   
   initial
     begin
	clk = '0;
	forever #(CLK_PERIOD/2) clk = ~clk;
     end

   initial
     begin
	
	fork

	   ////////////////////////////////////////////////////////////
	   //
	   // Transmit side
	   //
	   ////////////////////////////////////////////////////////////
	   
	   begin
	      sck = '0;
	      ws = '0;
	      sck_ctr = 0;
	      ws_ctr = 0;
	      tx_data = '0;

	      // Generate reset
	      rst_n = '0;
	      @(negedge clk);
	      @(negedge clk);
	      rst_n = '1;

	      // This loop generates two counter signals sck_ctr and ws_ctr
	      //   sck_ctr = 1/4 clk
	      //   ws_ctr = 1/48 sck_ctr
	      // sck and ws are decoded from these
	      
	      forever
		begin
		   
		   @(posedge clk)
		     begin
			if (sck_ctr == 2'b11)
			  begin
			     sck = !sck;
			     
			     // Advance WS counter on SCK falling edges
			     if (sck == '0)
			       begin
				  
				  if (ws_ctr == 47)
				    begin
				       ws = ! ws;
				       ws_ctr = 0;
				    end
				  else if (ws_ctr == 23)
				    begin
				       ws = ! ws;
				       ws_ctr = ws_ctr + 1;				       
				    end
				  else
				    begin
				       ws_ctr = ws_ctr + 1;
				    end

				  // Next tx data words
				  if (ws_ctr == 1)
				    begin
				       tx_data[47:24] = $urandom;
				       tx_data[23:0] = $urandom;				       
				    end

				  // Select tx bit
				  if (ws_ctr == 0)
				    tx_bit = tx_data[0];
				  else
				    tx_bit = tx_data[48-ws_ctr];
			       end 
			  end 
			
			sck_ctr = sck_ctr + 1;
		     end 
		end 
	   end 

	   ////////////////////////////////////////////////////////////
	   //
	   // Receive side (interface task test)
	   //
	   ////////////////////////////////////////////////////////////
	   

	   begin

	      i2s_bus.reset;
	      $info("i2s reset");
	      
	      forever
		begin
		   rx_ok = '0;
		   i2s_bus.monitor(rx_ok, audio_out);
		   $info("i2s rx");
			assert (audio_out[0] == tx_data[47:24] && audio_out[1] == tx_data[23:0])
			  else $error("i2s_if monitor returned wrong data, TX = (%h, %h), RX = (%h, %h)", 
				      tx_data[47:24], audio_out[0], tx_data[23:0], audio_out[1]);
		end
	   end
	join
	
     end // initial begin
   
   
endmodule

`endif
