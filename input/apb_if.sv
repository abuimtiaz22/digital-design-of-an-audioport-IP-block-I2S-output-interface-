//
//  apb_if.sv
//
//  Interface object that provides a functional model of the APB bus
//  Parameter APB_INPUT_DELAY (defined in apb_pkg.sv) 
//  can be used to delay write data 

`include "audioport.svh"

import audioport_pkg::*;
import apb_pkg::*;

interface apb_if (input logic clk, input logic rst_n);
   
   logic [31:0] paddr;
   logic [31:0] pwdata;
   logic [31:0] prdata;
   logic 	psel;
   logic        penable;
   logic 	pwrite;
   logic 	pready;
   logic 	pslverr;

   modport master (
		   output paddr,
		   output pwdata,
		   input  prdata,
		   output psel,
		   output penable,
		   output pwrite,
		   input  pready,
		   input  pslverr);

   modport slave (
		   input paddr,
		   input pwdata,
		   output  prdata,
		   input psel,
		   input penable,
		   input pwrite,
		   output  pready,
		   output  pslverr);
   

`ifndef SYNTHESIS

   //////////////////////////////////////////////////////////////////
   //
   // Clocking block that captures inputs and outputs on posedge clk
   //
   //////////////////////////////////////////////////////////////////
   
   clocking cb @(posedge clk);
      input 		      pready, prdata;
      output 		      #(APB_INPUT_DELAY) psel, pwrite, penable,
			      pwdata, paddr;
   endclocking

   //////////////////////////////////////////////////////////////////
   //
   // Task subprograms for driving this interface
   //
   //////////////////////////////////////////////////////////////////
   
   task reset;
      pwrite <= '0;
      paddr <= 0;
      pwdata <= 0;
      penable <= '0;
      psel <= '0;
      @(posedge rst_n);
   endtask

   task init;
      pwrite <= '0;
      paddr <= 0;
      pwdata <= 0;
      penable <= '0;
      psel <= '0;
   endtask

   task set(input logic [31:0] addr, input logic [31:0] data, input logic sel, input logic enable, input logic write);
      pwrite <= write;
      paddr <= addr;
      pwdata <= data;
      penable <= enable;
      psel <= sel;
   endtask
   
   task write(input logic [31:0] addr, input logic [31:0] data, output logic fail);
      int wait_counter;

      // 1. APB SETUP Phase
     
      @cb;
      
      cb.pwrite <= '1;
      cb.paddr <= addr;
      cb.pwdata <= data;
      cb.penable <= '0;		
      if (addr >= DUT_START_ADDRESS && addr <= DUT_END_ADDRESS)
        cb.psel <= '1;
      else
	cb.psel <= '0;

      // 2. APB ACCESS Phase

      @cb;
      
      cb.penable <= '1;      

      wait_counter = 0;
      while (wait_counter <= APB_MAX_WAIT_STATES)
	begin
	   @(cb)
	     if (cb.pready == '1)
	       break;
	   wait_counter = wait_counter + 1;
	end		

      if (wait_counter > APB_MAX_WAIT_STATES) fail = '1;
      else fail = '0;
      cb.penable <= '0;
      cb.psel <= '0;				
      cb.paddr <= '0;

   endtask


   task read(input logic [31:0] addr,  output logic [31:0] data, output logic fail);
      int wait_counter;

      // 1. APB SETUP Phase
      
      @cb;      

      cb.pwrite <= '0;
      cb.paddr <= addr;
      cb.penable <= '0;		
      if (addr >= DUT_START_ADDRESS && addr <= DUT_END_ADDRESS)
	cb.psel <= '1;
      else
	cb.psel <= '0;

      // 2. APB ACCESS Phase

      @cb;      

      cb.penable <= '1;
      wait_counter = 0;
      while (wait_counter <= APB_MAX_WAIT_STATES)
	begin
	   @cb 
	     if (cb.pready == '1) 
	       break;
	   wait_counter = wait_counter + 1;		     
	end
      if (wait_counter > APB_MAX_WAIT_STATES) fail = '1;
      else fail = '0;
      data = cb.prdata;
      cb.penable <= '0;
      cb.psel <= '0;
      cb.paddr <= '0;				
      
   endtask
     

   task monitor(output logic tx_ok, output logic [31:0] addr,  output logic [31:0] data, output logic write_mode);
      
      @cb;  
      addr = paddr;
      if (penable == '1 && cb.pready == '1)
	begin
	   if (pwrite == '1)
	     begin
		data = pwdata;
		write_mode = '1;
	     end
	   else
	     begin	     
		data = cb.prdata;		  
		write_mode = '0;
	     end
	   tx_ok = '1;
	end
      else
	tx_ok = '0;
   endtask

   //////////////////////////////////////////////////////////////////
   //
   // Assertions
   //
   //////////////////////////////////////////////////////////////////

`ifndef DISABLE_ASSERTIONS
   
   property signal_is_valid(signal);
      @(posedge clk)
	!$isunknown(signal);
   endproperty

   psel_valid: assert property( signal_is_valid (psel) );
   penable_valid: assert property( signal_is_valid (penable) );
   pwrite_valid: assert property( signal_is_valid (pwrite) );
   paddr_valid: assert property( signal_is_valid (paddr) );
   pwdata_valid: assert property( signal_is_valid (pwdata) );
   pready_valid: assert property( signal_is_valid (pready) );
   pslverr_valid: assert property( signal_is_valid (pslverr) );

   property psel_to_penable;
      @(posedge clk) disable iff (rst_n == '0)
	$rose(psel) |=> penable;
   endproperty

   psel_to_penable_ok: assert property(psel_to_penable);
   psel_to_penable_cov: cover property(psel_to_penable);

  property max_wait_states;
     @(posedge clk) disable iff (rst_n == '0)
       psel && $rose(penable) |-> !pready [*0:APB_MAX_WAIT_STATES] ##1 pready;
  endproperty

   max_wait_states_ok: assert property(max_wait_states);

   property penable_deasserted;
      @(posedge clk) disable iff (rst_n == '0)
	$rose(penable && pready) |=> !penable;
   endproperty
   
   penable_deassert_ok: assert property(penable_deasserted);
   penable_deassert_cov: cover property(penable_deasserted);
 `endif
   
`endif
   
endinterface

   

