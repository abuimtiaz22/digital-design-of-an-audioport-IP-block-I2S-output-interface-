//
//  irq_out_if.sv
//
//  Interface object that describes the irq_out output of the audioport
//  This object is needed so that the irq_out port can be handed to
//  the UVM test via the configuration database.
//


`include "audioport.svh"

import audioport_pkg::*;

interface irq_out_if 
   (input logic clk, input logic rst_n);
   
   logic irq_out;

   modport master (input  irq_out);
   modport slave  (output  irq_out);   

`ifndef SYNTHESIS
	
   clocking cb @(posedge clk);
      input irq_out;
   endclocking
   
   task reset;
      @(posedge rst_n);
   endtask


   task monitor(output logic irq_val);
      @cb;  
      irq_val = cb.irq_out;
   endtask

`endif
   
endinterface

   

