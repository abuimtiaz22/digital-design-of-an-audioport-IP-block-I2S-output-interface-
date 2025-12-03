`include "audioport.svh"

import audioport_pkg::*;

module dsp_unit(
		input logic 			   clk,
		input logic 			   rst_n,
		input logic 			   tick_in,
		input logic 			   cfg_in,
		input logic 			   level_in,
		input logic 			   clr_in, 
		input logic [23:0] 		   audio0_in,
		input logic [23:0] 		   audio1_in, 
		input logic [DSP_REGISTERS*32-1:0] dsp_regs_in,
		input logic [31:0] 		   level_reg_in,
		input logic [31:0] 		   cfg_reg_in,
		output logic [23:0] 		   audio0_out,
		output logic [23:0] 		   audio1_out,
		output logic 			   tick_out		
		);

   ////////////////////////////////////////////////////////////////////////////
   // Include SVA assertion module bindings here if testbench is in SystemC
   ////////////////////////////////////////////////////////////////////////////

`ifdef design_top_is_dsp_unit
`ifdef HLS_RTL
 `include "sva_bindings.svh"
`endif
`endif   

   ///////////////////////////////////////////////////////////////////////////////
   // Uncomment this instantiation of HLS-generated module instantiation after HLS.
   // The module is in file results/dsp_unit_rtl.v.
   ///////////////////////////////////////////////////////////////////////////////
   
    dsp_unit_rtl dsp_unit_rtl_1 (.*);
   
endmodule



