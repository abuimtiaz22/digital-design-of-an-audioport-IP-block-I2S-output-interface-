
`ifndef SYNTHESIS

`include "audioport.svh"

import apb_pkg::*;
import audioport_pkg::*;
import audioport_util_pkg::*;

`ifdef UVM_TESTBENCH
`include "uvm_macros.svh"
import uvm_pkg::*;
import audioport_uvm_tests_pkg::*;
 `endif

module audioport_tb  #(parameter DUT_VS_REF_SIMULATION = 0);
   
   logic clk;
   logic mclk;
   logic rst_n;
   logic PSEL;
   logic PENABLE;
   logic PWRITE;
   logic [31:0] PADDR;
   logic [31:0] PWDATA;
   logic [31:0] PRDATA;
   logic 	PREADY;
   logic 	PSLVERR;
   logic 	irq_out;
   logic 	ws_out;
   logic 	sck_out;   
   logic 	sdo_out;
   logic 	test_mode_in;
   logic 	scan_en_in;
   logic [31:0] ref_PRDATA;
   logic 	ref_PREADY;
   logic 	ref_PSLVERR;
   logic 	ref_irq_out;
   logic 	ref_ws_out;
   logic 	ref_sck_out;   
   logic 	ref_sdo_out;
   logic 	stop_clocks;
   
   ////////////////////////////////////////////////////////////////////////////
   // Interface object declarations and connections
   ////////////////////////////////////////////////////////////////////////////

   apb_if apb(clk, rst_n);   
   irq_out_if irq(clk, rst_n);   
   i2s_if i2s(rst_n);
   
   assign PSEL = apb.psel;
   assign PENABLE = apb.penable;   
   assign PWRITE = apb.pwrite;
   assign PADDR = apb.paddr;
   assign PWDATA = apb.pwdata;
   assign apb.prdata =  ((PADDR >= DUT_START_ADDRESS && PADDR <= DUT_END_ADDRESS)  ? PRDATA: 32'h00000000);
   assign apb.pready =  ((PADDR >= DUT_START_ADDRESS && PADDR <= DUT_END_ADDRESS ) ? PREADY : 1'b1);
   assign apb.pslverr = ((PADDR >= DUT_START_ADDRESS && PADDR <= DUT_END_ADDRESS)  ? PSLVERR : 1'b0);
   assign irq.irq_out = irq_out;

   localparam real REF_MODEL_DELAY = 0.0;  // For aligning waveforms

   // Delays modeled as transport delays (<= #)
   always @(sdo_out) i2s.sdo <= #(REF_MODEL_DELAY) sdo_out;
   always @(sck_out) i2s.sck <= #(REF_MODEL_DELAY) sck_out;
   always @(ws_out)  i2s.ws  <= #(REF_MODEL_DELAY) ws_out;

   ////////////////////////////////////////////////////////////////////////////
   // Clock and reset generation
   ////////////////////////////////////////////////////////////////////////////
   
   initial
     begin
	clk = '0;
	forever begin
	   if (stop_clocks == '1) break;
	   #(CLK_PERIOD/2) clk = ~clk;
	end
     end

   initial
     begin
	realtime delay;
	mclk = '0;
	delay = real'($urandom_range(0, MCLK_PERIOD/2))/10.0;
	#(delay);
	forever begin
	   if (stop_clocks == '1) break;
	   #(MCLK_PERIOD/2) mclk = ~mclk;
	end
     end
   
   initial
     begin
	rst_n = '0;
	repeat (20) 
	  @(negedge clk) rst_n = '0;
	@(negedge clk) rst_n = '1;	
     end

   ////////////////////////////////////////////////////////////////////////////
   // DUT instantiation
   ////////////////////////////////////////////////////////////////////////////

   audioport DUT_INSTANCE
     (.clk(clk),
      .rst_n(rst_n),
      .mclk(mclk),
      .PSEL(PSEL),
      .PENABLE(PENABLE),
      .PWRITE(PWRITE),
      .PADDR(PADDR),	      
      .PWDATA(PWDATA),
      .PRDATA(PRDATA),
      .PREADY(PREADY),
      .PSLVERR(PSLVERR),
      .irq_out(irq_out),   
      .sck_out(sck_out),   
      .ws_out(ws_out),
      .sdo_out(sdo_out),
      .test_mode_in(test_mode_in),
      .scan_en_in(scan_en_in)      
      );
   

   ////////////////////////////////////////////////////////////////////////////
   // Include SVA assertion module bindings
   ////////////////////////////////////////////////////////////////////////////

 `ifndef GATELEVEL_SIM
 `ifndef POSTLAYOUT_SIM
 
`include "sva_bindings.svh"

`endif
`endif

   ////////////////////////////////////////////////////////////////////////////
   // Test program instantiation for non-UVM test
   ////////////////////////////////////////////////////////////////////////////
   
`ifndef UVM_TESTBENCH

   audioport_test TEST (.*);
   
`else

   ////////////////////////////////////////////////////////////////////////////
   // UVM test setup
   ////////////////////////////////////////////////////////////////////////////
   
   initial
     begin
	int apb_test_cycles;
	string sub;
	sub = student_number.substr(student_number.len()-2,student_number.len()-1);
	apb_test_cycles = 100 + sub.atoi();
	stop_clocks = '0;
	scan_en_in = '0; // disable test mode for all UVM tests
	test_mode_in = '0; // disable test mode for all UVM tests	
	save_test_parameters("reports/3_vsim_audioport_test_parameters.txt");	
	uvm_top.finish_on_completion = 1;
	uvm_config_db #(int)::set(null, "*", "recording_detail", 1);	
	uvm_config_db #(int)::set( null , "" , "APB_TEST_CYCLES" , 200);
	uvm_config_db #(virtual interface apb_if)::set( null , "" , "apb_if_config" , apb);
        uvm_config_db #(virtual interface irq_out_if)::set( null , "" , "irq_out_if_config" , irq);
        uvm_config_db #(virtual interface i2s_if)::set( null , "" , "i2s_if_config" , i2s);      
   	run_test();
        stop_clocks = '1;
        $finish;
   
     end

`endif // !`ifndef UVM_TESTBENCH
   
   initial
     begin
	save_test_parameters("reports/3_vsim_audioport_test_parameters.txt");	
     end

endmodule 

`endif
