///////////////////////////////////////////////////////////////////////////////
//
// audioport.svh
//
// This file is included in all source files. Common macro definitions
// can be placed here.
//
///////////////////////////////////////////////////////////////////////////////

//----------------------------------------------------------------------------
// Time unit and resolution definition
//----------------------------------------------------------------------------

`ifndef SYNTHESIS
timeunit 1ns;
timeprecision 1ps;
`endif

//----------------------------------------------------------------------------
// Macros
//----------------------------------------------------------------------------

// Enable assertion module bindings project-wide
//`define DISABLE_ASSERTIONS 1

`define xcheck(name) X_``name``: assert property ( @(posedge clk) disable iff (rst_n !== '1) !$isunknown( name) ) else $error(`"name has unknown bits.`")   
`define xcheckm(name) X_``name``: assert property ( @(posedge mclk) disable iff (muxrst_n !== '1) !$isunknown( name) ) else $error(`"name has unknown bits.`")   



