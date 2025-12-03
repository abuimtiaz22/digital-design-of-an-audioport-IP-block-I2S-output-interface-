package audioport_env_pkg;

`ifndef SYNTHESIS
   
`include "uvm_macros.svh"

   import uvm_pkg::*;
   import apb_pkg::*;
   import audioport_pkg::*;
   import audioport_util_pkg::*;   
   import apb_env_pkg::*;    
   import control_unit_env_pkg::*;
   
`include "i2s_transaction.svh"   
`include "i2s_monitor.svh"
`include "i2s_agent.svh"   
`include "audioport_comparator.svh"
`include "audioport_predictor.svh"
`include "audioport_scoreboard.svh"
`include "audioport_env.svh"

`endif //  `ifndef SYNTHESIS
   
endpackage
