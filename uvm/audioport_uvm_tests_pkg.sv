package audioport_uvm_tests_pkg;

`ifndef SYNTHESIS
   
`include "uvm_macros.svh"

   // Import packages needed by the tests defined in this file
   import uvm_pkg::*;
   import apb_pkg::*;
   import audioport_pkg::*;
   import audioport_util_pkg::*;   
   import apb_env_pkg::*;   
   import control_unit_env_pkg::*;
   import audioport_env_pkg::*;

   // apb_test related classes

`ifdef apb_test_classes   // The ifdef flags are set in 0_setup_audioport.tcl
`include "apb_sequence_config.svh"
`include "apb_sequence.svh"
`include "apb_test.svh"
`endif

   // control_unit_uvm_test related classes   

`ifdef control_unit_uvm_test_classes   
`include "control_unit_sequence.svh"
`include "control_unit_uvm_test.svh"      
`endif
   
   // audioport_uvm_test related classes   

`ifdef audioport_uvm_test_classes   
`include "audioport_sequence_config.svh"      
`include "audioport_isr_sequence_base.svh"
`include "audioport_isr_sequence.svh"
`include "audioport_main_sequence_base.svh"
`include "audioport_main_sequence.svh"
`include "audioport_master_sequence.svh"
`include "audioport_uvm_test.svh"      
`endif
   
   // my_uvm_test related classes   

`ifdef my_uvm_test_classes      
// `include "my_uvm_sequence.svh"
// `include "my_uvm_test.svh"      
`endif
      
`endif //  `ifndef SYNTHESIS
   
endpackage
