###################################################################
# Design Data
###################################################################

set DESIGN_NAME "control_unit"

set DESIGN_FILES [list \
		      "input/apb_pkg.sv" \
		      "input/audioport_pkg.sv" \
		      "input/audioport_util_pkg.sv" 
		 ]

set RTL_FILES [list \
		      "input/control_unit.sv" \
		     ]

set SVA_FILES [list \
		      "input/control_unit_svamod.sv" \
		     ]

set TESTBENCH_FILES [list \
			 "input/apb_if.sv" \
			 "input/irq_out_if.sv" \
			 "input/control_unit_test.sv" \
		         "input/control_unit_tb.sv" \
			]

set RTL_LANGUAGE "SystemVerilog"

set SYSTEMC_SOURCE_FILES    "input/control_unit.cpp"
set SYSTEMC_HEADER_FILES    "input/control_unit.h"
set SYSTEMC_TESTBENCH_FILES ""
set SYSTEMC_MODULES          {  "control_unit"  }

###################################################################
# Timing Constraints
###################################################################

set SDC_FILE input/${DESIGN_NAME}.sdc

set CLOCK_NAMES           {"clk"}
set CLOCK_PERIODS         [list $CLK_PERIOD]
set CLOCK_UNCERTAINTIES   {   0 }
set CLOCK_LATENCIES       {   0 }
set INPUT_DELAYS          { 1.0 }
set OUTPUT_DELAYS         { 1.0 }
set OUTPUT_LOAD             0
set RESET_NAMES           { "rst_n" }
set RESET_STYLES          { "async" }
set RESET_LEVELS          { 0 }

###################################################################
# Settings for simulation scripts
###################################################################

# Simulation run times (set to "-all" to run all)
set RTL_SIMULATION_TIME        "-all"
set GATELEVEL_SIMULATION_TIME  "-all"

# Wave settings
set VSIM_MIXEDLANG_WAVES       "input/1_vsim_control_unit_mixedlang_simulation_waves.tcl"
set VSIM_RTL_WAVES             "input/3_vsim_control_unit_rtl_simulation_waves.tcl"

set VCS_VLOG_RTL_OPTIONS      " +define+RTL_SIM"

###################################################################
# Settings for static verification scripts
###################################################################

# Static verification tool init file
set QUESTA_INIT_FILE "input/rst.questa_init"
set JASPER_INIT_FILE "input/rst.jasper_init"

# Questa static verification directives file for user-created directives
set QUESTA_DIRECTIVES "input/control_unit.questa_dir.tcl"

# Questa PropertyCheck
set QFORMAL_TIMEOUT        2h
set QFORMAL_COVERAGE       0


