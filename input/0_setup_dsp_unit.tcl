###################################################################
# Design Data
###################################################################

set DESIGN_NAME "dsp_unit"

set DESIGN_FILES {  "input/apb_pkg.sv" \
                    "input/audioport_pkg.sv" \
		    "input/audioport_util_pkg.sv" \
                 }

set RTL_FILES    {   "results/dsp_unit_hls_rtl.v"
		    "input/dsp_unit.sv"  \
		 }

set SVA_FILES    {  "input/dsp_unit_svamod.sv" \
		 }

set TESTBENCH_FILES {  "input/dsp_unit_test.sv" \
			"input/dsp_unit_tb.sv" }

set RTL_LANGUAGE "SystemVerilog"

set SYSTEMC_SOURCE_FILES    "input/dsp_unit.cpp"
set SYSTEMC_HEADER_FILES    "input/dsp_unit.h input/dsp_unit_tb.h input/dsp_unit_top.h "
set SYSTEMC_TESTBENCH_FILES "input/dsp_unit_tb.cpp input/dsp_unit_top.cpp input/dsp_unit_sc_main.cpp "
set SYSTEMC_MODULES          {  "dsp_unit"  }

###################################################################
# Timing Constraints
###################################################################

set SDC_FILE input/dsp_unit.sdc

set CLOCK_NAMES           { "clk" }
set CLOCK_PERIODS         [list $CLK_PERIOD]
set CLOCK_UNCERTAINTIES   { 0 }
set CLOCK_LATENCIES       { 0 }
set INPUT_DELAYS          { 0 }
set OUTPUT_DELAYS         { 0 }
set OUTPUT_LOAD             0
set RESET_NAMES           { "rst_n" }
set RESET_LEVELS          { 0 }
set RESET_STYLES          { async }

###################################################################
# High-Level Synthesis Settings
###################################################################

set CATAPULT_DIRECTIVE_FILE   "${LAUNCH_DIR}/input/dsp_unit_catapult_directives.tcl"
set CATAPULT_PROJECT_DIR      "${LAUNCH_DIR}/results"
set CATAPULT_SUPPRESS_WARNINGS { OPT-4 CIN-108 CLUSTER-24 LIB-142}
set CATAPULT_REMOVE_PROJECT    1

set STRATUS_MODULE_CONFIG_FILE "${LAUNCH_DIR}/input/dsp_unit_stratus_cfg.tcl"

###################################################################
# Settings for simulation scripts
###################################################################

set SC_EXE_ARGS               "-run systemc -output results"
set SYSTEMC_SIMULATION_TIME   "-all"
set VSIM_SYSTEMC_OPTIONS      "-sc_arg \"-run\" -sc_arg \"vsim_systemc\" -sc_arg \"-output\" -sc_arg \"results\" "
set VSIM_SC_WAVES             "input/1_vsim_dsp_unit_systemc_simulation_waves.tcl"
set XCELIUM_SC_WAVES          "input/1_xcelium_dsp_unit_systemc_simulation_waves.tcl"

set RTL_SIMULATION_TIME       "-all"
set VSIM_SC_RTL_WAVES         "input/3_vsim_dsp_unit_systemc_rtl_simulation_waves.tcl"
set VSIM_SCRTL_OPTIONS        "-t 1ps -sc_arg \"-run\" -sc_arg \"vsim_rtl\" -sc_arg \"-output\" -sc_arg \"results\""

###################################################################
# Settings for static verification scripts
###################################################################

set QUESTA_INIT_FILE          "input/rst.questa_init"
set QAUTOCHECK_DISABLE_MODULES { "dsp_unit_rtl" }

