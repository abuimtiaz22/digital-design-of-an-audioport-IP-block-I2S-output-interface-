set DESIGN_NAME "tlm_audioport"

set SYSTEMC_SOURCE_FILES  {			    }

set SYSTEMC_HEADER_FILES    { 			      }

set SYSTEMC_TESTBENCH_FILES { \
				  "input/tlm_audioport.cpp" \
				  "input/tlm_cpu.cpp" \
				  "input/tlm_dac.cpp" \
				  "input/tlm_scoreboard.cpp" \
				  "input/tlm_sc_main.cpp" \
			      }
set VSIM_SCCOM_OPTIONS "-DSC_DISABLE_VIRTUAL_BIND"

set SYSTEMC_SIMULATION_TIME "-all"

set VSIM_SC_WAVES "input/1_vsim_tlm_audioport_systemc_simulation_waves.tcl"
