if { [file exists assertion_tb.mpf ] == 1 } {
    if { [info exists vsim_project_is_open ] == 0 } {
	set vsim_project_is_open 1
	project open assertion_tb.mpf
    }
} else {
    project new "." assertion_tb
    set vsim_project_is_open 1
}

vlib output/assertion_tb_work
vmap work output/assertion_tb_work

project addfile input/audioport_pkg.sv
project addfile input/assertion_tb.sv

vlog -work work input/apb_pkg.sv
vlog -work work input/audioport_pkg.sv
vlog -work work input/audioport_util_pkg.sv
vlog -work work input/assertion_tb.sv
vsim -t 1ps -msgmode both -fsmdebug -assertdebug -voptargs=+acc work.assertion_tb

run 0
log -r /*

add wave -nofilter Assertion /assertion_tb/*
configure wave -signalnamewidth 1
configure wave -datasetprefix 0

atv log -asserts -enable /assertion_tb/*

run -all

view assertions
wave zoomfull
