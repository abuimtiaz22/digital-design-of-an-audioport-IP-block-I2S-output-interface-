onerror {add wave -noupdate -divider {Wave setup error!}; resume}

set CLK_NAME_COLOR {Pale Green}
set MCLK_COLOR {Coral}
set MCLK_NAME_COLOR {Pink}

add wave -itemcolor $CLK_NAME_COLOR -noupdate -expand -group CLOCKS /cdc_unit_tb/DUT_INSTANCE/clk
add wave -itemcolor $MCLK_NAME_COLOR -color $MCLK_COLOR -noupdate -expand -group CLOCKS /cdc_unit_tb/DUT_INSTANCE/mclk
add wave -itemcolor $CLK_NAME_COLOR -noupdate -expand -group CLOCKS /cdc_unit_tb/DUT_INSTANCE/rst_n

add wave -itemcolor $CLK_NAME_COLOR -noupdate -expand -group "TEST MUXING" /cdc_unit_tb/DUT_INSTANCE/test_mode_in
add wave -itemcolor $CLK_NAME_COLOR -noupdate -expand -group "TEST MUXING" /cdc_unit_tb/DUT_INSTANCE/clk
add wave -itemcolor $MCLK_NAME_COLOR -color $MCLK_COLOR -noupdate -expand -group "TEST MUXING" /cdc_unit_tb/DUT_INSTANCE/mclk
add wave -itemcolor $MCLK_NAME_COLOR -color $MCLK_COLOR -noupdate -expand -group "TEST MUXING" /cdc_unit_tb/DUT_INSTANCE/muxclk_out
add wave -itemcolor $CLK_NAME_COLOR -noupdate -expand -group "TEST MUXING" /cdc_unit_tb/DUT_INSTANCE/rst_n
add wave -itemcolor $MCLK_NAME_COLOR -color $MCLK_COLOR -noupdate -expand -group "TEST MUXING" /cdc_unit_tb/DUT_INSTANCE/mrst_n
add wave -itemcolor $MCLK_NAME_COLOR -color $MCLK_COLOR -noupdate -expand -group "TEST MUXING" /cdc_unit_tb/DUT_INSTANCE/muxrst_n_out

add wave -itemcolor $CLK_NAME_COLOR -noupdate -expand -group "RESET SYNC" /cdc_unit_tb/DUT_INSTANCE/rst_n
add wave -itemcolor $MCLK_NAME_COLOR -color $MCLK_COLOR -noupdate -expand -group "RESET SYNC" /cdc_unit_tb/DUT_INSTANCE/muxrst_n_out

add wave -itemcolor $CLK_NAME_COLOR -noupdate -expand -group "1-BIT SYNC" /cdc_unit_tb/DUT_INSTANCE/clk
add wave -itemcolor $CLK_NAME_COLOR -noupdate -expand -group "1-BIT SYNC" /cdc_unit_tb/DUT_INSTANCE/play_in
add wave -itemcolor $MCLK_NAME_COLOR -color $MCLK_COLOR -noupdate -expand -group "1-BIT SYNC" /cdc_unit_tb/DUT_INSTANCE/muxclk_out
add wave -itemcolor $MCLK_NAME_COLOR -color $MCLK_COLOR -noupdate -expand -group "1-BIT SYNC" /cdc_unit_tb/DUT_INSTANCE/play_out

add wave -itemcolor $MCLK_NAME_COLOR -color $MCLK_COLOR -noupdate -expand -group "PULSE SYNC" /cdc_unit_tb/DUT_INSTANCE/muxclk_out
add wave -itemcolor $MCLK_NAME_COLOR -color $MCLK_COLOR -noupdate -expand -group "PULSE SYNC" /cdc_unit_tb/DUT_INSTANCE/req_in
add wave -itemcolor $CLK_NAME_COLOR -noupdate -expand -group "PULSE SYNC" /cdc_unit_tb/DUT_INSTANCE/clk
add wave -itemcolor $CLK_NAME_COLOR -noupdate -expand -group "PULSE SYNC" /cdc_unit_tb/DUT_INSTANCE/req_out

add wave -itemcolor $CLK_NAME_COLOR -noupdate -expand -group "MULTIBIT SYNC" /cdc_unit_tb/DUT_INSTANCE/clk
add wave -itemcolor $CLK_NAME_COLOR -noupdate -expand -group "MULTIBIT SYNC" /cdc_unit_tb/DUT_INSTANCE/tick_in
add wave -itemcolor $CLK_NAME_COLOR -noupdate -expand -group "MULTIBIT SYNC" /cdc_unit_tb/DUT_INSTANCE/audio0_in
add wave -itemcolor $CLK_NAME_COLOR -noupdate -expand -group "MULTIBIT SYNC" /cdc_unit_tb/DUT_INSTANCE/audio1_in
add wave -itemcolor $MCLK_NAME_COLOR -color $MCLK_COLOR -noupdate -expand -group "MULTIBIT SYNC" /cdc_unit_tb/DUT_INSTANCE/muxclk_out
add wave -itemcolor $MCLK_NAME_COLOR -color $MCLK_COLOR -noupdate -expand -group "MULTIBIT SYNC" /cdc_unit_tb/DUT_INSTANCE/tick_out
add wave -itemcolor $MCLK_NAME_COLOR -color $MCLK_COLOR -noupdate -expand -group "MULTIBIT SYNC" /cdc_unit_tb/DUT_INSTANCE/audio0_out
add wave -itemcolor $MCLK_NAME_COLOR -color $MCLK_COLOR -noupdate -expand -group "MULTIBIT SYNC" /cdc_unit_tb/DUT_INSTANCE/audio1_out

foreach s [find signals -internal /*/DUT_INSTANCE/*] {
    add wave -group INTERNAL $s
}




if { [info exists VSIM_VISUALIZER ] } {
    add wave -noupdate -format analog-step /cdc_unit_tb/TEST/tmaxlatency
} else {
    add wave -noupdate -format analog-step -height 84 -max 400 /cdc_unit_tb/TEST/tmaxlatency    
}

if  { [llength [find instances -bydu cdc_unit_svamod] ] > 0 } {
    add wave -noupdate -divider {BLACKBOX ASSERTIONS}

    if { [info exists VSIM_VISUALIZER ] } {
	set mf [find blocks /cdc_unit_tb/DUT_INSTANCE/CHECKER_MODULE/mf_*]
	set af [find blocks /cdc_unit_tb/DUT_INSTANCE/CHECKER_MODULE/af_*]
	foreach i [concat $mf $af] {
	    set name [lindex $i 0]
	    add wave -noupdate $name
	}
    } else {
	add wave -nofilter Assertion /cdc_unit_tb/DUT_INSTANCE/CHECKER_MODULE/mf_*
	add wave -nofilter Assertion /cdc_unit_tb/DUT_INSTANCE/CHECKER_MODULE/af_*
    }
	add wave -noupdate /audioport_util_pkg::assertions_failed
}

configure wave -signalnamewidth 1
configure wave -datasetprefix 0

