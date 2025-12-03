onerror {add wave -noupdate -divider {Wave setup error!}; resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /cdc_unit_tb/DUT_INSTANCE/clk
add wave -noupdate /cdc_unit_tb/DUT_INSTANCE/rst_n
add wave -noupdate /cdc_unit_tb/DUT_INSTANCE/mclk
add wave -noupdate -expand -group testmux /cdc_unit_tb/DUT_INSTANCE/test_mode_in
add wave -noupdate -expand -group testmux /cdc_unit_tb/DUT_INSTANCE/muxclk_out
add wave -noupdate -expand -group testmux /cdc_unit_tb/DUT_INSTANCE/muxrst_n_out

add wave -noupdate -expand -group reset_sync /cdc_unit_tb/DUT_INSTANCE/muxclk_out
add wave -noupdate -expand -group reset_sync /cdc_unit_tb/DUT_INSTANCE/rst_n
add wave -noupdate -expand -group reset_sync /cdc_unit_tb/DUT_INSTANCE/muxrst_n_out

add wave -noupdate -expand -group play_sync /cdc_unit_tb/DUT_INSTANCE/muxclk_out
add wave -noupdate -expand -group play_sync /cdc_unit_tb/DUT_INSTANCE/play_in
add wave -noupdate -expand -group play_sync /cdc_unit_tb/DUT_INSTANCE/play_out

add wave -noupdate -expand -group req_sync /cdc_unit_tb/DUT_INSTANCE/clk
add wave -noupdate -expand -group req_sync /cdc_unit_tb/DUT_INSTANCE/req_in
add wave -noupdate -expand -group req_sync /cdc_unit_tb/DUT_INSTANCE/req_out

add wave -noupdate -expand -group audio_sync /cdc_unit_tb/DUT_INSTANCE/muxclk_out
add wave -noupdate -expand -group audio_sync /cdc_unit_tb/DUT_INSTANCE/tick_in
add wave -noupdate -expand -group audio_sync /cdc_unit_tb/DUT_INSTANCE/audio0_in
add wave -noupdate -expand -group audio_sync /cdc_unit_tb/DUT_INSTANCE/audio1_in
add wave -noupdate -expand -group audio_sync /cdc_unit_tb/DUT_INSTANCE/tick_out
add wave -noupdate -expand -group audio_sync /cdc_unit_tb/DUT_INSTANCE/audio0_out
add wave -noupdate -expand -group audio_sync /cdc_unit_tb/DUT_INSTANCE/audio1_out

if  { [llength [find instances -bydu cdc_unit_svamod] ] > 0 } {
    add wave -noupdate -divider {BLACKBOX ASSERTIONS}
    add wave -nofilter Assertion /cdc_unit_tb/DUT_INSTANCE/CHECKER_MODULE/mf_*
    add wave -nofilter Assertion /cdc_unit_tb/DUT_INSTANCE/CHECKER_MODULE/af_*
#    add wave -noupdate -divider {WHITEBOX ASSERTIONS}
#    add wave -nofilter Assertion /cdc_unit_tb/DUT_INSTANCE/CHECKER_MODULE/ar_*
    add wave -noupdate /audioport_util_pkg::assertions_failed
}

configure wave -signalnamewidth 1
configure wave -datasetprefix 0
