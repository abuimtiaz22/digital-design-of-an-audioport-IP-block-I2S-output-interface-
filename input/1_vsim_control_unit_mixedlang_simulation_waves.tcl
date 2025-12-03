onerror {add wave -noupdate -divider {Wave setup error, check variable names!}; resume}
configure wave -signalnamewidth 1
configure wave -datasetprefix 0
configure wave -timelineunits ns
add wave -noupdate /control_unit_tb/DUT_INSTANCE/clk
add wave -noupdate /control_unit_tb/DUT_INSTANCE/rst_n
add wave -noupdate /control_unit_tb/DUT_INSTANCE/PSEL
add wave -noupdate /control_unit_tb/DUT_INSTANCE/PENABLE
add wave -noupdate /control_unit_tb/DUT_INSTANCE/PWRITE
add wave -noupdate /control_unit_tb/DUT_INSTANCE/PREADY
add wave -noupdate /control_unit_tb/DUT_INSTANCE/PADDR
add wave -noupdate /control_unit_tb/DUT_INSTANCE/PWDATA
add wave -noupdate /control_unit_tb/DUT_INSTANCE/PRDATA
add wave -noupdate /control_unit_tb/DUT_INSTANCE/PSLVERR
add wave -noupdate /control_unit_tb/DUT_INSTANCE/req_in
add wave -noupdate /control_unit_tb/DUT_INSTANCE/irq_out
add wave -noupdate /control_unit_tb/DUT_INSTANCE/cfg_reg_out
add wave -noupdate /control_unit_tb/DUT_INSTANCE/level_reg_out
add wave -noupdate /control_unit_tb/DUT_INSTANCE/dsp_regs_out
add wave -noupdate /control_unit_tb/DUT_INSTANCE/clr_out
add wave -noupdate /control_unit_tb/DUT_INSTANCE/cfg_out
add wave -noupdate /control_unit_tb/DUT_INSTANCE/level_out
add wave -noupdate /control_unit_tb/DUT_INSTANCE/play_out
add wave -noupdate /control_unit_tb/DUT_INSTANCE/tick_out
add wave -noupdate /control_unit_tb/DUT_INSTANCE/audio0_out
add wave -noupdate /control_unit_tb/DUT_INSTANCE/audio1_out
add wave -noupdate -divider INTERNAL
add wave -noupdate /control_unit_tb/DUT_INSTANCE/rindex
add wave -noupdate /control_unit_tb/DUT_INSTANCE/apbwrite
add wave -noupdate /control_unit_tb/DUT_INSTANCE/apbread
add wave -noupdate /control_unit_tb/DUT_INSTANCE/rbank_r
add wave -noupdate /control_unit_tb/DUT_INSTANCE/play_r
add wave -noupdate /control_unit_tb/DUT_INSTANCE/req_r
add wave -noupdate /control_unit_tb/DUT_INSTANCE/irq_r
add wave -noupdate /control_unit_tb/DUT_INSTANCE/ldata_r
add wave -noupdate /control_unit_tb/DUT_INSTANCE/lhead_r
add wave -noupdate /control_unit_tb/DUT_INSTANCE/ltail_r
add wave -noupdate /control_unit_tb/DUT_INSTANCE/llooped_r
add wave -noupdate /control_unit_tb/DUT_INSTANCE/rdata_r
add wave -noupdate /control_unit_tb/DUT_INSTANCE/rhead_r
add wave -noupdate /control_unit_tb/DUT_INSTANCE/rtail_r
add wave -noupdate /control_unit_tb/DUT_INSTANCE/rlooped_r
add wave -noupdate /control_unit_tb/DUT_INSTANCE/lfifo
add wave -noupdate /control_unit_tb/DUT_INSTANCE/rfifo
add wave -noupdate /control_unit_tb/DUT_INSTANCE/lempty
add wave -noupdate /control_unit_tb/DUT_INSTANCE/rempty
add wave -noupdate /control_unit_tb/DUT_INSTANCE/start
add wave -noupdate /control_unit_tb/DUT_INSTANCE/stop
add wave -noupdate /control_unit_tb/DUT_INSTANCE/clr
add wave -noupdate /control_unit_tb/DUT_INSTANCE/irqack

add wave -noupdate -divider TEST_PROGRAM
add wave -noupdate /control_unit_tb/TEST/*

if  { [llength [find instances -bydu control_unit_svamod] ] > 0 } {
    add wave -noupdate -divider {BLACKBOX ASSERTIONS}
    add wave -nofilter Assertion /control_unit_tb/DUT_INSTANCE/CHECKER_MODULE/af_*
}
add wave -noupdate /audioport_util_pkg::assertions_failed
TreeUpdate [SetDefaultTree]
update

