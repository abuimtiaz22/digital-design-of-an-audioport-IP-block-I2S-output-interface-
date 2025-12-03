onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/clk
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/rst_n
add wave -noupdate -radix decimal /sc_main/dsp_unit_top_inst/dsp_unit_tb_inst/sample_number
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/cfg_in
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/level_in
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/clr_in
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/tick_in
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/cfg_reg_in
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/dsp_regs_in
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/level_reg_in
add wave -noupdate -format Analog-Step -height 84 -max 8388610.0 -min -8388610.0 -radix decimal /sc_main/dsp_unit_top_inst/dsp_unit_inst/audio0_in
add wave -noupdate -format Analog-Step -height 84 -max 8388610.0 -min -8388610.0 -radix decimal /sc_main/dsp_unit_top_inst/dsp_unit_inst/audio1_in
add wave -noupdate -format Analog-Step -height 84 -max 8388610.0 -min -8388610.0 -radix decimal /sc_main/dsp_unit_top_inst/dsp_unit_inst/audio0_out
add wave -noupdate -format Analog-Step -height 84 -max 8388610.0 -min -8388610.0 -radix decimal /sc_main/dsp_unit_top_inst/dsp_unit_inst/audio1_out
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/valid_out
add wave -noupdate -divider {Latency Check:}
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/clk
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/tick_in
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/clr_in
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/valid_out
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_tb_inst/latency
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {5549570000 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 111
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits us
update
WaveRestoreZoom {0 ps} {67207893375 ps}
