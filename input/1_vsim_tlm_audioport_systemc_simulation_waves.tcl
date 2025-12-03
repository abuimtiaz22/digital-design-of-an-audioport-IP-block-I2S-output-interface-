onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /sc_main/tlm_top_inst/tlm_cpu_inst/test_number

add wave -noupdate -expand -group {AUDIO IN/OUT} -radix decimal -childformat {{/sc_main/tlm_top_inst/tlm_scoreboard_inst/audio_in.left -radix decimal} {/sc_main/tlm_top_inst/tlm_scoreboard_inst/audio_in.right -radix decimal}} -expand -subitemconfig {/sc_main/tlm_top_inst/tlm_scoreboard_inst/audio_in.left {-format Analog-Step -height 64 -max 8388610.0 -min -8388610.0 -radix decimal} /sc_main/tlm_top_inst/tlm_scoreboard_inst/audio_in.right {-format Analog-Step -height 64 -max 8388610.0 -min -8388610.0 -radix decimal}} /sc_main/tlm_top_inst/tlm_scoreboard_inst/audio_in
add wave -noupdate -expand -group {AUDIO IN/OUT} -radix decimal -childformat {{/sc_main/tlm_top_inst/tlm_scoreboard_inst/audio_out.left -radix decimal} {/sc_main/tlm_top_inst/tlm_scoreboard_inst/audio_out.right -radix decimal}} -expand -subitemconfig {/sc_main/tlm_top_inst/tlm_scoreboard_inst/audio_out.left {-format Analog-Step -height 64 -max 8388610.0 -min -8388610.0 -radix decimal} /sc_main/tlm_top_inst/tlm_scoreboard_inst/audio_out.right {-format Analog-Step -height 64 -max 8388610.0 -min -8388610.0 -radix decimal}} /sc_main/tlm_top_inst/tlm_scoreboard_inst/audio_out

add wave -noupdate -expand -group {TLM BUS INPUT} /sc_main/tlm_top_inst/tlm_cpu_inst/tlm_cmd
add wave -noupdate -expand -group {TLM BUS INPUT} /sc_main/tlm_top_inst/tlm_audioport_inst/tlm_addr
add wave -noupdate -expand -group {TLM BUS INPUT} /sc_main/tlm_top_inst/tlm_audioport_inst/tlm_data
add wave -noupdate -expand -group {TLM BUS INPUT} /sc_main/tlm_top_inst/tlm_cpu_inst/tlm_status

add wave -noupdate -expand /sc_main/tlm_top_inst/tlm_audioport_inst/irq_out

add wave -noupdate -expand -group {I2S OUTPUT} /sc_main/tlm_top_inst/tlm_audioport_inst/sck_out
add wave -noupdate -expand -group {I2S OUTPUT} /sc_main/tlm_top_inst/tlm_audioport_inst/ws_out
add wave -noupdate -expand -group {I2S OUTPUT} /sc_main/tlm_top_inst/tlm_audioport_inst/sdo_out

add wave -noupdate -divider {INTERNAL}

add wave -noupdate -expand -group {REGISTER INTERFACE} /sc_main/tlm_top_inst/tlm_audioport_inst/rbank_r(0)
add wave -noupdate -expand -group {REGISTER INTERFACE} /sc_main/tlm_top_inst/tlm_audioport_inst/rbank_r(1)
add wave -noupdate -expand -group {REGISTER INTERFACE} /sc_main/tlm_top_inst/tlm_audioport_inst/rbank_r(2)
add wave -noupdate -expand -group {REGISTER INTERFACE} /sc_main/tlm_top_inst/tlm_audioport_inst/rbank_r(3)
add wave -noupdate -expand -group {REGISTER INTERFACE} /sc_main/tlm_top_inst/tlm_audioport_inst/rbank_r
add wave -noupdate -expand -group {REGISTER INTERFACE} /sc_main/tlm_top_inst/tlm_audioport_inst/lfifo
add wave -noupdate -expand -group {REGISTER INTERFACE} /sc_main/tlm_top_inst/tlm_audioport_inst/rfifo

add wave -noupdate -expand -group {PLAYBACK CONTROL} /sc_main/tlm_top_inst/tlm_audioport_inst/play_mode
add wave -noupdate -expand -group {PLAYBACK CONTROL} /sc_main/tlm_top_inst/tlm_audioport_inst/req
add wave -noupdate -expand -group {PLAYBACK CONTROL} /sc_main/tlm_top_inst/tlm_audioport_inst/tick
add wave -noupdate -expand -group {PLAYBACK CONTROL} /sc_main/tlm_top_inst/tlm_audioport_inst/active_config_data
add wave -noupdate -expand -group {PLAYBACK CONTROL} /sc_main/tlm_top_inst/tlm_audioport_inst/active_level_data
add wave -noupdate -expand -group {PLAYBACK CONTROL} /sc_main/tlm_top_inst/tlm_audioport_inst/active_dsp_regs
add wave -noupdate -expand -group {PLAYBACK CONTROL} /sc_main/tlm_top_inst/tlm_audioport_inst/i2s_state

add wave -noupdate -expand -group DSP -childformat {{/sc_main/tlm_top_inst/tlm_audioport_inst/dsp_inputs(0) -radix decimal} {/sc_main/tlm_top_inst/tlm_audioport_inst/dsp_inputs(1) -radix decimal}} -expand -subitemconfig {/sc_main/tlm_top_inst/tlm_audioport_inst/dsp_inputs(0) {-format Analog-Step -height 16 -max 8388607.0 -min -8388607.0 -radix decimal} /sc_main/tlm_top_inst/tlm_audioport_inst/dsp_inputs(1) {-format Analog-Step -height 16 -max 8388607.0 -min -8388607.0 -radix decimal}} /sc_main/tlm_top_inst/tlm_audioport_inst/dsp_inputs
add wave -noupdate -expand -group DSP -childformat {{/sc_main/tlm_top_inst/tlm_audioport_inst/filter_outputs(0) -radix decimal} {/sc_main/tlm_top_inst/tlm_audioport_inst/filter_outputs(1) -radix decimal}} -expand -subitemconfig {/sc_main/tlm_top_inst/tlm_audioport_inst/filter_outputs(0) {-format Analog-Step -height 16 -max 8388607.0 -min -8388607.0 -radix decimal} /sc_main/tlm_top_inst/tlm_audioport_inst/filter_outputs(1) {-format Analog-Step -height 16 -max 8388607.0 -min -8388607.0 -radix decimal}} /sc_main/tlm_top_inst/tlm_audioport_inst/filter_outputs
add wave -noupdate -expand -group DSP -childformat {{/sc_main/tlm_top_inst/tlm_audioport_inst/dsp_outputs(0) -radix decimal} {/sc_main/tlm_top_inst/tlm_audioport_inst/dsp_outputs(1) -radix decimal}} -expand -subitemconfig {/sc_main/tlm_top_inst/tlm_audioport_inst/dsp_outputs(0) {-format Analog-Step -height 16 -max 8388607.0 -min -8388607.0 -radix decimal} /sc_main/tlm_top_inst/tlm_audioport_inst/dsp_outputs(1) {-format Analog-Step -height 16 -max 8388607.0 -min -8388607.0 -radix decimal}} /sc_main/tlm_top_inst/tlm_audioport_inst/dsp_outputs

configure wave -signalnamewidth 1 
configure wave -datasetprefix 0

update
wave zoom full

proc T1 {} {
    wave zoom range 0 5000ns
}

proc T2 {} {
    wave zoom range 4900ns 12100ns
}

proc T3 {} {
    wave zoom range  12000ns 12220ns
}

proc T4 {} {
    wave zoom range  12200ns 12350ns
}

proc T5_1 {} {
    wave zoom range  12350ns 2072055ns
}

proc T5_2 {} {
    wave zoom range  2072050 4131810ns
}

proc T5_3 {} {
    wave zoom range  4131800ns 6191500ns
}

proc T5_4 {} {
    wave zoom range 6191450ns 8251350ns
}

proc T5_5 {} {
    wave zoom range 8251330ns 10311170ns
}

