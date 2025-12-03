######################################################################
# control_unit.sdc: Timing Constraints File
######################################################################

# 1. Define clock period and clock edge times in ns

create_clock -name clk -period 13.0 clk

# 2. Define reset input timing wrt clock in ns

set_input_delay  -clock clk 0.0 rst_n

# 3. Define input external delays (arrival times) wrt clock in ns

set_input_delay -clock clk 1.625 PSEL
set_input_delay -clock clk 1.625 PENABLE
set_input_delay -clock clk 1.625 PWRITE
set_input_delay -clock clk 1.625 PADDR
set_input_delay -clock clk 1.625 PWDATA
set_input_delay -clock clk 1.625 req_in

# 4. Define output external delays (setup times) wrt clock in ns

set_output_delay -clock clk 1.625 PRDATA
set_output_delay -clock clk 1.625 PREADY
set_output_delay -clock clk 1.625 PSLVERR
set_output_delay -clock clk 1.625 irq_out
set_output_delay -clock clk 1.625 audio0_out
set_output_delay -clock clk 1.625 audio1_out
set_output_delay -clock clk 1.625 cfg_out
set_output_delay -clock clk 1.625 cfg_reg_out
set_output_delay -clock clk 1.625 level_out
set_output_delay -clock clk 1.625 level_reg_out
set_output_delay -clock clk 1.625 dsp_regs_out
set_output_delay -clock clk 1.625 clr_out   
set_output_delay -clock clk 1.625 tick_out
set_output_delay -clock clk 1.625 play_out

