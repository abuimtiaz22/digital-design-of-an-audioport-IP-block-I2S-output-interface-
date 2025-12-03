##########################################################################
# dsp_unit.sdc: Timing Constraints File
##########################################################################

# 1. Define clock period and clock edge times in ns

create_clock -name clk -period 10.0 clk

# 2. Define reset input timing wrt clock in ns

set_input_delay  -clock clk 0.0 rst_n

# 3. Define input external delays (arrival times) wrt clock in ns

set_input_delay  -clock clk 0.0 [all_inputs]

# 4. Define output external delays (setup times) wrt clock in ns

set_output_delay  -clock clk 0.0 [all_outputs]
