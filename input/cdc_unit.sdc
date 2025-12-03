######################################################################################
# cdc_unit.sdc: Timing Constraints File
#####################################################################################

# 1. Define clock period and clock edge times in ns

create_clock -name clk  -period 13.0 clk
create_clock -name mclk -period 54.2 mclk

set_clock_groups -asynchronous -name cdc_unit_clk_domains -group clk -group mclk

# 2. Define reset input delay relative to clock clk in ns
set_input_delay  -clock clk 1.625 rst_n

# 3. Define data input external delays

set_input_delay  -clock clk 1.625 test_mode_in
set_input_delay  -clock clk 1.625 audio0_in
set_input_delay  -clock clk 1.625 audio1_in
set_input_delay  -clock clk 1.625 play_in
set_input_delay  -clock clk 1.625 tick_in

set_input_delay  -clock mclk 6.775 req_in

# 4. Define output external delays relative to clock mclk in ns

set_output_delay  -clock mclk 6.775 audio0_out
set_output_delay  -clock mclk 6.775 audio1_out
set_output_delay  -clock mclk 6.775 tick_out
set_output_delay  -clock mclk 6.775 play_out 

set_output_delay  -clock clk 1.625 req_out

# 5. Run analysis in normal mode
set_case_analysis 0 test_mode_in