##############################################
# audioport.sdc: Timing Constraints File
##############################################

##############################################
# clk clock domain
##############################################

# 1. Define clock period and clock edge times in ns

create_clock -name clk -period 17.5 clk

set_clock_latency  0. clk
set_clock_uncertainty 0.0 clk

# 2. Define reset input timing w.r.t. clock in ns

set_input_delay  -clock clk 8.25 rst_n

# 3. Define input external delays (arrival times) wrt clock in ns

set_input_delay -clock clk 5.0 PSEL
set_input_delay -clock clk 5.0 PENABLE
set_input_delay -clock clk 5.0 PWRITE
set_input_delay -clock clk 5.0 PADDR
set_input_delay -clock clk 5.0 PWDATA
set_input_delay -clock clk 5.0 test_mode_in
set_input_delay -clock clk 5.0 scan_en_in

# 4. Define output external delays (setup times) wrt clock in ns

set_output_delay -clock clk 5.0 PRDATA
set_output_delay -clock clk 5.0 PREADY
set_output_delay -clock clk 5.0 PSLVERR
set_output_delay -clock clk 5.0 irq_out

##############################################
# mclk clock domain
##############################################

# 1. Define clock period and clock edge times in ns

create_clock -name mclk -period 54.25 mclk

# 2. Define input external delays (arrival times) wrt clock in ns

# 3. Define output external delays (setup times) wrt clock in ns

set_output_delay -clock mclk 0.0 ws_out
set_output_delay -clock mclk 0.0 sck_out
set_output_delay -clock mclk 0.0 sdo_out

set_clock_groups -asynchronous -name audioport_clk_domains -group clk -group mclk

##############################################
# Input drives and output loads
##############################################

set_load 0.2 [all_outputs]

##############################################
# Timing Exceptions
##############################################

#set_case_analysis 0 scan_en_in
#set_case_analysis 0 test_mode_in
