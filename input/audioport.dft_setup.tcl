#################################################################################
# Scan Chain Setup File for audioport
#################################################################################

# Scan clock (rises at 45ns, falls at 55ns, test clock period is 100ns by default)
set_dft_signal -view existing_dft -type ScanClock -timing { 45 55 } -port clk

# Reset
set_dft_signal -view existing_dft -type Reset -port rst_n -active_state 0

# Test mode select input tied to low in test mode
set_dft_signal -view existing_dft -type Constant -port test_mode_in -active_state 1

# Unused clock input mclk tied to low in test mode
set_dft_signal -view existing_dft -type Constant -port mclk -active_state 0

# Scan enable input    
set_dft_signal -view spec -type ScanEnable -port scan_en_in -active_state 1

# Settings for two scan paths
set_scan_configuration -style multiplexed_flip_flop \
                       -chain_count 2 \
                       -clock_mixing mix_clocks 

# Scan path inputs and outputs
set_dft_signal -view spec -type ScanDataIn  -port "PADDR[0]"
set_dft_signal -view spec -type ScanDataOut -port "PRDATA[0]"

set_dft_signal -view spec -type ScanDataIn  -port "PADDR[1]"
set_dft_signal -view spec -type ScanDataOut -port "PRDATA[1]"

