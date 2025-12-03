#!/bin/bash
#
# This script shows a stereo audio data series file as waveforms 
# using gnuplot.
# The data are assumed to be organized in columns, with the first
# column containing the time value and the reset of the columns
# the data values. The first half of the data columns represent
# input data as stereo channels, and the second hald output data.

echo "Press any key to kill gnuplot windows..."
sleep 1

# Data file given as command line argument:
filename="results/audioport_uvm_comparator_out.txt"

# Count number of channels from number of columns
columns=`awk '{ print NF}' $filename | head -1`
let channels=($columns-1)

# Find out screen size
screenw=`xrandr | grep current | sed s/,//g | awk '{print $8}'`
screenh=`xrandr | grep current | sed s/,//g | awk '{print $10}'`

# Calculate graph window dimensions
let dx=$screenw
let wt=($dx-20)
let dy=$screenh/4
let ht=($dy-40)

# Calculate L+R input and output data column indices
let li=2
let ri=3
let lo=4
let ro=5
# Window x coordinate of channel
let x=10
# Plot L+R input and output data
let y=20
gnuplot  -geometry ${wt}x${ht}+${x}+${y} -persist  -e "set terminal x11 title \"DUT[LEFT]\"; set style line 1 lc rgb \"green\"; set style data lines; plot \"${filename}\" using 1:${li} ls 1; pause -1" &
let y=20+${dy}
gnuplot  -geometry ${wt}x${ht}+${x}+${y} -persist -e "set terminal x11 title \"DUT[RIGHT]\"; set style line 1 lc rgb \"green\"; set style data lines; plot \"${filename}\" using 1:${ri} ls 1; pause -1" &
let y=20+2*${dy}
gnuplot  -geometry ${wt}x${ht}+${x}+${y} -persist -e "set terminal x11 title \"REF[LEFT]\"; set style line 1 lc rgb \"red\"; set style data lines; plot \"${filename}\" using 1:${lo} ls 1; pause -1" &
let y=20+3*${dy}
gnuplot  -geometry ${wt}x${ht}+${x}+${y} -persist -e "set terminal x11 title \"REF[RIGHT]\"; set style line 1 lc rgb \"red\"; set style data lines; plot \"${filename}\" using 1:${ro} ls 1; pause -1" &



read -n 1
killall gnuplot_x11
