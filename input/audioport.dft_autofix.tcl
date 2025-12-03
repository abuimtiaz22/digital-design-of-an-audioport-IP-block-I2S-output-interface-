if { $EDA_TOOL == "Design-Compiler" } {

    # Define clock port as test data used for fixing
    set_dft_signal -view spec -type TestData -port clk

    # Enable fixing of uncontrollable clock, reset and set pins of flip-flops
    set_dft_configuration     -fix_clock enable
    set_dft_configuration     -fix_reset enable
    set_dft_configuration     -fix_set   enable

    # Chose OR-gate based solution
    set_autofix_configuration -type clock -control_signal test_mode_in
    set_autofix_configuration -type set   -control_signal test_mode_in
    set_autofix_configuration -type reset -control_signal test_mode_in

} 

if { $EDA_TOOL == "Genus" } {

    fix_dft_violations -test_control test_mode_in -async_set -async_reset

}
