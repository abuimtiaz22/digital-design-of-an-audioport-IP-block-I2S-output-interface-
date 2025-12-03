if { $EDA_TOOL == "Design-Compiler" } {
    set_ungroup control_unit_1 false
    set_ungroup dsp_unit_1     false
    set_ungroup i2s_unit_1     false
    set_ungroup cdc_unit_1     false
}

if { $EDA_TOOL == "Genus" } {
    set_db [vfind / -hinst control_unit_1] .ungroup_ok false
    set_db [vfind / -hinst dsp_unit_1]     .ungroup_ok false
    set_db [vfind / -hinst cdc_unit_1]     .ungroup_ok false
    set_db [vfind / -hinst i2s_unit_1]     .ungroup_ok false
}
