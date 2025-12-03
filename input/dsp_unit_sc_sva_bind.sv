// Binding of SVA module to HLS generated RTL module

`ifdef HLS_RTL
bind dsp_unit_rtl dsp_unit_svamod CHECKER_MODULE (.*);
`else
bind dsp_unit dsp_unit_svamod CHECKER_MODULE (.*);
`endif
  
