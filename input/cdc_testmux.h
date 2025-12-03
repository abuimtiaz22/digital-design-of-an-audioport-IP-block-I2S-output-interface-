#ifndef cdc_testmux_h
#define cdc_testmux_h

#include "systemc_headers.h"
#include "audioport_defs.h"

#ifdef HLS_RTL

#else


SC_MODULE(cdc_testmux) {
public:
  sc_in<bool>  test_mode_in;
  sc_in<bool>  clk;  
  sc_in<bool>  rst_n;
  sc_in<bool>  mclk;    
  sc_in<bool>  mrst_n;
  sc_out<bool> muxclk;
  sc_out<bool> rsync_clk;
  sc_out<bool> muxrst_n;  

  SC_CTOR(cdc_testmux)
    {
      SC_METHOD(cdc_testmux_proc);
      sensitive << test_mode_in << clk << rst_n << mclk << mrst_n;
    }

  void cdc_testmux_proc()
  {
    if (test_mode_in.read()) {
      muxclk.write(clk.read());
      muxrst_n.write(rst_n.read());
      rsync_clk.write(clk.read());
    } else {
      muxclk.write(mclk.read());
      muxrst_n.write(mrst_n.read());
      rsync_clk.write(!mclk.read());
    }
    
  }
};

#endif
#endif
