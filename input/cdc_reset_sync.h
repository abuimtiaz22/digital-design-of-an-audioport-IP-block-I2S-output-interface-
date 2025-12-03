#ifndef cdc_reset_sync_h
#define cdc_reset_sync_h

#include "systemc_headers.h"
#include "audioport_defs.h"

#ifdef HLS_RTL

#else

SC_MODULE(cdc_reset_sync) {
public:
  sc_in<bool>              clk;
  sc_in<bool>              rst_n;
  sc_out<bool>             mrst_n;

  sc_signal<bool> rst_sff1;

  SC_CTOR(cdc_reset_sync)
    {
      SC_METHOD(reset_sync_proc);
      sensitive << clk.pos() << rst_n.neg();
    }

  void reset_sync_proc()
  {
    if(!rst_n.read()) {
      rst_sff1.write(0);
      mrst_n.write(0);
    } else {
      rst_sff1.write(1);
      mrst_n.write(rst_sff1.read());
    }
  }
  

};

#endif
#endif
