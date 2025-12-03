#ifndef i2s_unit_h
#define i2s_unit_h

#include "systemc_headers.h"
#include "audioport_defs.h"

#ifdef HLS_RTL
#include "i2s_unit_sc_foreign_module.h"
#else

SC_MODULE(i2s_unit) {
 public:
  sc_in_clk              clk;
  sc_in<bool>            rst_n;
  sc_in<bool>            play_in;
  sc_in<bool>            tick_in;
  sc_in < sc_int<24> >   audio0_in;
  sc_in < sc_int<24> >   audio1_in;
  sc_out<bool>            req_out;
  sc_out<bool>            ws_out;
  sc_out<bool>            sck_out;
  sc_out<bool>            sdo_out;
  
  void proc();
  
  SC_CTOR(i2s_unit) {
    SC_CTHREAD(proc, clk.pos());
    async_reset_signal_is(rst_n, false);
  }
    
  sc_uint<3>   state_r;
  sc_uint<48>  inreg_r;
  sc_uint<48>  srg_r;
  sc_uint<9>   ctr_r;
};


#endif

#endif
