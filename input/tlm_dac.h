#ifndef tlm_dac_h
#define tlm_dac_h

#include "systemc_headers.h"
#include <queue>

#include "audioport_defs.h"
#include "tlm_audioport_defs.h"



SC_MODULE(tlm_dac) {
public:
  sc_in_clk               sck;
  sc_in <bool>            sdo;
  sc_in <bool>            ws;
  sc_fifo_out < audio_data_t > i2s_fifo;

  void i2s_sipo();

  SC_CTOR(tlm_dac)
  {
    SC_CTHREAD(i2s_sipo, sck.pos());
  }

  sc_int <48>   srg;
  sc_uint <5>   lctr;
  sc_uint <5>   rctr;      
  audio_data_t i2s_sample;
};

#endif
