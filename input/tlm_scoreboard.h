#ifndef tlm_scoreboard_h
#define tlm_scoreboard_h

#include "systemc_headers.h"
#include "audioport_defs.h"
#include "tlm_audioport_defs.h"

#include <queue>

SC_MODULE(tlm_scoreboard) {
public:
  sc_fifo_in < audio_data_t >   audio_fifo;
  sc_fifo_in < audio_data_t >   i2s_fifo;
  
  void thread();
  void clear();
  
  SC_CTOR(tlm_scoreboard)
  {
    SC_THREAD(thread);
    SC_THREAD(clear);

  }
  
  int sample_number;
  audio_data_t audio_in;
  audio_data_t audio_out;

};

#endif
