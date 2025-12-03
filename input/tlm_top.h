#ifndef tlm_top_h
#define tlm_top_h

#define SC_INCLUDE_DYNAMIC_PROCESSES

#define SC_INCLUDE_FX
#include <systemc.h>

sc_event scoreboard_reset;

#include "audioport_defs.h"
#include "tlm_audioport_defs.h"
#include "tlm_audioport.h"
#include "tlm_cpu.h"
#include "tlm_dac.h"
#include "tlm_scoreboard.h"

SC_MODULE(tlm_top) {
public:
  
  sc_signal < bool >         irq_out;
  sc_signal <bool>           sdo_out;
  sc_signal <bool>           ws_out;
  sc_signal <bool>           sck_out;
  sc_fifo < audio_data_t >   audio_fifo;
  sc_fifo < audio_data_t >   i2s_fifo;

  tlm_audioport              tlm_audioport_inst;
  tlm_cpu                    tlm_cpu_inst;
  tlm_dac                    tlm_dac_inst;
  tlm_scoreboard             tlm_scoreboard_inst;

  SC_CTOR(tlm_top) : 
    audio_fifo(AUDIO_FIFO_SIZE),
    i2s_fifo(AUDIO_FIFO_SIZE),
    tlm_audioport_inst("tlm_audioport_inst"),
    tlm_cpu_inst("tlm_cpu_inst"),
    tlm_dac_inst("tlm_dac_inst"),
    tlm_scoreboard_inst("tlm_scoreboard_inst")
  {

    tlm_audioport_inst.irq_out     ( irq_out );
    tlm_audioport_inst.sdo_out     ( sdo_out );
    tlm_audioport_inst.ws_out      ( ws_out );
    tlm_audioport_inst.sck_out     ( sck_out );
    
    tlm_cpu_inst.irq_out           ( irq_out );
    tlm_cpu_inst.audio_fifo        ( audio_fifo );
    tlm_cpu_inst.socket.bind       ( tlm_audioport_inst.socket );

    tlm_dac_inst.sck               ( sck_out );
    tlm_dac_inst.sdo               ( sdo_out );
    tlm_dac_inst.ws                ( ws_out );
    tlm_dac_inst.i2s_fifo          ( i2s_fifo );

    tlm_scoreboard_inst.audio_fifo ( audio_fifo );
    tlm_scoreboard_inst.i2s_fifo   ( i2s_fifo );
  }
    
};

#endif
