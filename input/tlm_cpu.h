#ifndef tlm_cpu_h
#define tlm_cpu_h

#define SC_INCLUDE_DYNAMIC_PROCESSES
#define SC_INCLUDE_FX
#include <systemc.h>
#include "tlm.h"
#include "tlm_utils/simple_initiator_socket.h"
using namespace sc_core;
using namespace sc_dt;
using namespace std;

#include <queue>

#include "audioport_defs.h"
#include "tlm_audioport_defs.h"

SC_MODULE(tlm_cpu) {

  tlm_utils::simple_initiator_socket<tlm_cpu> socket;   // TLM-2 socket, defaults to 32-bits wide, base protocol
  sc_in < bool >                              irq_out;
  sc_fifo_out < audio_data_t >                audio_fifo;


  tlm::tlm_generic_payload*   tlm_tx;
  tlm::tlm_command            tlm_cmd;
  tlm::tlm_response_status    tlm_status;
  unsigned int                tlm_buffer;

  int 		test_number;

  void       test_program();
  void       bus_write(sc_uint<32> addr, sc_uint<32> wdata, bool &fail);
  void       bus_read(sc_uint<32>  addr, sc_uint<32> &rdata, bool &fail);
  void       irq_handler();
  sc_int<24> square_generator();
  sc_int<24> sine_generator();
  int        read_filter_taps();

  SC_CTOR(tlm_cpu)
    : socket("socket")
  {
    SC_THREAD(test_program);
    tlm_tx = new tlm::tlm_generic_payload;  
  }

  sc_int<32>  filter_taps[4*FILTER_TAPS];
  int         phase_accu;
  audio_data_t audio_sample;
};


#endif
