#ifndef cdc_pulse_sync_h
#define cdc_pulse_sync_h

#include "systemc_headers.h"
#include "audioport_defs.h"

#ifdef HLS_RTL
#include "cdc_pulse_sync_sc_foreign_module.h"
#else


SC_MODULE(cdc_pulse_sync) {
public:
    sc_in_clk                   clk;
    sc_in<bool>                 rst_n;
    sc_in<bool>                 bit_in;
    sc_out<bool>                bit_out;

    sc_signal<bool>             ff1;
    sc_signal<bool>             ff2;
    sc_signal<bool>             ff3;

    void sync_regs()
    {
      if (rst_n.read() == 0)
	{
	  ff1 = 0;
	  ff2 = 0;
	  ff3 = 0;
	}
      else
	{
	  ff1 = bit_in;
	  ff2 = ff1;
	  ff3 = ff2;
	}
    }
    
    void sync_logic()
    {
      if (ff3 == 0 && ff2 == 1)
	  bit_out = 1;
	else
	  bit_out = 0;	  
    }
    
    
    SC_CTOR(cdc_pulse_sync) {
      
      SC_METHOD(sync_regs);
      sensitive << clk.pos() << rst_n.neg();
      dont_initialize();

      SC_METHOD(sync_logic);
      sensitive << ff2 << ff3;
      dont_initialize();
    }

};


#endif
#endif
