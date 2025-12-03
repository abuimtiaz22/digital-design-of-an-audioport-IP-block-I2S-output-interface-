#ifndef cdc_2ff_sync_h
#define cdc_2ff_sync_h

#include "systemc_headers.h"
#include "audioport_defs.h"

#ifdef HLS_RTL
#include "cdc_2ff_sync_sc_foreign_module.h"
#else

SC_MODULE(cdc_2ff_sync) {
public:
    sc_in_clk                   clk;
    sc_in<bool>                 rst_n;
    sc_in<bool>                 bit_in;
    sc_out<bool>                bit_out;

    sc_signal<bool>             ff1;

    void sync_regs()
    {
      if (rst_n.read() == 0)
	{
	  ff1 = 0;
	  bit_out = 0;
	}
      else
	{
	  ff1 = bit_in;
	  bit_out = ff1;
	}
    }
    
    
    SC_CTOR(cdc_2ff_sync) {
      
      SC_METHOD(sync_regs);
      sensitive << clk.pos() << rst_n.neg();
      dont_initialize();

    }

};


#endif
#endif
