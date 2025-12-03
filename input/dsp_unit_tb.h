#ifndef dsp_unit_tb_h
#define dsp_unit_tb_h

#include "systemc_headers.h"
#include "audioport_defs.h"
#include <queue>

SC_MODULE(dsp_unit_tb) {
public:
    sc_in<bool>                        clk;
    sc_in<bool>                        rst_n;
    sc_out < sc_int<DATABITS> >        audio0_in;
    sc_out < sc_int<DATABITS> >        audio1_in;
    sc_out < bool >                    tick_in;
    sc_out < bool >                    cfg_in;
    sc_out < bool >                    clr_in;
    sc_out < bool >                    level_in;
    sc_out  < sc_uint<32> >            cfg_reg_in;
    sc_out  < sc_uint<32> >            level_reg_in;
    sc_out < sc_bv<DSP_REGISTERS*32> > dsp_regs_in;
    sc_in < sc_int<DATABITS> >         audio0_out;
    sc_in < sc_int<DATABITS> >         audio1_out;
    sc_in < bool >                     tick_out;
    
    void tx();
    void rx();
    int read_filter_taps();
    
    SC_CTOR(dsp_unit_tb) 
    {
      SC_CTHREAD(tx, clk.pos());
      reset_signal_is(rst_n, false);
      SC_CTHREAD(rx, clk.pos());
      reset_signal_is(rst_n, false);
    }
    
    sc_int<DATABITS> inputs[2];
    sc_int<DATABITS> outputs[2];
    sc_int<32> filter_taps[4*FILTER_TAPS];

    std::queue<sc_time> start_times;
    std::queue< sc_int<DATABITS> > input_samples[2];
    int sample_number;
    int latency_sum;
    int latency;
    int max_latency;
};


#endif
