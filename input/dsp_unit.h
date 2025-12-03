#ifndef dsp_unit_h
#define dsp_unit_h

// 1. 
#include "systemc_headers.h"
#include "audioport_defs.h"

#ifdef HLS_RTL
#include "dsp_unit_sc_foreign_module.h"
#else

// 2. 
SC_MODULE(dsp_unit) {

  // 3. 
    sc_in<bool>                        clk;
    sc_in<bool>                        rst_n;
    sc_in < sc_int<DATABITS> >         audio0_in;
    sc_in < sc_int<DATABITS> >         audio1_in;
    sc_in < bool >                     tick_in;
    sc_in < bool >                     cfg_in;
    sc_in < bool >                     clr_in;
    sc_in < bool >                     level_in;
    sc_in < sc_uint<32> >              cfg_reg_in;
    sc_in < sc_uint<32> >              level_reg_in;
    sc_in < sc_bv<DSP_REGISTERS*32> >  dsp_regs_in;
    sc_out < sc_int<DATABITS> >        audio0_out;
    sc_out < sc_int<DATABITS> >        audio1_out;
    sc_out < bool >                    tick_out;

    
// Filter accumulators using sc_bigint for precision handling
    sc_signal<sc_bigint<DATABITS + COEFFBITS + 10>> acc0_r;  // Left channel accumulator
    sc_signal<sc_bigint<DATABITS + COEFFBITS + 10>> acc1_r;  // Right channel accumulator

    // Mono mode processing accumulator
    sc_signal<sc_int<DATABITS + 1>> mono_sum_r;  // For mono channel averaging

    // Overflow protection flags
    sc_signal<bool> overflow0_r;
    sc_signal<bool> overflow1_r;

    
    // 4.   
    void dsp_proc();
    void regs_proc();
    void read_inputs(bool &tick, bool &clr, bool &filter_cfg, sc_uint<16> &level0, sc_uint<16> &level1,sc_int<DATABITS> &audio0, sc_int<DATABITS> &audio1);
    void write_outputs(sc_int<DATABITS> dsp0, sc_int<DATABITS> dsp1);

    SC_CTOR(dsp_unit) {

      SC_CTHREAD(dsp_proc, clk.pos());
      async_reset_signal_is(rst_n, false);
      
      SC_METHOD(regs_proc);
      sensitive << clk.pos() << rst_n.neg();
      dont_initialize(); // Prevent simulator from executing this during elaboration 
    }
    
    // 5.
 private:
    sc_signal < sc_int<32>  > dsp_regs_r[DSP_REGISTERS];
    sc_signal < sc_uint<16> > level0_r;
    sc_signal < sc_uint<16> > level1_r;
    sc_signal < bool >        filter_r;
    sc_int    < DATABITS >    data0_r[FILTER_TAPS];
    sc_int    < DATABITS >    data1_r[FILTER_TAPS];
    //To do: Declare member variables you need here

    
};


#endif

#endif
