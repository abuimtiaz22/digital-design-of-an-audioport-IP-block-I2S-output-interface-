#ifndef cdc_unit_h
#define cdc_unit_h

#include "systemc_headers.h"
#include "audioport_defs.h"

#ifdef HLS_RTL
#include "cdc_unit_sc_foreign_module.h"
#else

#include "cdc_testmux.h"
#include "cdc_reset_sync.h"
#include "cdc_2ff_sync.h"								
#include "cdc_pulse_sync.h"				
#include "cdc_handshake.h"				

SC_MODULE(cdc_unit) {
public:
    sc_in<bool>              clk;
    sc_in<bool>              rst_n;
    sc_in<bool>              mclk;
    sc_out<bool>             muxclk_out;
    sc_out<bool>             muxrst_n_out;
    sc_in<bool>              test_mode_in;
    sc_in<bool>              tick_in;
    sc_in< sc_int<DATABITS> >      audio0_in;
    sc_in< sc_int<DATABITS> >      audio1_in;
    sc_out<bool>             tick_out;
    sc_out< sc_int<DATABITS> >     audio0_out;
    sc_out< sc_int<DATABITS> >     audio1_out;
    sc_in<bool>              req_in;
    sc_out<bool>             req_out;
    
    sc_in<bool>              play_in;
    sc_out<bool>             play_out;
    
    sc_signal<bool> muxclk;
    sc_signal<bool> muxrst_n;  
    sc_signal<bool> rsync_clk;  
    sc_signal<bool> mrst_n;

    cdc_testmux cdc_testmux_inst;
    cdc_reset_sync cdc_reset_sync_inst;
    cdc_handshake cdc_handshake_inst;
    cdc_pulse_sync cdc_pulse_sync_inst;
    cdc_2ff_sync cdc_2ff_sync_inst;

    sc_signal< sc_uint<2*DATABITS> > audio_in_concat;    
    sc_signal< sc_uint<2*DATABITS> > audio_out_concat;    

    void interconnect_proc() {
      audio_in_concat =  (sc_uint<2*DATABITS>)(audio1_in, audio0_in);
      audio0_out = (sc_int<DATABITS>)audio_out_concat.read().range(DATABITS-1,0);
      audio1_out = (sc_int<DATABITS>)audio_out_concat.read().range(2*DATABITS-1,DATABITS);
      muxclk_out = muxclk;
      muxrst_n_out = muxrst_n;
    }

    SC_CTOR(cdc_unit) :
      cdc_testmux_inst("cdc_testmux_inst"),
      cdc_reset_sync_inst("cdc_reset_sync_inst"),
      cdc_handshake_inst("cdc_handshake_inst"),
      cdc_pulse_sync_inst("cdc_pulse_sync_inst"),
      cdc_2ff_sync_inst("cdc_2ff_sync_inst")
    {

    SC_METHOD(interconnect_proc);
    sensitive << audio0_in << audio1_in << audio_out_concat << muxclk << muxrst_n;

    cdc_testmux_inst.test_mode_in(test_mode_in);
    cdc_testmux_inst.clk(clk);
    cdc_testmux_inst.rst_n(rst_n);
    cdc_testmux_inst.mrst_n(mrst_n);    
    cdc_testmux_inst.mclk(mclk);
    cdc_testmux_inst.muxclk(muxclk);
    cdc_testmux_inst.muxrst_n(muxrst_n);
    cdc_testmux_inst.rsync_clk(rsync_clk);                        

    cdc_reset_sync_inst.clk(rsync_clk);
    cdc_reset_sync_inst.rst_n(rst_n);
    cdc_reset_sync_inst.mrst_n(mrst_n);

    cdc_2ff_sync_inst.clk(muxclk);
    cdc_2ff_sync_inst.rst_n(muxrst_n);
    cdc_2ff_sync_inst.bit_in(play_in);    
    cdc_2ff_sync_inst.bit_out(play_out);    
    
    cdc_pulse_sync_inst.clk(clk);
    cdc_pulse_sync_inst.rst_n(rst_n);
    cdc_pulse_sync_inst.bit_in(req_in);    
    cdc_pulse_sync_inst.bit_out(req_out);    
    
    cdc_handshake_inst.clk1(clk);
    cdc_handshake_inst.rst1_n(rst_n);
    cdc_handshake_inst.clk2(muxclk);
    cdc_handshake_inst.rst2_n(muxrst_n);
    cdc_handshake_inst.tx_en_in(tick_in);
    cdc_handshake_inst.tx_in(audio_in_concat);
    cdc_handshake_inst.rx_en_out(tick_out);
    cdc_handshake_inst.rx_out(audio_out_concat);
    
    }

};

#endif
#endif

