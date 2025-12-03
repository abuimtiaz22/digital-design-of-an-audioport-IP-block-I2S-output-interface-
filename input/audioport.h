#ifndef audioport_h
#define audioport_h

#include "systemc_headers.h"
#include "audioport_defs.h"

//#define _test_

#ifdef HLS_RTL
#include "audioport_sc_foreign_module.h"
#else
#include "control_unit.h"
#include "dsp_unit.h"
#include "cdc_unit.h"
#include "i2s_unit.h"

SC_MODULE(audioport) {
public:
  sc_in<bool>             clk;
  sc_in<bool>            rst_n;
  sc_in<bool>            mclk;
  sc_in < sc_uint<32> >  PADDR;
  sc_in < sc_uint<32> >  PWDATA;
  sc_in < bool >         PENABLE;
  sc_in < bool >         PSEL;
  sc_in < bool >         PWRITE;
  sc_out < sc_uint<32> > PRDATA;
  sc_out < bool >        PREADY;
  sc_out < bool >        PSLVERR;
  sc_out < bool >        irq_out;
  sc_out <bool>          sdo_out;
  sc_out <bool>          ws_out;
  sc_out <bool>          sck_out;
  sc_in<bool>            test_mode_in;
  sc_in<bool>            scan_en_in;  

#ifdef _test_
  void testproc() {
    PRDATA.write(0);
    wait();
    while(1) {
      PRDATA.write(PWDATA.read());
      wait();
    }
  }
#endif
  
#ifndef _test_
  control_unit           control_unit_1;
  dsp_unit               dsp_unit_1;
  cdc_unit               cdc_unit_1;
  i2s_unit               i2s_unit_1;

  sc_signal<bool>          tick;
  sc_signal<bool>          play;
  sc_signal<bool>          cfg;
  sc_signal<bool>          level;
  sc_signal<bool>          clr;
  sc_signal< sc_int<24> >  audio0;
  sc_signal< sc_int<24> >  audio1;  
  sc_signal< sc_uint<32> > cfg_reg;
  sc_signal< sc_uint<32> > level_reg;
  sc_signal< sc_bv<DSP_REGISTERS*32> >  dsp_regs;
  sc_signal< sc_int<24> >  daudio0;
  sc_signal< sc_int<24> >  daudio1;  
  sc_signal<bool> 	   dtick;
  sc_signal<bool>          muxclk;
  sc_signal<bool>          muxrst_n;  
  sc_signal<bool> 	   mtick;
  sc_signal<bool> 	   mplay;
  sc_signal<bool> 	   mreq;
  sc_signal< sc_int<24> >  maudio0;
  sc_signal< sc_int<24> >  maudio1;
  sc_signal<bool> 	   req;
#endif
  
  SC_CTOR(audioport) :
  clk("clk"),
    rst_n("rst_n"),
    mclk("mclk"),
    PADDR("PADDR"),
    PWDATA("PWDATA"),
    PENABLE("PENABLE"),
    PSEL("PSEL"),
    PWRITE("PWRITE"),
    PRDATA("PRDATA"),
    PREADY("PREADY"),
    PSLVERR("PSLVERR"),
    irq_out("irq_out"),
    sdo_out("sdo_out"),
    ws_out("ws_out"),
    sck_out("sck_out"),
    test_mode_in("test_mode_in"),
    scan_en_in("scan_en_in")
#ifndef _test_
    ,
    control_unit_1("control_unit_1"),
    dsp_unit_1("dsp_unit_1"),
    cdc_unit_1("cdc_unit_1"),
    i2s_unit_1("i2s_unit_1")
#endif
    {
#ifdef _test_
      SC_CTHREAD(testproc, clk.pos());
      async_reset_signal_is(rst_n, false);
#endif
      
#ifndef _test_      
      control_unit_1.clk(clk);
      control_unit_1.rst_n(rst_n);
      control_unit_1.PSEL(PSEL);
      control_unit_1.PENABLE(PENABLE);
      control_unit_1.PWRITE(PWRITE);
      control_unit_1.PADDR(PADDR);	      
      control_unit_1.PWDATA(PWDATA);
      control_unit_1.PRDATA(PRDATA);
      control_unit_1.PREADY(PREADY);
      control_unit_1.PSLVERR(PSLVERR);
      control_unit_1.irq_out(irq_out);
      control_unit_1.audio0_out(audio0);
      control_unit_1.audio1_out(audio1);
      control_unit_1.cfg_reg_out(cfg_reg);
      control_unit_1.level_reg_out(level_reg);
      control_unit_1.dsp_regs_out(dsp_regs);
      control_unit_1.cfg_out(cfg);
      control_unit_1.level_out(level);
      control_unit_1.clr_out(clr);   
      control_unit_1.tick_out(tick);
      control_unit_1.play_out(play);
      control_unit_1.req_in(req);

      dsp_unit_1.clk(clk);
      dsp_unit_1.rst_n(rst_n);
      dsp_unit_1.audio0_in(audio0);
      dsp_unit_1.audio1_in(audio1);      
      dsp_unit_1.cfg_reg_in(cfg_reg);
      dsp_unit_1.level_reg_in(level_reg);
      dsp_unit_1.dsp_regs_in(dsp_regs);
      dsp_unit_1.tick_in(tick);
      dsp_unit_1.level_in(level);
      dsp_unit_1.clr_in(clr);		
      dsp_unit_1.cfg_in(cfg);
      dsp_unit_1.audio0_out(daudio0);
      dsp_unit_1.audio1_out(daudio1);
      dsp_unit_1.tick_out(dtick);

      cdc_unit_1.clk(clk);
      cdc_unit_1.rst_n(rst_n);
      cdc_unit_1.test_mode_in(test_mode_in);      
      cdc_unit_1.audio0_in(daudio0);
      cdc_unit_1.audio1_in(daudio1);      
      cdc_unit_1.tick_in(dtick);
      cdc_unit_1.play_in(play);
      cdc_unit_1.req_out(req);
      cdc_unit_1.mclk(mclk);
      cdc_unit_1.muxclk_out(muxclk);      
      cdc_unit_1.muxrst_n_out(muxrst_n);
      cdc_unit_1.audio0_out(maudio0);
      cdc_unit_1.audio1_out(maudio1);
      cdc_unit_1.tick_out(mtick);
      cdc_unit_1.play_out(mplay); 
      cdc_unit_1.req_in(mreq);

      i2s_unit_1.clk( muxclk );
      i2s_unit_1.rst_n( muxrst_n );
      i2s_unit_1.play_in( mplay );
      i2s_unit_1.tick_in( mtick );
      i2s_unit_1.audio0_in( maudio0);
      i2s_unit_1.audio1_in( maudio1);
      i2s_unit_1.req_out( mreq );
      i2s_unit_1.ws_out( ws_out );
      i2s_unit_1.sck_out( sck_out );
      i2s_unit_1.sdo_out( sdo_out );
#endif
    }
    
};


#endif

#endif
