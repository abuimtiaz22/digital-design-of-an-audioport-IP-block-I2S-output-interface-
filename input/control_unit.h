#ifndef control_unit_h
#define control_unit_h

#include "systemc_headers.h"
#include "audioport_defs.h"

#ifdef HLS_RTL
#include "control_unit_sc_foreign_module.h"
#else

SC_MODULE(control_unit) {
 public:
  sc_in_clk              clk;
  sc_in<bool>            rst_n;
  sc_in < sc_uint<32> >  PADDR;
  sc_in < sc_uint<32> >  PWDATA;
  sc_in < bool >         PENABLE;
  sc_in < bool >         PSEL;
  sc_in < bool >         PWRITE;
  sc_out < sc_uint<32> > PRDATA;
  sc_out < bool >        PREADY;
  sc_out < bool >        PSLVERR;
  sc_out < bool >        irq_out;
  sc_out < sc_uint<32> > cfg_reg_out;
  sc_out <bool>          cfg_out;
  sc_out < sc_uint<32> > level_reg_out;
  sc_out <bool>          level_out;
  sc_out <bool>          clr_out;
  sc_out < sc_bv<DSP_REGISTERS*32> >  dsp_regs_out;
  sc_in  <bool>          req_in;
  sc_out < sc_int<24> >  audio0_out;
  sc_out < sc_int<24> >  audio1_out;
  sc_out <bool>          tick_out;
  sc_out <bool>          play_out;

  void bus_decoder();
  void bus_writer();
  void command_decoder();
  void rbank_writer();
  void rbank_reader();  
  void play_logic();
  void interrupt_handler();
  void fifo_writer();
  void fifo_reader();  
  
  void control_regs_proc();
  
  sc_signal < sc_uint<32> >  rbank_r[AUDIOPORT_REGISTERS];
  sc_signal < bool >         irq_r;
  sc_signal < bool >         play_r;
  sc_signal < bool >         req_r;
  
  sc_signal < sc_uint<24> >  ldata_r[AUDIO_FIFO_SIZE];
  sc_signal < sc_uint<16> > lhead_r;
  sc_signal < sc_uint<16> > ltail_r;  
  sc_signal < bool >        llooped_r;
  sc_signal<bool>           lempty;
  sc_signal<bool>           lfull;
  sc_signal < sc_uint<24> >  lfifo;
  
  sc_signal < sc_uint<24> >  rdata_r[AUDIO_FIFO_SIZE];
  sc_signal < sc_uint<16> > rhead_r;
  sc_signal < sc_uint<16> > rtail_r;  
  sc_signal < bool >        rlooped_r;
  sc_signal <bool>          rempty;
  sc_signal <bool>          rfull;    
  sc_signal < sc_uint<24> > rfifo;

  sc_signal < sc_uint<24> > ldata_ns[AUDIO_FIFO_SIZE];
  sc_signal < sc_uint<16> > lhead_ns;
  sc_signal < sc_uint<16> > ltail_ns;  
  sc_signal < bool >        llooped_ns;
  sc_signal < sc_uint<24> > rdata_ns[AUDIO_FIFO_SIZE];
  sc_signal < sc_uint<16> > rhead_ns;
  sc_signal < sc_uint<16> > rtail_ns;  
  sc_signal < bool >        rlooped_ns;
  
  sc_signal < sc_uint<32> >  rbank_ns[AUDIOPORT_REGISTERS];
  sc_signal < bool >         irq_ns;
  sc_signal < bool >         play_ns;
  sc_signal < bool >         req_ns;
  sc_signal<sc_uint<16>>     rindex;
  sc_signal<bool>            apbwrite;
  sc_signal<bool>            apbread;  
  sc_signal<bool>            cmd_exe;
  sc_signal<bool>            start;
  sc_signal<bool>            stop;
  sc_signal<bool>            clr;
  sc_signal<bool>            irqack;
  
 SC_CTOR(control_unit) :
  clk("clk"),
    rst_n("rst_n"),
    PADDR("PADDR"),
    PWDATA("PWDATA"),
    PENABLE("PENABLE"),
    PSEL("PSEL"),
    PWRITE("PWRITE"),
    PRDATA("PRDATA"),
    PREADY("PREADY"),
    PSLVERR("PSLVERR"),
    irq_out("irq_out"),
    cfg_reg_out("cfg_reg_out"),
    cfg_out("cfg_out"),
    level_reg_out("level_reg_out"),
    level_out("level_out"),
    clr_out("clr_out"),
    dsp_regs_out("dsp_regs_out"),
    req_in("req_in"),
    audio0_out("audio0_out"),
    audio1_out("audio1_out"),
    tick_out("tick_out"),
    play_out("play_out"),
    //    rbank_r("rbank_r"),
    irq_r("irq_r"),
    play_r("play_r"),
    req_r("req_r"),
    //    rbank_ns("rbank_ns"),
    irq_ns("irq_ns"),
    play_ns("play_ns"),
    req_ns("req_ns"),
    rindex("rindex"),
    start("start"),
    stop("stop"),
    clr("clr"),
    irqack("irqack")

    {

      SC_METHOD(bus_decoder);
      sensitive << PADDR << PSEL << PENABLE << PWRITE;

      SC_METHOD(bus_writer);
      sensitive  <<  PSEL << rindex << lfifo << rfifo;
      for(int i=0; i < AUDIOPORT_REGISTERS; ++i)
	sensitive << rbank_r[i];
      
      SC_METHOD(command_decoder);
      sensitive << apbwrite << PWDATA << rindex << play_r;

      SC_METHOD(rbank_writer);
      sensitive << apbwrite << rindex << start << stop << PWDATA;
      for(int i=0; i < AUDIOPORT_REGISTERS; ++i)
	sensitive << rbank_r[i];
      
      SC_METHOD(rbank_reader);
      for(int i=0; i < AUDIOPORT_REGISTERS; ++i)
	sensitive << rbank_r[i];

      SC_METHOD(play_logic);
      sensitive << req_in << start << stop << play_r << req_r;

      SC_METHOD(interrupt_handler);
      sensitive << stop << irqack << lempty << rempty << play_r << irq_r;

      SC_METHOD(fifo_writer);
      sensitive << apbwrite << apbread << rindex << lhead_r << ltail_r << llooped_r << lempty << lfull
		<< rhead_r << rtail_r << rlooped_r << rempty << rfull << req_r << PWDATA << clr << play_r;
      for(int i=0; i < AUDIO_FIFO_SIZE; ++i)
	{
	  sensitive << ldata_r[i];
	  sensitive << rdata_r[i];
	}
      
      SC_METHOD(fifo_reader);
      sensitive << lhead_r << ltail_r << llooped_r << rhead_r << rtail_r << rlooped_r;
      for(int i=0; i < AUDIO_FIFO_SIZE; ++i)
	{
	  sensitive << ldata_r[i];
	  sensitive << rdata_r[i];
	}
          
      SC_METHOD(control_regs_proc);
      sensitive << clk.pos() << rst_n.neg();

  }
    



};


#endif

#endif
