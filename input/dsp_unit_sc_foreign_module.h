#ifndef _dsp_unit_sc_foreign_module_
#define _dsp_unit_sc_foreign_module_

#ifdef MTI_SYSTEMC

// Foreign module for Siemens QuestaSim

class dsp_unit : public sc_foreign_module
{
 public:
    sc_in_clk  clk;
    sc_in<bool>  rst_n;

    sc_in < sc_int<DATABITS> >        audio0_in;
    sc_in < sc_int<DATABITS> >        audio1_in;
    sc_in < bool >                    tick_in;
    sc_in < bool >                    cfg_in;
    sc_in < bool >                    clr_in;
    sc_in < bool >                    level_in;
    sc_in  < sc_uint<32> >            cfg_reg_in;
    sc_in  < sc_uint<32> >            level_reg_in;
    sc_in < sc_bv<DSP_REGISTERS*32> > dsp_regs_in;
    sc_out < sc_int<DATABITS> >       audio0_out;
    sc_out < sc_int<DATABITS> >       audio1_out;
    sc_out < bool >                   tick_out;

    dsp_unit(sc_module_name nm, const char* hdl_name)
      : sc_foreign_module(nm),
      clk("clk"),
      rst_n("rst_n"),
      tick_in("tick_in"),
      cfg_in("cfg_in"),
      clr_in("clr_in")
	{
	  
	  elaborate_foreign_module(hdl_name);
	}
    ~dsp_unit()
    {}

};

#endif

#ifdef XCELIUM

// Foreign module for Cadence Xcelium

class dsp_unit : public xmsc_foreign_module
{
 public:
    sc_in_clk  clk;
    sc_in<bool>  rst_n;

    sc_in < sc_int<DATABITS> >        audio0_in;
    sc_in < sc_int<DATABITS> >        audio1_in;
    sc_in < bool >                    tick_in;
    sc_in < bool >                    cfg_in;
    sc_in < bool >                    clr_in;
    sc_in < bool >                    level_in;
    sc_in  < sc_uint<32> >            cfg_reg_in;
    sc_in  < sc_uint<32> >            level_reg_in;
    sc_in < sc_bv<DSP_REGISTERS*32> > dsp_regs_in;
    sc_out < sc_int<DATABITS> >       audio0_out;
    sc_out < sc_int<DATABITS> >       audio1_out;
    sc_out < bool >                   tick_out;

    dsp_unit(sc_module_name nm)
      : xmsc_foreign_module(nm),
    clk("clk"),
      rst_n("rst_n"),
      audio0_in("audio0_in"),
      audio1_in("audio1_in"),      
      tick_in("tick_in"),
      cfg_in("cfg_in"),
      clr_in("clr_in"),
      level_in("level_in"),
      level_reg_in("level_reg_in"),
      cfg_reg_in("cfg_reg_in"),
      dsp_regs_in("dsp_regs_in"),                        
      audio0_out("audio0_out"),
      audio1_out("audio1_out"),      
      tick_out("tick_out")
	{
	}
     const char* hdl_name() const { return "dsp_unit"; }
    ~dsp_unit()
    {}

};

#endif

#endif

