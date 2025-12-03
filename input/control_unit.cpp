#include "control_unit.h"

void control_unit::control_regs_proc()
{
  
  if (rst_n.read() == 0)
    {
      for(int i=0; i < AUDIOPORT_REGISTERS; ++i)
	rbank_r[i] = 0;
      for(int i=0; i < AUDIO_FIFO_SIZE; ++i)
	{
	  ldata_r[i] = 0;
	  rdata_r[i] = 0;	  
	}
      lhead_r = 0;
      ltail_r = 0;
      llooped_r = 0;
      rhead_r = 0;
      rtail_r = 0;
      rlooped_r = 0;
      irq_r = 0;
      play_r = 0;
      req_r = 0;
    }
  else
    {
      for(int i=0; i < AUDIOPORT_REGISTERS; ++i)
	rbank_r[i] =  rbank_ns[i];
      for(int i=0; i < AUDIO_FIFO_SIZE; ++i)
	{
	  ldata_r[i] = ldata_ns[i];
	  rdata_r[i] = rdata_ns[i];	  
	}
      lhead_r = lhead_ns;
      ltail_r = ltail_ns;
      llooped_r = llooped_ns;
      rhead_r = rhead_ns;
      rtail_r = rtail_ns;
      rlooped_r = rlooped_ns;
      irq_r = irq_ns;
      play_r = play_ns;
      req_r = req_ns;
    }

}

void control_unit::bus_decoder()
{
  if(PSEL.read() == 1)
    rindex.write( ((PADDR.read() - AUDIOPORT_START_ADDRESS) >> 2) );
  else
    rindex.write(0);

  if(PSEL.read() == 1 && PENABLE.read() == 1 && PWRITE.read() == 1)  
    apbwrite.write(1);
  else
    apbwrite.write(0);    

  if(PSEL.read() == 1 && PENABLE.read() == 1 && PWRITE.read() == 0)  
    apbread.write(1);
  else
    apbread.write(0);    
  
}


void control_unit::bus_writer()
{

  PREADY.write(1);
  PSLVERR.write(0);

  // PRDATA mux
  if (PSEL.read() == 1)
    {
      if (rindex.read() < AUDIOPORT_REGISTERS)
	PRDATA.write( rbank_r[rindex.read()].read() );
      else if (rindex.read() == LEFT_FIFO_INDEX)
	PRDATA.write( sc_uint<32> (lfifo.read()) );
      else if (rindex.read() == RIGHT_FIFO_INDEX)
	PRDATA.write( sc_uint<32> (rfifo.read()) );
      else
	PRDATA.write( 0 );	
    }
  else
    PRDATA.write(0);
  
}

void control_unit::command_decoder()
{
  clr.write(0);
  clr_out.write(0);
  cfg_out.write(0);
  level_out.write(0);
  start.write(0);
  stop.write(0);
  irqack.write(0);
  
  if (apbwrite.read() == 1 && rindex.read() == CMD_REG_INDEX)
    { 
      switch (PWDATA.read())
	{
	case CMD_NOP:
	  break;
	case CMD_CLR:   
	  if (!play_r)
	    {
	      clr.write(1);
	      clr_out.write(1);
	    }
	    break;
	case CMD_CFG:   
	  cfg_out.write(1);	  
	  break;
	case CMD_LEVEL: 
	  level_out.write(1);
	  break;
	case CMD_START: 
	  start.write(1);
	  break;
	case CMD_STOP:  
	  stop.write(1);
	  break;
	case CMD_IRQACK:  
	  irqack.write(1);
	  break;
	}
    }
}


void control_unit::rbank_writer()
{
  int index;
  index = rindex.read();

  for (int i = 0; i < AUDIOPORT_REGISTERS; ++i)
    {
      if (apbwrite.read() == 1 && i == index)
	rbank_ns[i].write(PWDATA);
      else
	rbank_ns[i].write(rbank_r[i].read());
    }
  
  if (start || stop)
    {
      sc_uint<32> tmp = rbank_r[STATUS_REG_INDEX].read();
      if (start)
	tmp[STATUS_PLAY] = 1;      
      else if (stop)
	tmp[STATUS_PLAY] = 0;      
      rbank_ns[STATUS_REG_INDEX].write(tmp);
    }

}

void control_unit::rbank_reader() {
  sc_bv<DSP_REGISTERS*32>  dsp_regs;  

  for(int i=0; i < DSP_REGISTERS; ++i)
    dsp_regs.range((i+1)*32-1, i*32) = (sc_bv<32>)(rbank_r[DSP_REGS_START_INDEX+i].read());
  dsp_regs_out. write( dsp_regs) ;
  
  cfg_reg_out.write( rbank_r[CFG_REG_INDEX].read() );
  level_reg_out.write( rbank_r[LEVEL_REG_INDEX].read() );


}

void control_unit::play_logic()
{
  if (play_r.read() == 1 && req_in.read() == 1)
    req_ns.write(1);
  else
    req_ns.write(0);

  if (play_r.read() == 1)
    tick_out.write(req_r);
  else
    tick_out.write(0);

  if (start.read() == 1)
    play_ns.write(1);
  else if (stop.read() == 1)
    play_ns.write(0);		      
  else
    play_ns.write(play_r.read());

  play_out.write( play_r.read() );

}

void control_unit::interrupt_handler()
{
  if ( play_r.read() == 0)
    irq_ns.write(0); 
  else if (irqack.read() == 1 || stop.read() == 1)
    irq_ns.write(0);	       
  else if (rempty.read() == 1 && lempty.read() == 1)
    {
      irq_ns.write(1);
    }
  else
    irq_ns.write(irq_r.read());

  irq_out.write(irq_r.read());
}

void control_unit::fifo_writer()
{
  if (clr.read() == 1)
    {
      for(int i=0; i < AUDIO_FIFO_SIZE; ++i)
	{
	  ldata_ns[i].write(0);
	  rdata_ns[i].write(0);	  
	}
      lhead_ns.write(0);
      ltail_ns.write(0);
      llooped_ns.write(0);
      rhead_ns.write(0);
      rtail_ns.write(0);
      rlooped_ns.write(0);
    }
  else
    {

      for(int i=0; i < AUDIO_FIFO_SIZE; ++i)
	{
	  ldata_ns[i].write( ldata_r[i].read() );
	  rdata_ns[i].write( rdata_r[i].read() );
	}
      lhead_ns.write(lhead_r.read());
      ltail_ns.write(ltail_r.read());
      llooped_ns.write(llooped_r.read());
      rhead_ns.write(rhead_r.read());
      rtail_ns.write(rtail_r.read());
      rlooped_ns.write(rlooped_r.read());
      
      if (apbwrite.read() == 1 && rindex.read() == LEFT_FIFO_INDEX && lfull.read() == 0) {
	ldata_ns[lhead_r.read()].write(sc_uint<24>(PWDATA.read()));
	if (lhead_r.read() == AUDIO_FIFO_SIZE-1) {
	  lhead_ns.write(0);
	  llooped_ns.write(1);
	}
	else
	  {
	    lhead_ns.write(lhead_r.read() + 1);
	  }
      }
      
      if (apbwrite.read() == 1 && rindex.read() == RIGHT_FIFO_INDEX && rfull.read() == 0) {
	rdata_ns[rhead_r.read()].write(sc_uint<24>(PWDATA.read()));
	if (rhead_r.read() == AUDIO_FIFO_SIZE-1) {
	  rhead_ns.write(0);
	  rlooped_ns.write(1);
	}
	else
	  {
	    rhead_ns.write(rhead_r.read() + 1);
	  }
      }
    }


  if ((play_r.read() == 1 && req_r.read() == 1) || (apbread.read() == 1 && rindex.read() == LEFT_FIFO_INDEX))
    {
      if (lempty.read() == 0)
	{
	  if (ltail_r.read() == AUDIO_FIFO_SIZE-1)
	    {
	      ltail_ns.write(0);
	      llooped_ns.write(0);
	    }
	  else
	    {
	      ltail_ns.write( ltail_r.read() + 1 );
	    }
	}
    }
  if ((play_r.read() == 1 && req_r.read() == 1) || (apbread.read() == 1 && rindex.read() == RIGHT_FIFO_INDEX))
    {
      if (rempty.read() == 0)
	{
	  if (rtail_r.read() == AUDIO_FIFO_SIZE-1)
	    {
	      rtail_ns.write(0);
	      rlooped_ns.write(0);
	    }
	  else
	    {
	      rtail_ns.write( rtail_r.read() + 1 );
	    }
	}
    }
  
}


void control_unit::fifo_reader()
{
  bool le, re;
  le = 0;
  re = 0;
  if (lhead_r.read() == ltail_r.read())
    {
      if (llooped_r.read())
	{
	  lempty.write(0);
	  lfull.write(1);
	}
      else
	{
	  le = 1;
	  lempty.write(1);
	  lfull.write(0);
	}
    }
  else
    {
      lempty.write(0);
      lfull.write(0);
    }
  
  if (rhead_r.read() == rtail_r.read())
    {
      if (rlooped_r.read())
	{
	  rempty.write(0);
	  rfull.write(1);
	}
      else
	{
	  re = 1;
	  rempty.write(1);
	  rfull.write(0);
	}
    }
  else
    {
      rempty.write(0);
      rfull.write(0);
    }

  if (le)
    {
      lfifo.write( 0 );
      audio0_out.write( 0 );
    }
  else
    {
      lfifo.write( ldata_r[ltail_r.read()].read() );
      audio0_out.write( sc_int<24>(ldata_r[ltail_r.read()].read()) );
    }
  
  if (re)  
    {
      rfifo. write( 0 );
      audio1_out.write( 0 );
    }
  else
    {
      rfifo. write( rdata_r[rtail_r.read()].read() );
      audio1_out.write( sc_int<24>(rdata_r[rtail_r.read()].read()) );
    }



}


#if defined(MTI_SYSTEMC)
SC_MODULE_EXPORT(control_unit);
#endif

#if defined(XMSC)
XMSC_MODULE_EXPORT(control_unit);
#endif
