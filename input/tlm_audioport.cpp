#include "tlm_audioport.h"

// ----------------------------------------------------------------------------------
// b_transport: TLM2.0 blocking transport method for target
// ----------------------------------------------------------------------------------

void tlm_audioport::b_transport( tlm::tlm_generic_payload& trans, sc_time& delay )
{
    tlm_cmd  = trans.get_command();
    tlm_addr = trans.get_address();
    tlm_buffer = trans.get_data_ptr();
    tlm_len  = trans.get_data_length();
    tlm_byt  = trans.get_byte_enable_ptr();
    tlm_wid  = trans.get_streaming_width();
    
    if (tlm_byt != 0 || tlm_len > 4 || tlm_wid < tlm_len)
      SC_REPORT_ERROR("TLM-2", "Target does not support given generic payload transaction format");
    
    if ((tlm_addr < sc_dt::uint64(AUDIOPORT_START_ADDRESS)) || (tlm_addr > sc_dt::uint64(AUDIOPORT_END_ADDRESS)))
      {
	char str[1024];
	sprintf(str, "Generic payload transaction address %x out of range [%x, %x]",
		tlm_addr, AUDIOPORT_START_ADDRESS, AUDIOPORT_END_ADDRESS);  
	SC_REPORT_ERROR("TLM-2", str);
      }
    else
      {
	if ( tlm_cmd == tlm::TLM_READ_COMMAND )
	  {
	    bus_read((unsigned int)tlm_addr, tlm_data, delay);
	    memcpy(tlm_buffer, &tlm_data, tlm_len);
	  }
	else if ( tlm_cmd == tlm::TLM_WRITE_COMMAND )
	  {
	    memcpy(&tlm_data, tlm_buffer, tlm_len);
	    bus_write((unsigned int)tlm_addr, tlm_data, delay);
	  }
	trans.set_response_status( tlm::TLM_OK_RESPONSE );
      }
}

// ----------------------------------------------------------------------------------
// bus_read: Register bank read
// ----------------------------------------------------------------------------------

void tlm_audioport::bus_read(unsigned int addr, unsigned int &rdata, sc_time& delay )
{
  unsigned int rindex;
  sc_time t(TLM_DATA_READ_DELAY, SC_NS);
  rindex = (addr - AUDIOPORT_START_ADDRESS)/4;
  if (rindex < AUDIOPORT_REGISTERS)
    rdata = rbank_r[rindex];
  delay = t;
}

// ----------------------------------------------------------------------------------
// bus_write: Register bank write and command actions
// ----------------------------------------------------------------------------------

void tlm_audioport::bus_write(unsigned int addr, unsigned int wdata, sc_time& delay )
{
  unsigned int rindex;
  rindex = (addr - AUDIOPORT_START_ADDRESS)/4;
  if (rindex < AUDIOPORT_REGISTERS)
    rbank_r[rindex] = wdata;
  
  if (rindex == CMD_REG_INDEX)
    {
      cmd_r = wdata;
      switch (cmd_r)
	{
	case CMD_START:
	  {
	    play_mode = 1;
	    rbank_r[STATUS_REG_INDEX][STATUS_PLAY] = 1;
	    break;
	  }
	case CMD_STOP:
	  {
	    play_mode = 0;	
	    irq = 0;
	    rbank_r[STATUS_REG_INDEX][STATUS_PLAY] = 0;
	    break;
	  }
	case CMD_CFG:
	  {
	    if (!play_mode)
	      {
		active_config_data = rbank_r[CFG_REG_INDEX];
		for (int i=0; i < DSP_REGISTERS; ++i)
		  active_dsp_regs[i] = rbank_r[DSP_REGS_START_INDEX+i];
	      }
	    break;
	  }
	case CMD_LEVEL:
	  {
	    active_level_data[0] = rbank_r[LEVEL_REG_INDEX].range(15,0);
	    active_level_data[1] = rbank_r[LEVEL_REG_INDEX].range(31,16);
	    break;
	  }
	case CMD_IRQACK:
	  {
	    irq = 0;
	    break;
	  }

	case CMD_CLR:
	  {
	    if (!play_mode)
	      {
		sc_int<24> tmp;
		for(int j=0; j < FILTER_TAPS; ++j)
		  {
		    filter_data[j][0] = 0;
		    filter_data[j][1] = 0;		
		  }
		dsp_inputs[0] = 0;
		dsp_inputs[1] = 0;
		dsp_outputs[0] = 0;
		dsp_outputs[1] = 0;
		while (lfifo.nb_read(tmp));
		while (rfifo.nb_read(tmp));		
		break;
	      }
	  }
	}
    }
  else if (rindex == LEFT_FIFO_INDEX) {
    lfifo.write(sc_int<24>(wdata));
  }
  else if (rindex == RIGHT_FIFO_INDEX) {
    rfifo.write(sc_int<24>(wdata));
  }
  
  sc_time t(TLM_DATA_WRITE_DELAY, SC_NS);
  delay = t;
}

// ----------------------------------------------------------------------------------
// do_dsp: DSP thread
// ----------------------------------------------------------------------------------

void tlm_audioport::do_dsp()
{

  while(1)
    {
      wait(req);

      dsp_inputs[0] = lfifo.read();
      dsp_inputs[1] = rfifo.read();
      if (lfifo.num_available() == 0 && rfifo.num_available() == 0)
	irq = 1;
      
      // Filter

      if (active_config_data[CFG_FILTER] == DSP_FILTER_OFF)
	{
	  filter_outputs[0] = dsp_inputs[0];
	  filter_outputs[1] = dsp_inputs[1];
	}
      else
	{
	  for (int tap=FILTER_TAPS-1; tap > 0; --tap)
	    {
	      filter_data[tap][0] = filter_data[tap-1][0];
	      filter_data[tap][1] = filter_data[tap-1][1];			  
	    }
	  filter_data[0][0] = dsp_inputs[0];
	  filter_data[0][1] = dsp_inputs[1];
	  
	  accuFIR0 = 0;
	  accuFIR1 = 0;
	  for (int tap=0; tap < FILTER_TAPS; ++tap)
	    {
	      sc_int < 24 >                   d;
	      sc_int < 32 >                   c;      
	      sc_int < 32+24 > mul;
	      d = filter_data[tap][0];
	      c = active_dsp_regs[tap];
	      mul = c * d;
	      accuFIR0 = accuFIR0 + mul;
	      d = filter_data[tap][1];
	      c = active_dsp_regs[FILTER_TAPS+tap];
	      mul = c * d;
	      accuFIR1 = accuFIR1 + mul;
	    }
	  filter_outputs[0] = accuFIR0 >> 31;
	  filter_outputs[1] = accuFIR1 >> 31;
	}
      
      // scaler
      scaledL = filter_outputs[0];
      scaledR = filter_outputs[1];
      levelL = 0;
      levelR = 0;
      levelL = (sc_int<17>)(active_level_data[0]);
      levelR = (sc_int<17>)(active_level_data[1]);
      
      scaledL = scaledL * levelL;
      scaledR = scaledR * levelR;		
      scaledL = scaledL >> 15;
      scaledR = scaledR >> 15;		
      
      dsp_outputs[0] = scaledL;
      dsp_outputs[1] = scaledR;
      
      audio_data_t sample;
      sample.left = dsp_outputs[0];
      sample.right = dsp_outputs[1];
      dsp_data.write(sample);

      wait(TLM_DSP_DELAY, SC_NS);

      tick.notify(TLM_TICK_DELAY, SC_NS);

    }
}


// ----------------------------------------------------------------------------------
// do_i2s: I2S thread
// ----------------------------------------------------------------------------------

void tlm_audioport::do_i2s()
{
  double delay;
  audio_data_t sample;
  sdo_out.write(0);
  sck_out.write(0);
  ws_out.write(0);
  irq_out.write(0);
  i2s_state = STOP;
  i2s_srg = 0;
  i2s_sample.left = 0;
  i2s_sample.right = 0;
  sck_ctr = 0;
  ws_ctr = 0;
  ws_state = 0;

  while(1)
    {

      if (play_mode && i2s_state == STOP) // START
	{
	  audio_data_t tmp;
	  while (cdc_fifo.nb_read(tmp)); // clear fifo!
	  /*	  sample.left = 0;
	  sample.right = 0;
	  cdc_fifo.write(sample);
	  */
	  i2s_state = PLAY;
	}

      if (!play_mode && sck_ctr == 1 && ws_ctr == 0)
	{
	  /*	  while(cdc_fifo.num_available() > 0)
	    cdc_fifo.read();	    
	  */
	  i2s_state = STOP;
	}

      if (i2s_state == PLAY)
	{
	  
	  if( sck_ctr == 1)
	    {
	      if (ws_ctr == 0)
		{
		  req.notify(TLM_REQ_DELAY, SC_NS);
		  /*
		  if (cdc_fifo.num_available() == 0)
		    {
		      SC_REPORT_ERROR("tlm_audioport", "Audio FIFO empty.");
		      i2s_sample.left = 0;
		      i2s_sample.right = 0;
		    }
		  else
		    {
		      i2s_sample = cdc_fifo.read();
		    }
		  */
		  i2s_sample = dsp_data.read();
		  i2s_srg = (i2s_sample.left, i2s_sample.right);
		}
	      else
		{
		  i2s_srg = i2s_srg << 1;
		}
	      if (ws_ctr == 23 || ws_ctr == 47)
		ws_state = !ws_state;
	      sdo_out.write(i2s_srg[47]);
	      irq_out.write(irq);
	      ws_out.write(ws_state);
	      sck_out.write(0);
	    }
	  else
	    {
	      sck_out.write(1);
	    }
	  
	  if (sck_ctr == 1)
	    {
	      if (ws_ctr < 47)
		ws_ctr = ws_ctr + 1;
	      else
		ws_ctr = 0;
	    }

	  if (sck_ctr == 0)
	    sck_ctr = 1;
	  else
	    sck_ctr = 0;
	  
	  delay = 0.02083333/96; // 48kHz
	  wait(delay, SC_MS);
	}
      else
	{
	  sdo_out.write(0);
	  sck_out.write(0);
	  ws_out.write(0);
	  i2s_state = STOP;
	  sck_ctr = 0;
	  ws_ctr = 0;
	  ws_state = 0;
	  wait(10.0, SC_NS);
	  irq_out.write(0);
	}
    }
}


#if defined(MTI_SYSTEMC)
SC_MODULE_EXPORT(tlm_audioport);
#endif
