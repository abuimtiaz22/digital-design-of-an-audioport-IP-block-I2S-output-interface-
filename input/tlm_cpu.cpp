#include "tlm_cpu.h"

#include <iostream>
#include <iomanip>
using namespace std;


extern char     *input_dir;
extern ofstream output_file;

// ----------------------------------------------------------------------------------
// test_program: Test program to test major operating modes
// ----------------------------------------------------------------------------------

void tlm_cpu::test_program()
{
  sc_uint<32>   addr;
  sc_uint<32>   wdata;
  sc_uint<32>   rdata;
  bool          fail;
  int 	        irq_counter;
  sc_uint<32>   level_data = 0x80008000;
  sc_uint<16> 	level_value;

  irq_counter = 0;
  test_number = 0;

  read_filter_taps();

  ////////////////////////////////////////////////////////////////
  // Test 1: Program filter
  ////////////////////////////////////////////////////////////////
      
  SC_REPORT_INFO("", "T1: Program filter");
  test_number = 1;
      
  for (int i=0; i < DSP_REGISTERS; ++i)
    {
      addr = DSP_REGS_START_ADDRESS + i*4;
      wdata = filter_taps[i];
      rdata = ~wdata;
      bus_write(addr, wdata, fail);
      bus_read(addr, rdata, fail);	     	     
      if (! (wdata == rdata) )
	{
	  SC_REPORT_WARNING("", "T1: DSP_REGS write/read failure.");	     
	}
    }
      
  ////////////////////////////////////////////////////////////////
  // Test 2: Fill audio fifos
  ////////////////////////////////////////////////////////////////
      
  SC_REPORT_INFO("", "T2: Fill FIFOs");	
  test_number = 2;
      
  for(int unsigned i=0; i < AUDIO_FIFO_SIZE; ++i)
    {
      sc_int<24> audioL = square_generator();
      sc_int<24> audioR = sine_generator();	   	   

      audio_sample.left = audioL;
      audio_sample.right = audioR;
      audio_fifo.write(audio_sample);

      addr = LEFT_FIFO_ADDRESS;
      wdata = audioL;
      bus_write(addr, wdata, fail);

      wdata = audioR;
      addr = RIGHT_FIFO_ADDRESS;
      bus_write(addr, wdata, fail);	     	     
    }
      
  ////////////////////////////////////////////////////////////////
  // Test 3: Set Level
  ////////////////////////////////////////////////////////////////

  wait(2.0, SC_US);
      
  SC_REPORT_INFO("", "T3 Set Level");
  test_number = 3;
      
  addr = LEVEL_REG_ADDRESS;
  wdata = 0x80008000;
  rdata = ~wdata;
  bus_write(addr, wdata, fail);	 
  bus_read(addr, rdata, fail);	     	     

  if(!(wdata == rdata))
    {
      SC_REPORT_WARNING("", "T3: LEVEL_REG write/read failure.");	     
    }
      
  addr = CMD_REG_ADDRESS;
  wdata = 0;
  wdata = CMD_LEVEL;
  bus_write(addr, wdata, fail);	 

  ////////////////////////////////////////////////////////////////
  // Test 4: Configure
  ////////////////////////////////////////////////////////////////

  SC_REPORT_INFO("", "T4 Configure");
  test_number = 4;
      
  wdata = 0;
  addr = CFG_REG_ADDRESS;
  wdata.range(1,0) = DSP_FILTER_OFF;
  rdata = ~wdata;
  bus_write(addr, wdata, fail);
  bus_read(addr, rdata, fail);

  if(!(wdata == rdata))
    {
      SC_REPORT_WARNING("", "T4: CFG_REG write/read failure.");	     
    }
      
  addr = CMD_REG_ADDRESS;
  wdata = 0;
  wdata = CMD_CFG;
  bus_write(addr, wdata, fail);	 
      
  ////////////////////////////////////////////////////////////////
  // Test 5 - : Playback
  ////////////////////////////////////////////////////////////////

  test_number = 5;      
  for(int test_counter = 1; test_counter <= 3; ++test_counter)
    {
      switch(test_counter)
	{
	case 1:
	  SC_REPORT_INFO("", "T5.1: Filter OFF");
	  wdata = 0;
	  addr = CFG_REG_ADDRESS;
	  wdata[CFG_FILTER] = DSP_FILTER_OFF;
	  bus_write(addr, wdata, fail);
	      
	  addr = CMD_REG_ADDRESS;
	  wdata = 0;
	  wdata = CMD_CFG;
	  bus_write(addr, wdata, fail);	 
	      
	  break;
	      
	case 2:
	  SC_REPORT_INFO("", "T5.2: Filter ON");
	  wdata = 0;
	  addr = CFG_REG_ADDRESS;
	  wdata[CFG_FILTER] = DSP_FILTER_ON;
	  bus_write(addr, wdata, fail);
	      
	  addr = CMD_REG_ADDRESS;
	  wdata = 0;
	  wdata = CMD_CFG;
	  bus_write(addr, wdata, fail);	 
	  break;

	case 3:
	  SC_REPORT_INFO("", "T5.3: Filter OFF, level scaling");
	  wdata = 0;
	  addr = CFG_REG_ADDRESS;
	  wdata[CFG_FILTER] = DSP_FILTER_OFF;
	  bus_write(addr, wdata, fail);
	      
	  addr = CMD_REG_ADDRESS;
	  wdata = 0;
	  wdata = CMD_CFG;
	  bus_write(addr, wdata, fail);	 

	  addr = LEVEL_REG_ADDRESS;
	  wdata = 0x40002000;
	  bus_write(addr, wdata, fail);	 

	  addr = CMD_REG_ADDRESS;
	  wdata = 0;
	  wdata = CMD_LEVEL;
	  bus_write(addr, wdata, fail);	 
	  
	  break;

	}

      wait(2.0, SC_US);
	  
      addr = CMD_REG_ADDRESS;
      wdata = 0;
      wdata = CMD_START;
      bus_write(addr, wdata, fail);	 	
	  
      sc_time t1;
      sc_time t2;

      t1 = sc_time_stamp();
      
      irq_counter = 0;
      do 
	{
	  wait(10, SC_NS);

	  t2 = sc_time_stamp();

	  if (irq_out.read() == 1)
	    {
	      irq_handler();
	      while (irq_out.read() == 1)
		wait(10, SC_NS);	      
	      ++irq_counter;
	    }
	} while (((t2 - t1).to_seconds() < 0.005) && (irq_counter < 2)); 
	  

      wait(10.0, SC_US);

      addr = CMD_REG_ADDRESS;
      wdata = 0;
      wdata = CMD_STOP;
      bus_write(addr, wdata, fail);	 
	  
      wait(30.0, SC_US);
      
      scoreboard_reset.notify();
      phase_accu = 0;

      addr = CMD_REG_ADDRESS;
      wdata = 0;
      wdata = CMD_CLR;
      bus_write(addr, wdata, fail);	 

      wait(10.0, SC_US);

      for(int unsigned i=0; i < AUDIO_FIFO_SIZE; ++i)
	{
	  sc_int<24> audioL = square_generator();
	  sc_int<24> audioR = sine_generator();	   	   

	  audio_sample.left = audioL;
	  audio_sample.right = audioR;
	  audio_fifo.write(audio_sample);

	  addr = LEFT_FIFO_ADDRESS;
	  wdata = audioL;
	  bus_write(addr, wdata, fail);

	  wdata = audioR;
	  addr = RIGHT_FIFO_ADDRESS;
	  bus_write(addr, wdata, fail);
	}


    }
  sc_stop();
      
}

// ----------------------------------------------------------------------------------
// bus_write: TLM2.0 blocking write call
// ----------------------------------------------------------------------------------

void tlm_cpu::bus_write(sc_uint<32> addr, sc_uint<32> wdata, bool &fail)
{
  sc_time delay = sc_time(0, SC_NS);

  wait(TLM_BUS_ACCESS_DELAY, SC_NS);

  tlm_cmd =                   tlm::TLM_WRITE_COMMAND;
  tlm_status =                tlm::TLM_INCOMPLETE_RESPONSE;
  tlm_buffer =                wdata;
  tlm_tx->set_command         ( tlm_cmd );
  tlm_tx->set_address         ( addr );
  tlm_tx->set_data_ptr        ( reinterpret_cast<unsigned char*>(&tlm_buffer) );
  tlm_tx->set_data_length     ( 4 );
  tlm_tx->set_streaming_width ( 4 );
  tlm_tx->set_byte_enable_ptr ( 0 );
  tlm_tx->set_dmi_allowed     ( false );
  tlm_tx->set_response_status ( tlm_status );
  
  socket->b_transport( *tlm_tx, delay );  // Blocking transport call
      
  if ( tlm_tx->is_response_error() )
    {
      fail = 1;
      SC_REPORT_WARNING("TLM-2", "Response error from b_transport");
    }

  wait(delay);
  tlm_status = tlm_tx->get_response_status();
}

// ----------------------------------------------------------------------------------
// bus_read: TLM2.0 blocking read call
// ----------------------------------------------------------------------------------

void tlm_cpu::bus_read(sc_uint<32>  addr, sc_uint<32> &rdata, bool &fail)
{
  
  sc_time delay = sc_time(0, SC_NS);

  wait(TLM_BUS_ACCESS_DELAY, SC_NS);

  tlm_cmd =                   tlm::TLM_READ_COMMAND;
  tlm_status =                tlm::TLM_INCOMPLETE_RESPONSE;



  tlm_buffer =                0;
  tlm_tx->set_command         ( tlm_cmd );
  tlm_tx->set_address         ( addr );
  tlm_tx->set_data_ptr        ( reinterpret_cast<unsigned char*>(&tlm_buffer) );
  tlm_tx->set_data_length     ( 4 );
  tlm_tx->set_streaming_width ( 4 );
  tlm_tx->set_byte_enable_ptr ( 0 );
  tlm_tx->set_dmi_allowed     ( false );
  tlm_tx->set_response_status ( tlm_status );
  
  socket->b_transport( *tlm_tx, delay );
      
  if ( tlm_tx->is_response_error() )
    {
      fail = 1;
      SC_REPORT_WARNING("TLM-2", "Response error from b_transport");
    }
  else
    {
      rdata = (sc_uint<32>)tlm_buffer;
    }

  wait(delay);
  tlm_status = tlm_tx->get_response_status();
}

// ----------------------------------------------------------------------------------
// irq_handler: Interrupt request handler
// ----------------------------------------------------------------------------------

void tlm_cpu::irq_handler()
{
  sc_uint<32>   addr;
  sc_uint<32>   wdata;
  sc_uint<32>   rdata;
  bool          fail;
  
  // Mimic interrupt latency
  wait(TLM_INTERRUPT_LATENCY, SC_NS);
  
  // Fill next buffer
  for(int i=0; i < AUDIO_FIFO_SIZE; ++i)
    {
      sc_int<24> audioL = square_generator();
      sc_int<24> audioR = sine_generator();	   	   

      audio_sample.left = audioL;
      audio_sample.right = audioR;
      audio_fifo.write(audio_sample);

      addr = LEFT_FIFO_ADDRESS;
      wdata = audioL;
      bus_write(addr, wdata, fail);

      addr = RIGHT_FIFO_ADDRESS;      
      wdata = audioR;
      bus_write(addr, wdata, fail);
    }

  addr = CMD_REG_ADDRESS;
  wdata = CMD_IRQACK;
  bus_write(addr, wdata, fail);	 
  
}

// ----------------------------------------------------------------------------------
// read_filter_taps: Read filter coefficient from file or generate them
// ----------------------------------------------------------------------------------

#define FILTER_TAPS_FILE  "filter_taps.txt"
#define MAX_AMPLITUDE     8388607
#define COEFF_SCALING     0x7fffffff

int tlm_cpu::read_filter_taps()
{
  FILE *file;
  char line[1024];
  int 	lines;
  float coeff;
  int coeff_int;
  char  path[1024];
  sprintf(path, "%s/%s", input_dir, FILTER_TAPS_FILE);
  file = fopen(path, "r");

  if (file == NULL)
    {
      double B;

      for (int f = 0; f < 4; ++f)
	{
	  switch (f)
	    {
	    case 0:
	      B =0.35;
	      break;
	    case 1:
	      B =0.25;
	      break;
	    case 2:
	      B =0.15;
	      break;
	    case 3:
	      B = 0.05;
	      break;
	    }
	  for (int i=0; i < FILTER_TAPS; ++i)
	    {
	      int x;
	      double sinc;
	      x = (i-FILTER_TAPS/2);
	      if (x == 0)
		filter_taps[f*FILTER_TAPS+i] = (sc_int<32>)  (0.5*COEFF_SCALING);
	      else
		filter_taps[f*FILTER_TAPS+i] = (sc_int<32>)  (COEFF_SCALING*B*sin(2*B*M_PI*x)/(2*B*M_PI*x));
	    }
	}

      return 0;
    }
  else
    {
      lines = 0;

      while(fgets(line, 1023, file) != 0 && lines < 4*FILTER_TAPS)
	{
	  if (sscanf(line, "%f", &coeff) != 1)
	    cout << "Filter tap file format error (expected 1 floating point value)" << endl;
	  else
	    {
	      coeff_int = (coeff * COEFF_SCALING);
	      filter_taps[lines] = (sc_int<32>) coeff_int;
	    }
	  ++lines;
	}

      fclose(file);
      return lines;
    }
}

// ----------------------------------------------------------------------------------
// square_generator: Square wave generator
// ----------------------------------------------------------------------------------

sc_int<24> tlm_cpu::square_generator()
{
  int mod = 8;
  sc_int<24> sig;
  sc_int<24> noise;

  if (phase_accu % mod <= mod/2)
    sig = 1048576;
  else
    sig = -1048576;
  ++phase_accu;

  return sig;
}

// ----------------------------------------------------------------------------------
// sine_generator: Sine wave generator
// ----------------------------------------------------------------------------------

sc_int<24> tlm_cpu::sine_generator()
{
  sc_int<24> sig;
  double phi;
  phi = (phase_accu * 2 * M_PI)/16;
  sig = 1048576* sin(phi);
  return sig;
}

