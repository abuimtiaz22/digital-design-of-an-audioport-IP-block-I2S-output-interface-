#include "tlm_top.h"

// Directory from where data are read
char *input_dir = (char *) "input";

// Directory where results files are saved
char *output_dir = (char *) "output";

// Name of simulation tun
char *run_name = (char *) 0;

// Output data file
ofstream output_file;

void save_test_parameters();

/////////////////////////////////////////////////////////////////////////////////////////////////////
//
// SystemC sc_main
//
/////////////////////////////////////////////////////////////////////////////////////////////////////

int sc_main( int argc, char *argv[] )
{
  tlm_top *tlm_top_inst;
  char filename[1024];

  sc_set_time_resolution(1,SC_PS);  

  tlm_top_inst = new tlm_top("tlm_top_inst");
  for (int i=1; i < argc; ++i)
    {
      if (!strcmp(argv[i], "-run"))
	{
	  ++i;
	  if (i < argc) run_name = argv[i];
	}
      else if (!strcmp(argv[i], "-input"))
	{
	  ++i;
	  if (i < argc) input_dir = argv[i];
	}
      else if (!strcmp(argv[i], "-output"))
	{
	  ++i;
	  if (i < argc) output_dir = argv[i];

	}
    }

  sprintf(filename, "%s/tlm_audioport_%s_out.txt", output_dir, run_name);
  output_file.open(filename);
  
  if (!output_file.is_open())
    cout << "Unable to open simulation output file " << filename << endl;
  else
    cout << "Simulation output is saved to file " << filename << endl;

  sc_start();

  cout << "SIMULATION STOPPED AT TIME = " << sc_time_stamp() << endl;

  if (output_file.is_open())
    output_file.close();

  save_test_parameters();
  return 0;  
}


void save_test_parameters()
{
  ofstream file;
  file.open("reports/1_vsim_audioport_test_paramaters.txt");
  
  
  file << "-----------------------------------------------------------------------------------------------" << endl;
      file << "DT3 PROJECT: SIMULATION PARAMATER VALUES:" << endl;
      file << "-----------------------------------------------------------------------------------------------" << endl;      
      file << "Clock periods:" << endl;
      file << "        clk                    " << std::setw(10) << std::fixed << std::setprecision(6) << CLK_PERIOD << " ns" << endl;
      file << "        mclk                   " << std::setw(10) << std::fixed << std::setprecision(6) << MCLK_PERIOD << " ns" << endl;            
      file << "DESIGN PARAMETERS:" << endl;
      file << "        FILTER_TAPS            " << std::setw(10) << FILTER_TAPS << endl;
      file << "        AUDIO_FIFO_SIZE        " << std::setw(10) << AUDIO_FIFO_SIZE << endl;
      file << "REGISTERS:" << endl;
      file << "        DSP_REGISTERS          " << std::setw(10) << DSP_REGISTERS << endl;
      file << "        AUDIOPORT_REGISTERS    " << std::setw(10) << AUDIOPORT_REGISTERS << endl;
      file << "INTERNAL REGISTER INDICES (DECIMAL):" << endl;
      file << "        CMD_REG_INDEX          " << std::setw(10) << CMD_REG_INDEX << endl;
      file << "        STATUS_REG_INDEX       " << std::setw(10) << STATUS_REG_INDEX << endl;      
      file << "        LEVEL_REG_INDEX        " << std::setw(10) << LEVEL_REG_INDEX << endl;
      file << "        CFG_REG_INDEX          " << std::setw(10) << CFG_REG_INDEX << endl;
      file << "        DSP_REGS_START_INDEX   " << std::setw(10) << DSP_REGS_START_INDEX << endl;
      file << "        DSP_REGS_END_INDEX     " << std::setw(10) << DSP_REGS_END_INDEX << endl;
      file << "        LEFT_FIFO_INDEX        " << std::setw(10) << LEFT_FIFO_INDEX << endl;
      file << "        RIGHT_FIFO_INDEX       " << std::setw(10) << RIGHT_FIFO_INDEX << endl;            
      file << "REGISTER APB ADDRESSES (HEX):" << endl;
      file << "        AUDIOPORT_START_ADDRESS" << std::hex << std::setw(10) <<  AUDIOPORT_START_ADDRESS << endl;
      file << "        AUDIOPORT_END_ADDRESS  " << std::hex << std::setw(10) <<  AUDIOPORT_END_ADDRESS << endl;      
      file << "        CMD_REG_ADDRESS        " << std::hex << std::setw(10) <<  CMD_REG_ADDRESS << endl;
      file << "        STATUS_REG_ADDRESS     " << std::hex << std::setw(10) <<  STATUS_REG_ADDRESS << endl;      
      file << "        LEVEL_REG_ADDRESS      " << std::hex << std::setw(10) <<  LEVEL_REG_ADDRESS << endl;
      file << "        CFG_REG_ADDRESS        " << std::hex << std::setw(10) <<  CFG_REG_ADDRESS << endl;
      file << "        DSP_REGS_START_ADDRESS " << std::hex << std::setw(10) <<  DSP_REGS_START_ADDRESS << endl;
      file << "        DSP_REGS_END_ADDRESS   " << std::hex << std::setw(10) <<  DSP_REGS_END_ADDRESS << endl;
      file << "        LEFT_FIFO_ADDRESS      " << std::hex << std::setw(10) <<  LEFT_FIFO_ADDRESS << endl;
      file << "        RIGHT_FIFO_ADDRESS     " << std::hex << std::setw(10) <<  RIGHT_FIFO_ADDRESS << endl;            
      file << " APB CONFIGURATION (HEX):" << endl;
      file << "        DUT_START_ADDRESS        N/A" << endl;
      file << "        DUT_END_ADDRESS          N/A" << endl;      
      file << "        APB_START_ADDRESS        N/A" << endl;
      file << "        APB_END_ADDRESS          N/A" << endl;      
      file << " clk CYCLES PER SAMPLE:" << endl;
      file << "        CLK_DIV_48000          " << std::dec << std::setw(10) << CLK_DIV_48000 << endl;
      file << " CDC PARAREMETRS (INT):" << endl;
      file << "        CDC_DATASYNC_INTERVAL    N/A"  << endl;
      file << "        CDC_DATASYNC_LATENCY     N/A"  << endl;      
      file << "        CDC_BITSYNC_INTERVAL     N/A"  << endl;
      file << "        CDC_BITYNC_LATENCY       N/A"  << endl;      
      file << "        CDC_PULSESYNC_INTERVAL   N/A"  << endl;
      file << "        CDC_PULSESYNC_LATENCY    N/A"  << endl;      
      file << " dsp_unit PARAREMETERS:" << endl;
      file << "        DSP_UNIT_MAX_LATENCY   " << std::dec << std::setw(10) << DSP_UNIT_MAX_LATENCY << endl;
      file << "-----------------------------------------------------------------------------------------------" << endl;

  if (file.is_open())
    file.close();

}
