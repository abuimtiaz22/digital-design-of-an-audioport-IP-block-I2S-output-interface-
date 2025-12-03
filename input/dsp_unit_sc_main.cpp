#include "dsp_unit_top.h"

// Directory from where data are read
char *input_dir = (char *) "input";

// Directory where results files are saved
char *output_dir = (char *) "output";

// Name of simulation tun
char *run_name = (char *) 0;

// Output data file
ofstream output_file;

// SoX format audio data file
ofstream sox_file;

// Latency measurement result
int max_latency;

// Function that opens output files

void open_results_files(char * run_name, char *directory)
{
  char filename[1024];

  if (run_name != NULL)
    {
      sprintf(filename, "%s/dsp_unit_%s_out.txt", directory, run_name);
      output_file.open(filename);
      
      if (!output_file.is_open())
	cout << "Unable to open simulation output file " << filename << endl;
      else
	cout << "Simulation output is saved to file " << filename << endl;

      sprintf(filename, "%s/dsp_unit_%s_out.dat", directory, run_name);
      sox_file.open(filename);
      
      if (!sox_file.is_open())
	cout << "Unable to open simulation output SoX file " << filename << endl;
      else
	cout << "Simulation output is saved in SoX format to file " << filename << endl;
      
      if (sox_file.is_open())
	{
	  sox_file << "; Sample Rate 48000"  << endl;
	  sox_file << "; Channels 4"  << endl;
	}
    }
}

// Function that closes output files
void close_results_files()
{
  if (output_file.is_open())
    output_file.close();
  
  if (sox_file.is_open())
    sox_file.close();
}


/////////////////////////////////////////////////////////////////////////////////////////////////////
//
// SystemC sc_main
//
/////////////////////////////////////////////////////////////////////////////////////////////////////

int sc_main( int argc, char *argv[] )
{

  // Normal SystemC simulation
  dsp_unit_top *dsp_unit_top_inst = new dsp_unit_top("dsp_unit_top_inst");

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


  open_results_files(run_name, output_dir);
  sc_start();
  close_results_files();
  cout << "SIMULATION STOPPED AT TIME = " << sc_time_stamp() << endl;
  cout << "--------------------------------------------------------------------------------" << endl;
  cout << "Maximum latency = " << max_latency << endl;
  cout << "--------------------------------------------------------------------------------" << endl;

  return 0;  
}



