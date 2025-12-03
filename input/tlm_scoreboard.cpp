#include "tlm_scoreboard.h"

#include <iostream>
#include <iomanip>
using namespace std;

extern ofstream output_file;

void tlm_scoreboard::thread()
{
  sample_number = 0;
  while(1)
    {
      audio_out = i2s_fifo.read();
      audio_in = audio_fifo.read();

      if (output_file.is_open())
	{
	  output_file << setw(10) << sample_number;
	  output_file << setw(12) << audio_in.left << setw(12) << audio_in.right << setw(12) << audio_out.left << setw(12) << audio_out.right;
	  output_file << endl;
	}
      else
	{
	  cout << setw(10) << sample_number;
	  cout << setw(12) << audio_in.left << setw(12) << audio_in.right << setw(12) << audio_out.left << setw(12) << audio_out.right;
	  cout << endl;
	}
      ++sample_number;
    }
}


void tlm_scoreboard::clear()
{
  audio_data_t audio;
  audio_data_t i2s;
  while(1)
    {
      audio_data_t tmp;
      wait(scoreboard_reset);
      while (audio_fifo.nb_read(tmp));
      while (i2s_fifo.nb_read(tmp));
    }
}


