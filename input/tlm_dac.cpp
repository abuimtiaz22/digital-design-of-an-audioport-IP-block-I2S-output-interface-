#include "tlm_dac.h"

#include <iostream>
#include <iomanip>
using namespace std;

// ----------------------------------------------------------------------------------
// i2c_sipo: I2S serial receiver
// ----------------------------------------------------------------------------------

void tlm_dac::i2s_sipo()
{
  // Shift registers
  
  srg = 0;
  lctr = 0;
  rctr = 0;

  wait();

  while(1)
    {
      bool sck_rise;
      lctr = 0;
      rctr = 0;
      do
	{
	  wait();
	  lctr = lctr+1;
	  srg = (srg.range(46, 0), sdo.read() );
	} while (!(ws.read() == 1));
      
      do
	{
	  wait();
	  rctr = rctr+1;
	  srg = (srg.range(46, 0), sdo.read() );
	}  while (!(ws.read() == 0));
      
      i2s_sample.left = srg.range(47,24);
      i2s_sample.right = srg.range(23,0);
      i2s_fifo.write(i2s_sample);
    }
}



