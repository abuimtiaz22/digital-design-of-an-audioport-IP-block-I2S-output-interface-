#include "dsp_unit_top.h"

void dsp_unit_top::reset_thread() 
{
   rst_n.write(false);
   wait(1);
   rst_n.write(true);
 }
