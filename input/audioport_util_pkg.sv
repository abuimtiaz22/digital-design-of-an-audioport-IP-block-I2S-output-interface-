`include "audioport.svh"

///////////////////////////////////////////////////////////////////////////////
//
// audioport_util_pkg.sv: Resources for testbenches.
//
///////////////////////////////////////////////////////////////////////////////

package audioport_util_pkg;

   import apb_pkg::*;
   import audioport_pkg::*;   
   

`ifndef SYNTHESIS

   int 			    tests_passed;
   int 			    tests_failed;
   int 			    assertions_failed;
`ifndef FINISH_ON_ERROR
   int                      finish_on_error = 0;
`else
   int                      finish_on_error = 1;
`endif
   localparam realtime 	    WATCHDOG_TIME = 20.0ms;
   
   function void assert_error(string name);
`ifndef RTL_VERIF
      ++assertions_failed;
      $error(name);
      if (finish_on_error) $finish;
`endif
   endfunction

   function void reset_test_stats;
`ifndef RTL_VERIF
      tests_passed = 0;
      tests_failed = 0;
      assertions_failed = 0;
`endif
   endfunction
   
   function void update_test_stats;
`ifndef RTL_VERIF
      if (assertions_failed == 0)
	++tests_passed;
      else
	++tests_failed;      
      assertions_failed = 0;
`endif
   endfunction

   class audio_sample;
      logic [23:0] left;
      logic [23:0] right;      
   endclass
   typedef audio_sample audio_sample_t;
   typedef audio_sample_t test_data_queue_t[$];
   
   localparam real INTERRUPT_LATENCY = 5us;
   const string    FILTER_TAPS_FILE = "";
   
   function void save_test_parameters(string path);
      int 	   file;
      file = $fopen(path, "w");      
      $fdisplay(file, "-----------------------------------------------------------------------------------------------");
      $fdisplay(file, "DT3 PROJECT: SIMULATION PARAMATER VALUES:");
      $fdisplay(file, "-----------------------------------------------------------------------------------------------");      
      $fdisplay(file, "Clock periods:");
      $fdisplay(file, "        clk                    %10f ns", CLK_PERIOD);
      $fdisplay(file, "        mclk                   %10f ns", MCLK_PERIOD);            
      $fdisplay(file, "DESIGN PARAMETERS:");
      $fdisplay(file, "        FILTER_TAPS            %10d", FILTER_TAPS);
      $fdisplay(file, "        AUDIO_FIFO_SIZE        %10d", AUDIO_FIFO_SIZE);
      $fdisplay(file, "REGISTERS:");
      $fdisplay(file, "        DSP_REGISTERS          %10d", DSP_REGISTERS);
      $fdisplay(file, "        AUDIOPORT_REGISTERS    %10d", AUDIOPORT_REGISTERS);
      $fdisplay(file, "INTERNAL REGISTER INDICES (DECIMAL):");
      $fdisplay(file, "        CMD_REG_INDEX          %10d", CMD_REG_INDEX);
      $fdisplay(file, "        STATUS_REG_INDEX       %10d", STATUS_REG_INDEX);      
      $fdisplay(file, "        LEVEL_REG_INDEX        %10d", LEVEL_REG_INDEX);
      $fdisplay(file, "        CFG_REG_INDEX          %10d", CFG_REG_INDEX);
      $fdisplay(file, "        DSP_REGS_START_INDEX   %10d", DSP_REGS_START_INDEX);
      $fdisplay(file, "        DSP_REGS_END_INDEX     %10d", DSP_REGS_END_INDEX);
      $fdisplay(file, "        LEFT_FIFO_INDEX        %10d", LEFT_FIFO_INDEX);
      $fdisplay(file, "        RIGHT_FIFO_INDEX       %10d", RIGHT_FIFO_INDEX);            
      $fdisplay(file, "REGISTER APB ADDRESSES (HEX):");
      $fdisplay(file, "        AUDIOPORT_START_ADDRESS  %8h", AUDIOPORT_START_ADDRESS);
      $fdisplay(file, "        AUDIOPORT_END_ADDRESS    %8h", AUDIOPORT_END_ADDRESS);      
      $fdisplay(file, "        CMD_REG_ADDRESS          %8h", CMD_REG_ADDRESS);
      $fdisplay(file, "        STATUS_REG_ADDRESS       %8h", STATUS_REG_ADDRESS);      
      $fdisplay(file, "        LEVEL_REG_ADDRESS        %8h", LEVEL_REG_ADDRESS);
      $fdisplay(file, "        CFG_REG_ADDRESS          %8h", CFG_REG_ADDRESS);
      $fdisplay(file, "        DSP_REGS_START_ADDRESS   %8h", DSP_REGS_START_ADDRESS);
      $fdisplay(file, "        DSP_REGS_END_ADDRESS     %8h", DSP_REGS_END_ADDRESS);
      $fdisplay(file, "        LEFT_FIFO_ADDRESS        %8h", LEFT_FIFO_ADDRESS);
      $fdisplay(file, "        RIGHT_FIFO_ADDRESS       %8h", RIGHT_FIFO_ADDRESS);            
      $fdisplay(file, " APB CONFIGURATION (HEX):");
      $fdisplay(file, "        DUT_START_ADDRESS        %8h", DUT_START_ADDRESS);
      $fdisplay(file, "        DUT_END_ADDRESS          %8h", DUT_END_ADDRESS);      
      $fdisplay(file, "        APB_START_ADDRESS        %8h", APB_START_ADDRESS);
      $fdisplay(file, "        APB_END_ADDRESS          %8h", APB_END_ADDRESS);      
      $fdisplay(file, " clk CYCLES PER SAMPLE:");
      $fdisplay(file, "        CLK_DIV_48000          %10d", CLK_DIV_48000);
      $fdisplay(file, " CDC PARAREMETRS (INT):");
      $fdisplay(file, "        CDC_DATASYNC_INTERVAL  %10d", CDC_DATASYNC_INTERVAL);
      $fdisplay(file, "        CDC_DATASYNC_LATENCY   %10d", CDC_DATASYNC_LATENCY);      
      $fdisplay(file, "        CDC_BITSYNC_INTERVAL   %10d", CDC_BITSYNC_INTERVAL);
      $fdisplay(file, "        CDC_BITYNC_LATENCY     %10d", CDC_BITSYNC_LATENCY);      
      $fdisplay(file, "        CDC_PULSESYNC_INTERVAL %10d", CDC_PULSESYNC_INTERVAL);
      $fdisplay(file, "        CDC_PULSESYNC_LATENCY  %10d", CDC_PULSESYNC_LATENCY);      
      $fdisplay(file, " dsp_unit PARAREMETERS:");
      $fdisplay(file, "        DSP_UNIT_MAX_LATENCY   %10d", DSP_UNIT_MAX_LATENCY);

      $fdisplay(file, "-----------------------------------------------------------------------------------------------");
      $fclose(file);      

   endfunction
      
   localparam logic signed [31:0] COEFF_SCALING = 32'h7fffffff;
   localparam real 		  M_PI = 3.14159265359;
   
   function automatic int read_filter_taps (ref logic [2*FILTER_TAPS-1:0][31:0] dsp_regs);
      begin
	 int file;
	 string line;
	 int 	lines;
	 real coeff;

	 file = 0;
	 
	 if (FILTER_TAPS_FILE.len() > 0)
	   file = $fopen(FILTER_TAPS_FILE, "r");

	 if (file == 0)
    	   begin
	      real B;
	      $info("No file specified. Generating default coefficients.\n");	      
	      for (int f = 0; f < 2; ++f)
		begin
		   case (f)
		     0:
		       B =0.35;
		     1:
		       B =0.25;
		     2:
		       B =0.15;
		     3:
		       B = 0.05;
		   endcase 
		   
		   for (int i=0; i < FILTER_TAPS; ++i)
		     begin
			int x;
			real sinc;
			x = (i-FILTER_TAPS/2);
			if (x == 0)
			  dsp_regs[f*FILTER_TAPS+i] = 0.5*COEFF_SCALING;
			else
			  dsp_regs[f*FILTER_TAPS+i] = COEFF_SCALING*B*$sin(2*B*M_PI*x)/(2*B*M_PI*x);
		     end
		end
	      
	      return 0;
    	   end
	 else
	   begin
	      lines = 0;
	      
	      while($fgets(line, file) != 0 && lines < 2*FILTER_TAPS)
		begin
		   if ($sscanf(line, "%f", coeff) != 1)
		     $error("Filter tap file format error (expected 1 floating point value)\n");
		   else
		     dsp_regs[lines] = ((2**31)-1) * coeff;
		   ++lines;
		end
	      $fclose(file);
	      return lines;
	   end // else: !if(file == 0)
      end
      
   endfunction


`endif
   
endpackage
   
