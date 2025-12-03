///////////////////////////////////////////////////////////
//
// audioport_comparator
//
// This component receives I2S transactions from the i2s_agent
// through its analysis export, then gets reference data values
// from the audioport_predictor through its get port, and
// writes both results to a text file.
//
///////////////////////////////////////////////////////////
   
class audioport_comparator extends uvm_component;
   `uvm_component_utils(audioport_comparator)
     
   uvm_analysis_imp #(i2s_transaction, audioport_comparator) audio_analysis_export;
   uvm_nonblocking_get_port #(i2s_transaction) predictor_get_port;
   int file;
   int m_samples = 0;
   int m_errors = 0;
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
      audio_analysis_export = new("audio_analysis_export", this);      
      predictor_get_port = new("predictor_get_port", this);
   endfunction 

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      file = $fopen("results/audioport_uvm_comparator_out.txt", "w");
   endfunction
   
   function void write(i2s_transaction t);
      i2s_transaction dut_tx = t;
      i2s_transaction ref_tx;      
      int tmp;
      
      tmp = predictor_get_port.try_get(ref_tx);

      if (ref_tx != null)
	begin 
	   ++m_samples;
	   
	   ia_audioport_comparator: assert((dut_tx.audio_data[0] == ref_tx.audio_data[0]) &&
		  (dut_tx.audio_data[1] == ref_tx.audio_data[1]))	     
	     else
	       begin
		  assert_error("ia_audioport_comparator");		  
		  $info("%10f: audioport_comparator: DUT=%11d%11d  REF=%11d%11d", 
			 $realtime/1000000000.0, 
			 signed'(dut_tx.audio_data[0]), signed'(dut_tx.audio_data[1]), 
			 signed'(ref_tx.audio_data[0]), signed'(ref_tx.audio_data[1]));
		  ++m_errors;
	       end
`ifdef DEBUG
	   $display("%10f: audioport_comparator: DUT=%11d%11d  REF=%11d%11d", 
		    $realtime/1000000000.0, 
		    signed'(dut_tx.audio_data[0]), signed'(dut_tx.audio_data[1]), 
		    signed'(ref_tx.audio_data[0]), signed'(ref_tx.audio_data[1]));
`endif
	   $fwrite(file, "%10f", $realtime/1000000000.0);
	   $fwrite(file, "%11d%11d", signed'(dut_tx.audio_data[0]), signed'(dut_tx.audio_data[1]));
	   $fwrite(file, "%11d%11d", signed'(ref_tx.audio_data[0]), signed'(ref_tx.audio_data[1]));
	   $fwrite(file, "\n");
	end // if (ref_tx != null)
      else
	begin
`ifdef DEBUG
	   $display("ref_ex == null in audioport_comparator");
`endif
	end
   endfunction

   function void report_phase( uvm_phase phase );
      uvm_report_info("audioport_comparator", $sformatf("%d samples compared, %d differences detected", m_samples, m_errors));
   endfunction
   
   
endclass
