///////////////////////////////////////////////////////////
//
// audioport_master_sequence
//
///////////////////////////////////////////////////////////

class audioport_master_sequence extends uvm_sequence #(apb_transaction);
      `uvm_object_utils(audioport_master_sequence)
   
   function new (string name = "");
      super.new(name);
   endfunction

   task body;
      audioport_main_sequence_base main_seq;
      audioport_isr_sequence_base isr_seq;      
      uvm_event irq_event;

      main_seq = audioport_main_sequence_base::type_id::create("main_seq");
      isr_seq = audioport_isr_sequence_base::type_id::create("isr_seq");            
      irq_event = uvm_event_pool::get_global("irq_out");

      fork
	 main_seq.start(m_sequencer); // Start main sequence
	 begin // In parallel: start interrut handling process loop
	    forever 
	      begin
		 irq_event.wait_trigger(); // Wait for interrupt event
		 isr_seq.start(m_sequencer); // Run interrupt service sequence once
	      end
	 end
      join_any
      disable fork; // If main sequence end, end everything

   endtask

endclass
