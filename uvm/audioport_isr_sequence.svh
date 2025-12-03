///////////////////////////////////////////////////////////
//
// audioport_isr_sequence
//
///////////////////////////////////////////////////////////

class audioport_isr_sequence extends audioport_isr_sequence_base;
      `uvm_object_utils(audioport_isr_sequence)

   function new (string name = "");
      super.new(name);
   endfunction

   task body;
      audio_sample_t sample;
      apb_transaction write_tx;
      audioport_sequence_config seq_config;
      int current_abuf = 0;
      write_tx = apb_transaction::type_id::create("write_tx");

      // Take over sequencer
      m_sequencer.grab(this);

      // Get sequence config object to find out current buffer number
      if (uvm_config_db #(audioport_sequence_config)::get(null, get_full_name(), "audioport_sequence_config", seq_config))
	begin
	   current_abuf = seq_config.current_abuf;
	end
      else
	uvm_report_error("audioport_isr_sequence.body:", "Could not get config data from uvm_config_db");

      // Mimic interrupt latency
      #(INTERRUPT_LATENCY);

      // Fill FIFOS
      for(int unsigned i=0; i < AUDIO_FIFO_SIZE; ++i)
	begin
	   sample = seq_config.get_test_data();	
	   write_tx.addr = LEFT_FIFO_ADDRESS;
	   write_tx.data = sample.left;
	   write_tx.write_mode = '1;	      
	   write_tx.fail = 0;
	   start_item(write_tx);
	   finish_item(write_tx);
	   
	   write_tx.addr = RIGHT_FIFO_ADDRESS;
	   write_tx.data = sample.right;
	   write_tx.write_mode = '1;	      
	   write_tx.fail = 0;
	   start_item(write_tx);
	   finish_item(write_tx);
	end

      ////////////////////////////////////////////////////////////////
      // Acknowledge interrupt
      ////////////////////////////////////////////////////////////////
      
      write_tx.addr = CMD_REG_ADDRESS;
      write_tx.data = CMD_IRQACK;
      write_tx.write_mode = '1;	      
      write_tx.fail = 0;
      start_item(write_tx);
      finish_item(write_tx);
      
      // Update buffer number and write back to database
      if (current_abuf == 0)
	seq_config.current_abuf = 1;
      else
	seq_config.current_abuf = 0;
      uvm_config_db #(audioport_sequence_config)::set(null, "*", "audioport_sequence_config", seq_config);
      
      // Release sequencer
      m_sequencer.ungrab(this);
   endtask
endclass
