///////////////////////////////////////////////////////////
//
// Class: apb_sequence
//
///////////////////////////////////////////////////////////

class apb_sequence extends uvm_sequence #(apb_transaction);
      `uvm_object_utils(apb_sequence)

   function new (string name = "");
      super.new(name);
   endfunction

   task body;
      apb_sequence_config seq_config;
      int test_cycles = 100;
      int queue_index;
      apb_transaction write_queue[$];
      
      if (uvm_config_db #(apb_sequence_config)::get(null, get_full_name(), "apb_sequence_config", seq_config))
	begin
	   test_cycles = seq_config.apb_test_cycles;
	   `uvm_info("",$sformatf("apb_sequence configured to run for %d test cycles", test_cycles), UVM_NONE);	   
	end
   
      repeat(test_cycles)
	begin
	   apb_transaction write_tx;
	   apb_transaction read_tx;	      
	   int unsigned random_value;
	   
	   random_value = $urandom_range(1,3);	      
	   for (int i=0; i < random_value; ++i)
	     begin
		write_tx = apb_transaction::type_id::create("write_tx");
		assert( write_tx.randomize() );
		write_tx.write_mode = '1;	      
		write_tx.fail = 0;
		write_queue.push_back(write_tx);
		start_item(write_tx);
		finish_item(write_tx);
	     end

	   random_value = $urandom_range(1,3);	      
	   for (int i=0; i < random_value; ++i)
	     begin
		read_tx = apb_transaction::type_id::create("read_tx");	      	      
		assert( read_tx.randomize() );	      
		queue_index = $urandom_range( 0, (write_queue.size()-1) );
		read_tx.addr = write_queue[queue_index].addr;
		read_tx.write_mode = '0;
		read_tx.fail = '0;	      
		start_item(read_tx);
		finish_item(read_tx);
	     end
	end
   endtask

endclass 
