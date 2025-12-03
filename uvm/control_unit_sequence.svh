///////////////////////////////////////////////////////////
// control_unit_sequence
///////////////////////////////////////////////////////////

class control_unit_sequence extends uvm_sequence #(apb_transaction);
      `uvm_object_utils(control_unit_sequence)

   //-------------------------------------------------------- 
   // Member functions
   //--------------------------------------------------------
	
   function new (string name = "");
      super.new(name);
   endfunction

   
   task body;

      /////////////////////////////////////////////////////////////////////
      // Variable declarations
      /////////////////////////////////////////////////////////////////////      

      uvm_event irq_event;  // Event to signal interrupts
      int stream_wdata = 1;  // Data to write into the registers (starting from 1)
      int reg_address;       // Address for register writes
      int buffer = 0;        // Toggle between two buffers
      apb_transaction apb_write_tx;
      apb_transaction apb_read_tx;

      /////////////////////////////////////////////////////////////////////      
      // Executable code
      /////////////////////////////////////////////////////////////////////

       reset_test_stats;
      irq_event = uvm_event_pool::get_global("irq_out");
      apb_write_tx = apb_transaction::type_id::create("apb_write_tx");
      apb_read_tx = apb_transaction::type_id::create("apb_read_tx");

 // === Phase 1: DSP Register Config ===
     $info("Task 1: Writing random data to DSP_REGS region");
      for(int i = 0; i < DSP_REGISTERS; ++i) begin
         reg_address = DSP_REGS_START_ADDRESS + i * 4;
         apb_write_tx.addr = reg_address;
         apb_write_tx.data = $urandom();
         apb_write_tx.write_mode = 1;
         start_item(apb_write_tx);
         finish_item(apb_write_tx);
      end
      update_test_stats;

      // === Phase 2: FIFO Initial Fill ===
     $info("Task 2: Initializing stream_wdata = 1");
      stream_wdata = 1;

    
         // Write to LEFT FIFO
         $info("Task 3: Writing to FIFOs");
      for(int i = 0; i < AUDIO_FIFO_SIZE; ++i) begin
         apb_write_tx.addr = LEFT_FIFO_ADDRESS + i * 4;
         apb_write_tx.data = stream_wdata++;
         apb_write_tx.write_mode = 1;
         start_item(apb_write_tx);
         finish_item(apb_write_tx);

         // Write to RIGHT FIFO
        apb_write_tx.addr = RIGHT_FIFO_ADDRESS + i * 4;
         apb_write_tx.data = stream_wdata++;
         apb_write_tx.write_mode = 1;
         start_item(apb_write_tx);
         finish_item(apb_write_tx);
      end
      update_test_stats;

      // === Phase 3: Configuration and Start ===
      // Enable DSP filter

	$info("Task 4: Writing to CFG_REG to enable the filter");
      apb_write_tx.addr = CFG_REG_ADDRESS;
      apb_write_tx.data = 32'h00000001;
      apb_write_tx.write_mode = 1;
      start_item(apb_write_tx);
      finish_item(apb_write_tx);
      update_test_stats;

      // Send CMD_CFG
      $info("Task 5: Writing CMD_CFG to CMD_REG");
      apb_write_tx.addr = CMD_REG_ADDRESS;
      apb_write_tx.data = CMD_CFG;
      apb_write_tx.write_mode = 1;
      start_item(apb_write_tx);
      finish_item(apb_write_tx);
      update_test_stats;

      // Set max playback level
   
	$info("Task 6: Writing LEVEL_REG");
      apb_write_tx.addr = LEVEL_REG_ADDRESS;
      apb_write_tx.data = 32'hFFFFFFFF;
      apb_write_tx.write_mode = 1;
      start_item(apb_write_tx);
      finish_item(apb_write_tx);
      update_test_stats;

      // Send CMD_LEVEL
      $info("Task 7: Writing CMD_LEVEL to CMD_REG");
      apb_write_tx.addr = CMD_REG_ADDRESS;
      apb_write_tx.data = CMD_LEVEL;
      apb_write_tx.write_mode = 1;
      start_item(apb_write_tx);
      finish_item(apb_write_tx);
      update_test_stats;

      // Send CMD_START
      $info("Task 8: Writing CMD_START to CMD_REG");
      apb_write_tx.addr = CMD_REG_ADDRESS;
      apb_write_tx.data = CMD_START;
      apb_write_tx.write_mode = 1;
      start_item(apb_write_tx);
      finish_item(apb_write_tx);

      // === Phase 4: IRQ Loop - 4 Playback Cycles ===
      stream_wdata = 1;
      repeat(4) begin
         irq_event.wait_trigger();
         #1000ns;

         // Refill FIFOs
    $info("Task 9: Filling FIFOs again");

         for(int i = 0; i < AUDIO_FIFO_SIZE; ++i) begin
            apb_write_tx.addr = LEFT_FIFO_ADDRESS + i * 4;
            apb_write_tx.data = stream_wdata++;
            apb_write_tx.write_mode = 1;
            start_item(apb_write_tx);
            finish_item(apb_write_tx);

            apb_write_tx.addr = RIGHT_FIFO_ADDRESS + i * 4;
            apb_write_tx.data = stream_wdata++;
            apb_write_tx.write_mode = 1;
            start_item(apb_write_tx);
            finish_item(apb_write_tx);
         end
         update_test_stats;

         // Send CMD_IRQACK
      apb_write_tx.addr = CMD_REG_ADDRESS;
         apb_write_tx.data = CMD_IRQACK;
         apb_write_tx.write_mode = 1;
         start_item(apb_write_tx);
         finish_item(apb_write_tx);
      end
      update_test_stats;

      #10us;

      // === Phase 5: Stop and Cleanup ===
     $info("Task 11: Writing CMD_STOP to CMD_REG");
      apb_write_tx.addr = CMD_REG_ADDRESS;
      apb_write_tx.data = CMD_STOP;
      apb_write_tx.write_mode = 1;
      start_item(apb_write_tx);
      finish_item(apb_write_tx);
      update_test_stats;

        $info("Task 12: Writing CMD_CLR to CMD_REG");
      apb_write_tx.addr = CMD_REG_ADDRESS;
      apb_write_tx.data = CMD_CLR;
      apb_write_tx.write_mode = 1;
      start_item(apb_write_tx);
      finish_item(apb_write_tx);
      update_test_stats;


      // Final delay to allow clean stop
      $info("Task 13: Waiting for 10us to give CMD_CLR time to work");
      #10us;

      
   endtask

   //----------------------------------------------------------------
   // Notice! This sequence can only access the control_unit's APB
   //         bus ports. Therefore the test program functions that need
   //         access to other ports are not implemented.
   //-----------------------------------------------------------------

endclass 
