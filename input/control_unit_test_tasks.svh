//////////////////////////////////////////////////////////////////////////////////////
task reset_test;
//////////////////////////////////////////////////////////////////////////////////////   
   @(negedge clk);   
   req_in = '0;
   apb.init;
   rst_n = '1;   
   @(negedge clk);   
   rst_n = '0;
   @(negedge clk);
   @(negedge clk);   
   rst_n = '1;
endtask

//////////////////////////////////////////////////////////////////////////////////////
task apb_test;
//////////////////////////////////////////////////////////////////////////////////////
   
 // Print a message to user   
   $info("apb_test");

   // 1.
   reset_test;
   req_in = '0;
   
   // 2
   addr = CMD_REG_ADDRESS;
   wdata = CMD_NOP;
   apb.write(addr, wdata, wfail);
   apb.read(addr, rdata, rfail);   
   ia_apb_test1: assert (!wfail && !rfail) else 
     assert_error("ia_apb_test1");  // See assert_error in audioport_pkg.sv

   //3 
   repeat(10)
     @(posedge clk);
   
   // 4
   addr = AUDIOPORT_START_ADDRESS-4;
   wdata = $urandom;
   apb.write(addr, wdata, wfail);
   apb.read(addr, rdata, rfail);   

   update_test_stats; // See audioport_pkg.sv
    
endtask

//////////////////////////////////////////////////////////////////////////////////////
task address_decoding_test;
//////////////////////////////////////////////////////////////////////////////////////   

 $info("address_decoding_test");
// 1. Execute reset_test
   reset_test;
req_in = '0;

   // 2. Execute a read access to all valid addresses in range AUDIOPORT_START_ADDRESS : AUDIOPORT_END_ADDRESS
   for (addr = AUDIOPORT_START_ADDRESS; addr <= AUDIOPORT_END_ADDRESS; addr += 4) begin
      apb.read(addr, rdata, rfail);
assert(!rfail) else assert_error("AUDIIOPORT_START_ADDRESS to AUDIOPORT_END_ADDRESS read failed.");
   end

   // 3. Execute a read access to an address outside audioport range
   addr = AUDIOPORT_END_ADDRESS + 4;
   apb.read(addr, rdata, rfail);
assert(!rfail) else assert_error("AUDIOPORT_END_ADDRESS read failed.");

   update_test_stats; // Update test statistics
   
endtask
//////////////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////////////
task register_test;
//////////////////////////////////////////////////////////////////////////////////////
  
int addr;
int A; // Base value (last digit of student number)

 $info("register_test");

   // 1. Execute reset_test
   reset_test;
req_in = '0;

   // 2. Write and read data to/from all valid addresses
A=3;
   for (addr = AUDIOPORT_START_ADDRESS; addr <= AUDIOPORT_END_ADDRESS; addr += 4) begin
       wdata = A + (addr - AUDIOPORT_START_ADDRESS) / 4; // Compute write data

              apb.write(addr, wdata, wfail);  // Write data
              apb.read(addr, rdata, rfail);  // Read data
       ia_register_test_1: assert (!rfail && (rdata == wdata)) else 
           assert_error($sformatf("Read failed or data mismatch at address %h", addr));
   end

   // Update test statistics
   update_test_stats;
endtask

//////////////////////////////////////////////////////////////////////////////////////
task fifo_bus_test;
//////////////////////////////////////////////////////////////////////////////////////
   $info("fifo_bus_test");
   
endtask

//////////////////////////////////////////////////////////////////////////////////////
task prdata_off_test;
//////////////////////////////////////////////////////////////////////////////////////

   logic PSEL; // Signal to indicate peripheral selection
   int addr;
   logic [31:0] PRDATA;

   $info("prdata_off_test");

   // 1. Execute reset_test
   reset_test;
   req_in = '0;

   wdata = 32'h293; //Last three digit of student ID

   // 2. Fill PRDATA in audioport registers, left FIFO, right FIFO
   for (int i = 0; i < AUDIOPORT_REGISTERS; i++) begin
      addr = AUDIOPORT_START_ADDRESS + i * 4;  // Calculate the register address
      
      apb.write(addr, wdata, wfail);  // Write data
      assert(!wfail) else 
          assert_error($sformatf("Write to AUDIOPORT_REGISTERS failed at index %0d", i));
   end

  
   for (int i = 0; i < AUDIO_FIFO_SIZE; i++) begin
      addr = LEFT_FIFO_ADDRESS;
      
      apb.write(addr, wdata, wfail);  // Write data
      assert(!wfail) else 
          assert_error($sformatf("Write to LEFT_FIFO_ADDRESS failed at iteration %0d", i));
   end

   
   for (int i = 0; i < AUDIO_FIFO_SIZE; i++) begin
      addr = RIGHT_FIFO_ADDRESS;
      
      apb.write(addr, wdata, wfail);  // Write data
      assert(!wfail) else 
          assert_error($sformatf("Write to RIGHT_FIFO_ADDRESS failed at iteration %0d", i));
   end




   // 3.1 Inside AUDIOPORT_REGISTER range
   for (int i = 0; i < AUDIOPORT_REGISTERS; i++) begin
       addr = AUDIOPORT_START_ADDRESS + i * 4;
       PSEL = 1; // Enable peripheral selection
       apb.read(addr, PRDATA, rfail);
       ia_prdata_test_1: assert (PRDATA == wdata) else
           assert_error($sformatf("PRDATA mismatch in AUDIOPORT_REGISTER range at address %h", addr));
   end

   // 3.2 For LEFT_FIFO_INDEX
   PSEL = 1; // Enable peripheral selection
   apb.read(LEFT_FIFO_ADDRESS, PRDATA, rfail);
   ia_prdata_test_2: assert (PRDATA == wdata) else
       assert_error($sformatf("PRDATA mismatch for LEFT_FIFO_ADDRESS"));

   // 3.3 For RIGHT_FIFO_INDEX
   PSEL = 1; // Enable peripheral selection
   apb.read(RIGHT_FIFO_ADDRESS, PRDATA, rfail);
   ia_prdata_test_3: assert (PRDATA == wdata) else
       assert_error($sformatf("PRDATA mismatch for RIGHT_FIFO_ADDRESS"));

   // 3.4 Outside AUDIOPORT range
   PSEL = 0; // Disable peripheral selection
   apb.read(AUDIOPORT_END_ADDRESS + 4, PRDATA, rfail);
   ia_prdata_test_4: assert (PRDATA == 0) else
       assert_error($sformatf("PRDATA is not 0 or PSEL is high for out-of-range address"));

   // Update test statistics
   update_test_stats();

endtask

//////////////////////////////////////////////////////////////////////////////////////
task cmd_start_stop_test;
//////////////////////////////////////////////////////////////////////////////////////   
   $info("cmd_start_stop_test");

endtask

//////////////////////////////////////////////////////////////////////////////////////
task status_test;
//////////////////////////////////////////////////////////////////////////////////////   
   $info("status_test");

endtask

//////////////////////////////////////////////////////////////////////////////////////   
task cmd_clr_test;
//////////////////////////////////////////////////////////////////////////////////////      
  $info("cmd_clr_test");
// 1. Execute reset_test to initialize the system
   reset_test;
   req_in = '0;

   // 2. Write the value CBA (e.g., 293) AUDIO_FIFO_SIZE times to both LEFT_FIFO_ADDRESS and RIGHT_FIFO_ADDRESS
   for (int i = 0; i < AUDIO_FIFO_SIZE; i++) begin
       wdata = 293; // Replace with the required CBA value
       apb.write(LEFT_FIFO_ADDRESS, wdata, wfail); // Write to LEFT_FIFO_ADDRESS
assert(!wfail) else assert_error("LEFT_FIFO_ADDRESS write failed.");
       apb.write(RIGHT_FIFO_ADDRESS, wdata, wfail); // Write to RIGHT_FIFO_ADDRESS
assert(!wfail) else assert_error("RIGHT_FIFO_ADDRESS write failed.");
       
   end

   // 3. Write the command code CMD_CLR to CMD_REG_ADDRESS
   apb.write(CMD_REG_ADDRESS, CMD_CLR, wfail);
assert(!wfail) else assert_error("CMD_REG_ADDRESS for CMD_CLR write failed.");
   

   // 4. Read AUDIO_FIFO_SIZE times from both LEFT_FIFO_ADDRESS and RIGHT_FIFO_ADDRESS
   for (int i = 0; i < AUDIO_FIFO_SIZE; i++) begin
       apb.read(LEFT_FIFO_ADDRESS, rdata, rfail); // Read from LEFT_FIFO_ADDRESS
       ia_cmd_clr_test_1: assert (!rfail && rdata == 0) else
           assert_error($sformatf("Read failed or data mismatch at LEFT_FIFO_ADDRESS, iteration %0d", i));

       apb.read(RIGHT_FIFO_ADDRESS, rdata, rfail); // Read from RIGHT_FIFO_ADDRESS
       ia_cmd_clr_test_2: assert (!rfail && rdata == 0) else
           assert_error($sformatf("Read failed or data mismatch at RIGHT_FIFO_ADDRESS, iteration %0d", i));
   end

   // Update test statistics
   update_test_stats;
endtask
//////////////////////////////////////////////////////////////////////////////////////
task cmd_cfg_test;
//////////////////////////////////////////////////////////////////////////////////////   
$info("cmd_cfg_test");
  // 1. Execute reset_test to initialize the system
   reset_test;
   req_in = '0;

   // 2. Write the command code CMD_CFG to CMD_REG_ADDRESS
   wdata = CMD_CFG; // Command code
   apb.write(CMD_REG_ADDRESS, wdata, wfail);
assert(!wfail) else assert_error("CMD_CFG write failed.");
   

   // Update test statistics
   update_test_stats;
endtask

//////////////////////////////////////////////////////////////////////////////////////
task cmd_level_test;
//////////////////////////////////////////////////////////////////////////////////////   
 $info("cmd_level_test");
 // 1. Execute reset_test to initialize the system
   reset_test;
   req_in = '0;

   // 2. Write the command code CMD_LEVEL to CMD_REG_ADDRESS
   wdata = CMD_LEVEL; // Command code
   apb.write(CMD_REG_ADDRESS, wdata, wfail);
assert(!wfail) else assert_error("CMD_LEVEL write failed.");
   

   // Update test statistics
   update_test_stats;
endtask
//////////////////////////////////////////////////////////////////////////////////////
task clr_error_test;
//////////////////////////////////////////////////////////////////////////////////////   
   $info("clr_error_test");

endtask

//////////////////////////////////////////////////////////////////////////////////////
task req_tick_test;
//////////////////////////////////////////////////////////////////////////////////////   
  $info("req_tick_test");
   // 1. Execute reset_test to initialize the system
   reset_test;
   req_in = '0;

   // 2. Fork two processes: apb_control and req_writer
   fork
      // apb_control process
      begin
         // 2-1. Write CMD_START to CMD_REG_ADDRESS and wait for 50 clock cycles
         apb.write(CMD_REG_ADDRESS, CMD_START, wfail);
assert(!wfail) else assert_error("CMD_START write failed.");

         
         repeat (50) @(posedge clk);

         // 2-2. Write CMD_STOP to CMD_REG_ADDRESS and wait for 50 clock cycles
         apb.write(CMD_REG_ADDRESS, CMD_STOP, wfail);
assert(!wfail) else assert_error("CMD_STOP write failed.");

         
         repeat (50) @(posedge clk);
      end

      // req_writer process
      begin : req_writer
         wait (play_out); // Wait until play_out is asserted
         forever begin
            // Generate a req_in pulse every 10 clock cycles
            repeat (10) @(posedge clk);
            req_in = 1;
            @(posedge clk);
            req_in = 0;
           
   
       // Check with assertion that tick_out == 1 if play_out == 1, or 0 otherwise
                ia_req_tick_test_1: assert((play_out && tick_out==1) || (!play_out && tick_out==0)) else
                    assert_error($sformatf("tick_out assertion failed at time %0t. play_out: %0b, tick_out: %0b", $time, play_out, tick_out));
  
     
         end
      end
   join_any

   // 3. End processes with "disable fork"
   disable fork;

   // Update test statistics
   update_test_stats;
endtask

//////////////////////////////////////////////////////////////////////////////////////
task fifo_test;
//////////////////////////////////////////////////////////////////////////////////////   
   $info("fifo_test");   
endtask

//////////////////////////////////////////////////////////////////////////////////////
task irq_up_test;
//////////////////////////////////////////////////////////////////////////////////////   
   $info("irq_up_test");      

endtask

//////////////////////////////////////////////////////////////////////////////////////
task irq_down_test;
//////////////////////////////////////////////////////////////////////////////////////   
 

// Variable declaration
   logic irq_out_state;  

 
$info("irq_down_test");

  
   // 1. Execute reset_test to bring the control_unit into standby mode
   reset_test;
   req_in = '0;

   // 2. Fill FIFOs with AUDIO_FIFO_SIZE writes
   for (int i = 0; i < AUDIO_FIFO_SIZE; i++) begin
      apb.write(LEFT_FIFO_ADDRESS, $urandom, wfail);
      assert (!wfail) else 
assert_error($sformatf("Write to LEFT_FIFO_ADDRESS failed at iteration %0d", i));
        

      apb.write(RIGHT_FIFO_ADDRESS, $urandom, wfail);
      assert (!wfail) else 
assert_error($sformatf("Write to RIGHT_FIFO_ADDRESS failed at iteration %0d", i));
          
   end

   // 3. Write CMD_START to CMD_REG_ADDRESS
   apb.write(CMD_REG_ADDRESS, CMD_START, wfail);
   assert (!wfail) else 
       assert_error("Write CMD_START failed");

   // 4. Generate AUDIO_FIFO_SIZE req_in pulses
   for (int i = 0; i < AUDIO_FIFO_SIZE; i++) begin
      repeat (10) @(posedge clk);
      req_in = 1;
      @(posedge clk);
      req_in = 0;
   end

   // 5. Wait for two clock cycles
   repeat (2) @(posedge clk);

   // 6. Monitor irq_out and check if it's asserted
   irq.monitor(irq_out_state);
   ia_irq_down_test_1: assert (irq_out_state == 1) else 
       assert_error("irq_out did not assert as expected");

   // 7. Wait for 10 clock cycles
   repeat (10) @(posedge clk);

   // 8. Write CMD_IRQACK to CMD_REG_ADDRESS
   apb.write(CMD_REG_ADDRESS, CMD_IRQACK, wfail);
   

   // 9. Monitor irq_out and check if it's deasserted
   irq.monitor(irq_out_state);
   ia_irq_down_test_2: assert (irq_out_state == 0) else 
       assert_error("irq_out did not deassert after CMD_IRQACK");

   // 10. Repeat steps 1-9 using CMD_STOP
   reset_test;
   req_in = '0;
   for (int i = 0; i < AUDIO_FIFO_SIZE; i++) begin
      apb.write(LEFT_FIFO_ADDRESS, $urandom, wfail);
      apb.write(RIGHT_FIFO_ADDRESS, $urandom, wfail);
   end
   apb.write(CMD_REG_ADDRESS, CMD_START, wfail);
   for (int i = 0; i < AUDIO_FIFO_SIZE; i++) begin
      repeat (10) @(posedge clk);
      req_in = 1;
      @(posedge clk);
      req_in = 0;
   end
   repeat (2) @(posedge clk);
   irq.monitor(irq_out_state);
   ia_irq_down_test_3: assert (irq_out_state == 1) else 
       assert_error("irq_out did not assert as expected in CMD_STOP test");

   repeat (10) @(posedge clk);
   apb.write(CMD_REG_ADDRESS, CMD_STOP, wfail);
   assert (!wfail) else 
       assert_error("Write CMD_STOP failed");

   irq.monitor(irq_out_state);
   ia_irq_down_test_4: assert (irq_out_state == 0) else 
       assert_error("irq_out did not deassert after CMD_STOP");

   // Update test statistics
   update_test_stats;
endtask


//////////////////////////////////////////////////////////////////////////////////////
task performance_test;
//////////////////////////////////////////////////////////////////////////////////////   
   int 					    irq_counter;
   logic 				    irq_out_state;
   logic [23:0] 			    stream_wdata;
   logic [23:0] 			    stream_rdata;   
   int 					    cycle_counter;
   
   $info("performance_test");   

   // 1.
   reset_test;
   req_in = '0;

   // 2.
   stream_wdata = 1;
   irq_counter = 0;
   cycle_counter = 0;
   
   // 3.
   for (int i=0; i < AUDIO_FIFO_SIZE; ++i)
     begin
	wdata = stream_wdata;
	apb.write(LEFT_FIFO_ADDRESS, wdata, wfail);
	++stream_wdata;
	wdata = stream_wdata;	
	apb.write(RIGHT_FIFO_ADDRESS, wdata, wfail);
	++stream_wdata;
     end
   
   fork
      
      begin : host_process
	 // 4-1.1.
	 addr = CMD_REG_ADDRESS;
	 wdata = CMD_START;
	 apb.write(addr, wdata, wfail);
	 // 4-1.2.
	 while (irq_counter < 3)
	   begin
	      // 4-1.3.
	      irq.monitor(irq_out_state);
	      // 4-1.4.
	      if (!irq_out_state)
		begin
		   ++cycle_counter;
		   ia_performance_test_1: assert ( cycle_counter < (AUDIO_FIFO_SIZE+1) * CLK_DIV_48000 ) 
		     else
		       begin
			  assert_error("ia_performance_test_1");
			  irq_counter = 3;
		       end
		end
	      // 4-1.5.
	      else
		begin
		   for (int i=0; i < AUDIO_FIFO_SIZE; ++i)
		     begin
			wdata = stream_wdata;
			apb.write(LEFT_FIFO_ADDRESS, wdata, wfail);
			++stream_wdata;
			wdata = stream_wdata;		   
			apb.write(RIGHT_FIFO_ADDRESS, wdata, wfail);
			++stream_wdata;
		     end
		   
		   // 4-1.5.
		   addr = CMD_REG_ADDRESS;
		   wdata = CMD_IRQACK;
		   apb.write(addr, wdata, wfail);
		   irq_counter = irq_counter + 1;
		   cycle_counter = 0;
		end
	   end
	 
	 // 4-1.6.		 
	 addr = CMD_REG_ADDRESS;
	 wdata = CMD_STOP;
	 apb.write(addr, wdata, wfail);

      end : host_process

      begin : req_in_driver

	 // 4-2.1.
	 wait (play_out);
	 // 4-2.2.
	 while(play_out)
	   begin
	      repeat(CLK_DIV_48000-1) @(posedge clk);
	      req_in = '1;
	      @(posedge clk);	      
	      req_in = '0;
	   end
	 
      end : req_in_driver


      begin: audio_out_reader
	 // 4-3.1.
	 stream_rdata = 1;
	 // 4-3.2.
	 forever
	   begin
	      wait(tick_out);
	      ia_performance_test_2: assert ( (audio0_out == stream_rdata) && audio1_out == stream_rdata+1) else assert_error("ia_performance_test_2");
	      stream_rdata = stream_rdata + 2;
	      @(posedge clk);
	   end
	 
      end: audio_out_reader
   join_any
   disable fork;
   
   update_test_stats;      

endtask


