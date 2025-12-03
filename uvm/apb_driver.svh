///////////////////////////////////////////////////////////
//
// Class: apb_driver
//
///////////////////////////////////////////////////////////

class apb_driver extends uvm_driver #(apb_transaction);
   `uvm_component_utils(apb_driver)

   virtual apb_if m_apb_if;

   int m_writes_to_dut = 0;
   int m_reads_from_dut = 0;   
   int m_writes_to_other = 0;
   int m_reads_from_other = 0;   
   int m_failed_writes_to_dut = 0;
   int m_failed_reads_from_dut = 0;   
   int m_failed_writes_to_other = 0;
   int m_failed_reads_from_other = 0;   
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction

   function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);

      if (!uvm_config_db #(virtual interface apb_if)::get(this, "", "apb_if_config", m_apb_if))
	begin
	   `uvm_error("apb_driver config error" , "uvm_config_db #( virtual interface apb_if )::get cannot find resource apb_if" );
	end   
   endfunction
   
   task run_phase(uvm_phase phase);

      m_apb_if.reset();

      forever
	begin
	   apb_transaction tx;
	   int wait_counter;
	   
	   seq_item_port.get_next_item(tx);

	   if (tx.write_mode == '1)
	     begin
		m_apb_if.write(tx.addr, tx.data, tx.fail);
		if (tx.addr >= DUT_START_ADDRESS && tx.addr <= DUT_END_ADDRESS)
		  begin
		     ++m_writes_to_dut;
		     if (tx.fail == '1)
		       ++m_failed_writes_to_dut;
		  end
		else
		  begin
		     ++m_writes_to_other;
		     if (tx.fail == '1)
		       ++m_failed_writes_to_other;
		  end
	     end
	   else
	     begin
		m_apb_if.read(tx.addr, tx.data, tx.fail);

		if (tx.addr >= DUT_START_ADDRESS && tx.addr <= DUT_END_ADDRESS)
		  begin
		     ++m_reads_from_dut;
		     if (tx.fail == '1)
		       ++m_failed_reads_from_dut;
		  end
		else
		  begin
		     ++m_reads_from_other;
		     if (tx.fail == '1)
		       ++m_failed_reads_from_other;
		  end
	     end

	   seq_item_port.item_done();

	end
   endtask

   function void report_phase( uvm_phase phase );
      uvm_report_info("apb_driver", "=========================== apb_driver REPORT =============================================");
      uvm_report_info("apb_driver", $sformatf("DUT:       %6d writes, %6d reads generated", m_writes_to_dut, m_reads_from_dut));
      uvm_report_info("apb_driver", $sformatf("           %6d failed, %6d failed", m_failed_writes_to_dut, m_failed_reads_from_dut));      
      uvm_report_info("apb_driver", $sformatf("Other APB: %6d writes, %6d reads generated", m_writes_to_other, m_reads_from_other));      
      uvm_report_info("apb_driver", $sformatf("           %6d failed, %6d failed", m_failed_writes_to_other, m_failed_reads_from_other));      
      uvm_report_info("apb_driver", "===========================================================================================");
   endfunction
   
endclass

