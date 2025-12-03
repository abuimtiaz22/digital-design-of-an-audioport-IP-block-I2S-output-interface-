///////////////////////////////////////////////////////////
//
// Class: apb_analyzer
//
///////////////////////////////////////////////////////////

class apb_analyzer extends uvm_subscriber #(apb_transaction);
   `uvm_component_utils(apb_analyzer)

   int m_writes_to_dut = 0;
   int m_reads_from_dut = 0;   
   int m_writes_to_other = 0;
   int m_reads_from_other = 0;   
   int m_data_valids = 0;
   int m_data_conflicts = 0;   
   
   logic [31:0] m_register_data[];
   logic m_write_hits[];
   logic m_read_hits[];      
   
   apb_transaction tx;
   
   covergroup dut_write_coverage;
      write_cov: coverpoint tx.addr[8:2] iff (tx.write_mode == '1);
   endgroup 

   covergroup dut_read_coverage;
      read_cov: coverpoint tx.addr[8:2] iff (tx.write_mode == '0);
   endgroup 

   function new(string name, uvm_component parent);
      super.new(name, parent);
      dut_write_coverage = new();
      dut_read_coverage = new();      
   endfunction

   function void write(apb_transaction t);
      tx = t;
      dut_write_coverage.sample();
      dut_read_coverage.sample();      
      
      if (t.addr >= DUT_START_ADDRESS && t.addr <= DUT_END_ADDRESS)
	begin
	   if (t.write_mode == '1)
	     begin
		++m_writes_to_dut;
		m_register_data[(t.addr - DUT_START_ADDRESS)/4] = t.data;
		m_write_hits[(t.addr - DUT_START_ADDRESS)/4] = '1;
	     end
	   else
	     begin
		++m_reads_from_dut;
		m_read_hits[(t.addr - DUT_START_ADDRESS)/4] = '1;

		if (m_write_hits[(t.addr - DUT_START_ADDRESS)/4] == '0)
		  uvm_report_error("apb_analyzer", $sformatf("Read from uninitialized location %d of\n%p\n", (t.addr - DUT_START_ADDRESS)/4, m_register_data));
		
		assert(m_register_data[(t.addr - DUT_START_ADDRESS)/4] == t.data)
		  ++m_data_valids;
                else
		  begin
		         uvm_report_error("apb_analyzer", $sformatf("Invalid data read from %h (register %d), got %h, expected %h\n",
								    t.addr,
								    (t.addr - DUT_START_ADDRESS)/4,
								    t.data, m_register_data[(t.addr - DUT_START_ADDRESS)/4]));
		     ++m_data_conflicts;
		  end
	     end
	end
      else 
	begin
	   if (t.write_mode == '1)
	     ++m_writes_to_other;
	   else
	     ++m_reads_from_other;	     
	end

   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      m_register_data = new[(DUT_END_ADDRESS-DUT_START_ADDRESS+1)];
      m_write_hits = new[(DUT_END_ADDRESS-DUT_START_ADDRESS+1)];      
      for (int i=0; i < (DUT_END_ADDRESS-DUT_START_ADDRESS+1)/4; ++i)
	m_write_hits[i] = '0;
      m_read_hits = new[(DUT_END_ADDRESS-DUT_START_ADDRESS+1)];      
      for (int i=0; i < (DUT_END_ADDRESS-DUT_START_ADDRESS+1)/4; ++i)
	m_read_hits[i] = '0;
   endfunction

   function void report_phase( uvm_phase phase );
      int write_hits = 0;
      int read_hits = 0;      
      real write_coverage =  dut_write_coverage.get_coverage();
      real read_coverage =  dut_read_coverage.get_coverage();      
      for (int i=0; i < (DUT_END_ADDRESS-DUT_START_ADDRESS+1)/4; ++i)
	if (m_write_hits[i] == '1) ++write_hits;
      for (int i=0; i < (DUT_END_ADDRESS-DUT_START_ADDRESS+1)/4; ++i)
	if (m_read_hits[i] == '1) ++read_hits;
      uvm_report_info("apb_analyzer", "=========================== apb_analyzer REPORT =============================================");
      uvm_report_info("apb_analyzer", $sformatf("DUT: Individual addresses accessed:   %6d writes, %6d reads", write_hits, read_hits));
      uvm_report_info("apb_analyzer", $sformatf("     Total accesses:                  %6d writes, %6d reads", m_writes_to_dut, m_reads_from_dut));
      uvm_report_info("apb_analyzer", $sformatf("     Coverage:                        %.2f%% write, %.2f%% read ", write_coverage, read_coverage));    
      uvm_report_info("apb_analyzer", $sformatf("     Read data:                       %6d valid,  %6d invalid", m_data_valids, m_data_conflicts));    
      uvm_report_info("apb_analyzer", $sformatf("Accesses to other APB addresses:      %6d writes, %6d reads", m_writes_to_other, m_reads_from_other));  
      uvm_report_info("apb_analyzer", "=============================================================================================");
   endfunction
   

endclass

