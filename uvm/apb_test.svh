///////////////////////////////////////////////////////////
//
// Class: apb_test
//
///////////////////////////////////////////////////////////
   
class apb_test extends uvm_test;
  `uvm_component_utils(apb_test)
    
  function new(string name, uvm_component parent);
     super.new(name,parent);
  endfunction

   apb_env m_env;

   function void build_phase(uvm_phase phase);
      apb_agent_config agent_config = new;
      apb_sequence_config seq_config = new;
      int test_cycles;
      
      super.build_phase(phase);

      agent_config.has_analyzer = 1;
      uvm_config_db #(apb_agent_config)::set(this, "*", "apb_agent_config", agent_config);
      
      if (uvm_config_db #(int)::get(null, get_full_name(), "APB_TEST_CYCLES", test_cycles))
	seq_config.apb_test_cycles = test_cycles;
      else
	seq_config.apb_test_cycles = 100;
      
      uvm_config_db #(apb_sequence_config)::set(this, "*", "apb_sequence_config", seq_config);

      m_env = apb_env::type_id::create("m_env", this);
 
  endfunction: build_phase

   task run_phase(uvm_phase phase);
      apb_sequence seq;
      seq = apb_sequence::type_id::create("seq");
      phase.raise_objection(this); 
      seq.start( m_env.m_agent.m_sequencer );
      phase.drop_objection(this); 
      uvm_report_info("apb_test", "apb_test finished.");
    endtask

endclass 

