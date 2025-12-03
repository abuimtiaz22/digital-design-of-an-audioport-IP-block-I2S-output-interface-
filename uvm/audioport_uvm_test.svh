///////////////////////////////////////////////////////////
//
// audioport_uvm_test
//
///////////////////////////////////////////////////////////
   
class audioport_uvm_test extends uvm_test;
  `uvm_component_utils(audioport_uvm_test)

   audioport_env m_env;
    
  function new(string name, uvm_component parent);
     super.new(name,parent);
  endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      m_env = audioport_env::type_id::create("m_env", this);
  endfunction: build_phase


   task run_phase(uvm_phase phase);
      audioport_master_sequence master_seq;
      audioport_sequence_config seq_config = new;
      audioport_main_sequence_base::type_id::set_type_override(audioport_main_sequence::get_type(), 1);
      audioport_isr_sequence_base::type_id::set_type_override(audioport_isr_sequence::get_type(), 1);            
      master_seq = audioport_master_sequence::type_id::create("master_seq");  

      // Initialize sequence config data
      void'(seq_config.create_test_data("")); // No filename given => generate default waveforms      
      uvm_config_db #(audioport_sequence_config)::set(null, "*", "audioport_sequence_config", seq_config);

      reset_test_stats; 
            
      phase.raise_objection(this); 
      master_seq.start( m_env.m_control_unit_agent.m_sequencer );
      phase.drop_objection(this); 

      update_test_stats;      

      $display("#####################################################################################################");	
      $display("audioport_uvm_test results: PASSED: %d / FAILED: %d", tests_passed, tests_failed);
      $display("#####################################################################################################");	

      ia_audioport_uvm_test: assert (tests_failed == 0) else 
	assert_error("ia_audioport_uvm_test");  // See audioport_pkg.sv

    endtask

endclass 
