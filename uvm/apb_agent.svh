///////////////////////////////////////////////////////////
//
// Class: apb_agent
//
///////////////////////////////////////////////////////////

class apb_agent extends uvm_agent;
   `uvm_component_utils(apb_agent)

   apb_driver m_driver;
   apb_monitor m_monitor;
   apb_analyzer m_analyzer;
   apb_sequencer m_sequencer;
   bit has_analyzer;
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
      apb_agent_config agent_cfg;

      super.build_phase(phase);

      m_sequencer = apb_sequencer::type_id::create("m_sequencer", this);
      m_driver    = apb_driver::type_id::create("m_driver", this);
      m_monitor   = apb_monitor::type_id::create("m_monitor", this);

      has_analyzer = 1;
      if (uvm_config_db #(apb_agent_config)::get(null, get_full_name(), "apb_agent_config", agent_cfg))
	begin
	   has_analyzer = agent_cfg.has_analyzer;
	   `uvm_info("",$sformatf("apb_agent configured %s analyzer component.", (has_analyzer ? "with" : "without")), UVM_NONE);
	end

      if (has_analyzer) m_analyzer = apb_analyzer::type_id::create("m_analyzer", this);            
   endfunction

   function void connect_phase(uvm_phase phase);
      m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
      if (has_analyzer) m_monitor.analysis_port.connect(m_analyzer.analysis_export);
   endfunction
   
endclass 
