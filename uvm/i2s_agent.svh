///////////////////////////////////////////////////////////
//
// i2s_agent
//
///////////////////////////////////////////////////////////

class i2s_agent extends uvm_agent;
   `uvm_component_utils(i2s_agent)

   i2s_monitor m_monitor;
   uvm_analysis_port #(i2s_transaction) analysis_port;
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
      analysis_port = new("analysis_port", this);
      
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      m_monitor   = i2s_monitor::type_id::create("m_monitor", this);
   endfunction

   function void connect_phase(uvm_phase phase);
      m_monitor.analysis_port.connect(analysis_port);      
   endfunction
   
endclass 
