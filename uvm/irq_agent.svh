///////////////////////////////////////////////////////////
//
// irq_agent
//
///////////////////////////////////////////////////////////

class irq_agent extends uvm_agent;
   `uvm_component_utils(irq_agent)

   //-------------------------------------------------------- 
   // Member variables
   //--------------------------------------------------------
     
   uvm_analysis_port #(irq_transaction) analysis_port;
   irq_monitor m_monitor;

   //-------------------------------------------------------- 
   // Member functions
   //--------------------------------------------------------
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
      analysis_port = new("analysis_port", this);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      m_monitor   = irq_monitor::type_id::create("m_monitor", this);
   endfunction

   function void connect_phase(uvm_phase phase);
     m_monitor.analysis_port.connect(analysis_port);
   endfunction
   
endclass 
