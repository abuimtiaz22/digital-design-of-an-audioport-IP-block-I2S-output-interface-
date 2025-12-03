///////////////////////////////////////////////////////////
//
// control_unit_agent
//
///////////////////////////////////////////////////////////

class control_unit_agent extends uvm_agent;
   `uvm_component_utils(control_unit_agent)

   //-------------------------------------------------------- 
   // Member variables
   //--------------------------------------------------------
   apb_driver     m_driver;
   apb_monitor    m_monitor;
   apb_sequencer  m_sequencer;

    
   uvm_event m_irq_event;
    uvm_analysis_imp #(irq_transaction, control_unit_agent) irq_analysis_export;
	uvm_analysis_port #(apb_transaction) analysis_port;
   //-------------------------------------------------------- 
   // Member functions
   //--------------------------------------------------------
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
irq_analysis_export = new("irq_analysis_export", this);
analysis_port = new("analysis_port", this);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);

 	// Create APB components using factory
      m_sequencer = apb_sequencer::type_id::create("m_sequencer", this);
      m_driver    = apb_driver::type_id::create("m_driver", this);
      m_monitor   = apb_monitor::type_id::create("m_monitor", this);
      m_irq_event = uvm_event_pool::get_global("irq_out");

   endfunction

   function void connect_phase(uvm_phase phase);
   m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
   m_monitor.analysis_port.connect(analysis_port);

   endfunction

   function void write(irq_transaction t);
      if(t.irq)
	m_irq_event.trigger();
   endfunction

endclass
 
