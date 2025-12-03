///////////////////////////////////////////////////////////
//
// irq_monitor
//
///////////////////////////////////////////////////////////

class irq_monitor extends uvm_monitor;
   `uvm_component_utils(irq_monitor)

   //-------------------------------------------------------- 
   // Member variables
   //--------------------------------------------------------
     
   uvm_analysis_port #(irq_transaction) analysis_port;
   virtual irq_out_if m_irq_out_if;

   //-------------------------------------------------------- 
   // Member functions
   //--------------------------------------------------------
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      analysis_port = new("analysis_port", this);
   endfunction

   function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      if (!uvm_config_db #(virtual interface irq_out_if)::get(this, "", "irq_out_if_config", m_irq_out_if))
	begin
	   `uvm_error("irq_monitor config error" , "uvm_config_db #( virtual interface irq_out_if )::get cannot find resource irq_out_if" );
	end
   endfunction

   task run_phase(uvm_phase phase);
      irq_transaction tx, tx_clone;      
      tx = irq_transaction::type_id::create("tx");
     forever
       begin
	  m_irq_out_if.monitor(tx.irq);
	  $cast(tx_clone, tx.clone());
	  analysis_port.write(tx_clone);
       end
    endtask
   
endclass

