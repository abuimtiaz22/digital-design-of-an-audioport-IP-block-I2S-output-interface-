///////////////////////////////////////////////////////////
//
// Class: apb_monitor
//
///////////////////////////////////////////////////////////

class apb_monitor extends uvm_monitor;
   `uvm_component_utils(apb_monitor)

   uvm_analysis_port #(apb_transaction) analysis_port;
   
   virtual apb_if m_apb_if;

   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      analysis_port = new("analysis_port", this);
   endfunction

   function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);

      if (!uvm_config_db #(virtual interface apb_if)::get(this, "", "apb_if_config", m_apb_if))
	begin
	   `uvm_error("apb_monitor config error" , "uvm_config_db #( virtual interface apb_if )::get cannot find resource apb_if" );
	end

   endfunction

   task run_phase(uvm_phase phase);
      logic tx_ok;
      
      apb_transaction tx, tx_clone;      
      tx = apb_transaction::type_id::create("tx");

     forever
       begin
	  m_apb_if.monitor(tx_ok, tx.addr, tx.data, tx.write_mode);
	  if (tx_ok == '1)
	    begin
	       $cast(tx_clone, tx.clone());
	       analysis_port.write(tx_clone);
	    end
       end
      
    endtask
   
endclass
