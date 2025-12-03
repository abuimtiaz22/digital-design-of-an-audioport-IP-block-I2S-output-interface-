///////////////////////////////////////////////////////////
//
// i2s_monitor
//
///////////////////////////////////////////////////////////

class i2s_monitor extends uvm_monitor;
   `uvm_component_utils(i2s_monitor)

   uvm_analysis_port #(i2s_transaction) analysis_port;
   
   virtual i2s_if m_i2s_if;

   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      analysis_port = new("analysis_port", this);
   endfunction

   function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);

      if (!uvm_config_db #(virtual interface i2s_if)::get(this, "", "i2s_if_config", m_i2s_if))
	begin
	   `uvm_error("i2s_monitor config error" , "uvm_config_db #( virtual interface i2s_if )::get cannot find resource i2s_if" );
	end

   endfunction

   task run_phase(uvm_phase phase);
      logic tx_ok;
      
      i2s_transaction tx, tx_clone;      
      tx = i2s_transaction::type_id::create("tx");

     forever
       begin
	  m_i2s_if.monitor(tx_ok, tx.audio_data);
	  if (tx_ok == '1)
	    begin
	       $cast(tx_clone, tx.clone());
	       analysis_port.write(tx_clone);
	    end
	  else
	    begin
	       $display("i2s_monitor: transaction failed!\n");
	    end
       end
      
    endtask
   
endclass
