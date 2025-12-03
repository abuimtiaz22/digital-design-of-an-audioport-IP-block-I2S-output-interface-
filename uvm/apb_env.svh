///////////////////////////////////////////////////////////
//
// Class: apb_env
//
///////////////////////////////////////////////////////////

class apb_env extends uvm_env;
   `uvm_component_utils(apb_env)

   apb_agent m_agent;
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      m_agent = apb_agent::type_id::create("m_agent", this);
   endfunction

endclass   

