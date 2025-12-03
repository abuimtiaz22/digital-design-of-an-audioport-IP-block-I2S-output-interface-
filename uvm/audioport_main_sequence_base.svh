///////////////////////////////////////////////////////////
//
// audioport_main_sequence_base
//
///////////////////////////////////////////////////////////

class audioport_main_sequence_base extends uvm_sequence #(apb_transaction);
      `uvm_object_utils(audioport_main_sequence_base)

   function new (string name = "");
      super.new(name);
   endfunction
   
endclass
