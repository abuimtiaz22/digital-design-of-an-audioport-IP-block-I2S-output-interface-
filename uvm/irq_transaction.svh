///////////////////////////////////////////////////////////
//
// irq_transaction
//
///////////////////////////////////////////////////////////

class irq_transaction extends uvm_sequence_item;
   `uvm_object_utils(irq_transaction)

   //-------------------------------------------------------- 
   // Member variables
   //--------------------------------------------------------
     
   logic irq;

   //-------------------------------------------------------- 
   // Member functions
   //--------------------------------------------------------
   
   function new (string name = "");
      super.new(name);
   endfunction
   
   function void do_copy(uvm_object rhs);
      irq_transaction rhs_;
      if(!$cast(rhs_, rhs)) begin
	 uvm_report_error("irq_transaction.do_copy:", "Cast failed");
	 return;
      end
      super.do_copy(rhs); 
      irq = rhs_.irq;
   endfunction

  function void do_record(uvm_recorder recorder);
   super.do_record(recorder);
   `uvm_record_attribute(recorder.tr_handle, "irq", irq);
   endfunction
   
endclass: irq_transaction


