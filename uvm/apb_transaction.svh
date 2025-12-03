///////////////////////////////////////////////////////////
//
// Class: apb_transaction
//
///////////////////////////////////////////////////////////

class apb_transaction extends uvm_sequence_item;
   `uvm_object_utils(apb_transaction)
  
   rand logic [31:0] addr;
   rand logic [31:0] data;
   rand logic write_mode;
   logic fail;
   
   function new (string name = "");
      super.new(name);
   endfunction
   
   constraint c_addr { addr >= APB_START_ADDRESS; addr < APB_END_ADDRESS; }

 constraint c_align {
      addr[1:0] == 2'b00;  // 4-byte alignment
   }
   
   constraint c_regs {
      addr != CMD_REG_ADDRESS;
      addr != LEFT_FIFO_ADDRESS;
      addr != RIGHT_FIFO_ADDRESS;
   }

   function void do_copy(uvm_object rhs);
      apb_transaction rhs_;
      if(!$cast(rhs_, rhs)) begin
	 uvm_report_error("apb_transaction.do_copy:", "Cast failed");
	 return;
      end

      super.do_copy(rhs); 
      addr = rhs_.addr;
      data = rhs_.data;
      write_mode = rhs_.write_mode;
      fail = rhs_.fail;
      
   endfunction


  function void do_record(uvm_recorder recorder);
   super.do_record(recorder);
   `uvm_record_attribute(recorder.tr_handle, "addr", addr);
   `uvm_record_attribute(recorder.tr_handle, "data", data);
   `uvm_record_attribute(recorder.tr_handle, "write_mode", write_mode);
   `uvm_record_attribute(recorder.tr_handle, "fail", fail);      
   endfunction

endclass: apb_transaction

