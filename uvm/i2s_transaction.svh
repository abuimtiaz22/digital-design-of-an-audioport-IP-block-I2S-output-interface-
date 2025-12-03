///////////////////////////////////////////////////////////
//
// i2s_transaction
//
///////////////////////////////////////////////////////////

class i2s_transaction extends uvm_sequence_item;
   `uvm_object_utils(i2s_transaction)
  
     logic [1:0][23:0] audio_data;
   
   function new (string name = "");
      super.new(name);
   endfunction
   
   function void do_copy(uvm_object rhs);
      i2s_transaction rhs_;
      if(!$cast(rhs_, rhs)) begin
	 uvm_report_error("i2s_transaction.do_copy:", "Cast failed");
	 return;
      end
      super.do_copy(rhs); 
      audio_data[0] = rhs_.audio_data[0];
      audio_data[1] = rhs_.audio_data[1];	   
      
   endfunction

  function void do_record(uvm_recorder recorder);
   super.do_record(recorder);
   `uvm_record_attribute(recorder.tr_handle, "audio_data", audio_data);
   endfunction
   
endclass: i2s_transaction
