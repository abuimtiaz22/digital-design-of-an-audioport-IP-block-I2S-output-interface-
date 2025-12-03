///////////////////////////////////////////////////////////
//
// Class: audioport_sequence_config
//
///////////////////////////////////////////////////////////

class audioport_sequence_config extends uvm_object;
   int current_abuf = 0;
   test_data_queue_t test_data_queue;

   function int create_test_data(string path);
      int file;
      string line;
      int    lines;
      int    left, right;
      
      current_abuf = 0;
      file = 0;
      
      if (path.len() > 0)
	file = $fopen(path, "r");
      
      if (file == 0)
    	begin
	   for (int i=0; i < 32; ++i)
	     begin
		audio_sample_t sample = new;
		if (i < 16)
		  begin
		     sample.right = 4194304 - i * (4194304/16);
		     sample.left = 4194304;
		  end
		else
		  begin
		     sample.right = -4194304 + i * (4194304/16);		     
		     sample.left = -4194304;
		  end

		test_data_queue.push_back(sample);
	     end
	   return 32;
	end
      else
	begin
	   lines = 0;
	   while($fgets(line, file) != 0)
	     begin
		if ($sscanf(line, "%d %d", left, right) != 2)
		  $error("Test data file format error (expected 2 integer values)\n");
		else
		  begin
		     audio_sample_t sample = new;
		     sample.left = left;
		     sample.right = right;		     
		     test_data_queue.push_back(sample);
		  end
		++lines;
	     end
	   $fclose(file);
	   $info("Read %d test data samples", lines);
	   return lines;
	end
      
   endfunction

   function audio_sample_t get_test_data;
      audio_sample_t sample;
      sample = test_data_queue.pop_front();
      test_data_queue.push_back(sample);
      return sample;
   endfunction

   function void reset();
      current_abuf = 0;
   endfunction
   
endclass 
