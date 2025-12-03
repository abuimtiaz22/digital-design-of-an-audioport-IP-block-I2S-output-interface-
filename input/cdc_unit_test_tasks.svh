task automatic testmux_test;
   $info("T1: testmux_test");
   
   // 1.

   play_in = '0;
   tick_in = '0;
   audio0_in = '0;
   audio1_in = '0;	
   req_in = '0;
   test_mode_in = '0;
   rst_n = '0;

   // 2.   
   test_mode_in = '0;
   rst_n = '0;
   repeat(4)
     begin
	@(posedge mclk);
     end

   // 3.
   
   rst_n = '1;
   repeat(4)
     begin
	@(posedge mclk);
     end

   // 4.
   
   test_mode_in = '1;
   rst_n = '0;
   repeat(8)
     begin
	@(negedge clk);
     end

   // 5.
   
   rst_n = '1;
   repeat(8)
     begin
	@(negedge clk);
     end

   test_mode_in = '0;   
   update_test_stats;
   
endtask

task automatic reset_sync_test;
   real  tlaunch_queue[$];
   real  tlaunch;
   real  tcapture;
   real  tlatency;

   $info("T2: reset_sync_test");

   fork
      begin
	 repeat(10)
	   begin
	      // 1
	      @(negedge clk);
	      rst_n = '0;
	      
	      // 3
	      #(2*MCLK_PERIOD);

	      // 4	   
	      @(negedge clk);
	      rst_n = '1;

	      // 5	   
	      @(posedge muxclk_out);

	      // 6	   
	      @(posedge muxclk_out);

	      // 7
	      #(2*MCLK_PERIOD);
	      
	   end // repeat (5)
      end // fork begin
      begin : timer_start
	 tlaunch_queue.delete();
	 forever
	   begin
	      @(posedge rst_n) begin
//		 $info("TX");
		 tlaunch_queue.push_back($realtime);
	      end
	   end
      end : timer_start

      begin : timer_end
	 forever
	   begin
	      @(posedge muxrst_n_out) begin
//		 $info("RX");		      
		 tcapture = $realtime;
		 tlaunch = tlaunch_queue.pop_front();
		 tlatency = tcapture - tlaunch;
		 if (tlatency > tmaxlatency) begin
		    tmaxlatency = tlatency;
//		    $info("latency = %f ns", tmaxlatency);
		 end
	      end
 	   end
      end : timer_end
   join_any
   disable fork;

   reset_sync_latency = tmaxlatency;
      
   update_test_stats;
   
endtask


task automatic play_sync_test;
   real  tlaunch_queue[$];
   real  tlaunch;
   real  tcapture;
   real  tlatency;
   logic play;
   logic past_play_in;
   logic past_play_out;

   
   $info("T3: play_sync_test");
   
   // 1
   play = '0;
   test_mode_in = '0;   
   tmaxlatency = 0.0;

   // 2 synchronize to clk
   @(cb_clk);	      
   
   fork
      begin : tx
	 repeat ($rtoi(MCLK_PERIOD/CLK_PERIOD)+10)
	   begin
	      play = !play;	      
	      cb_clk.play_in <= play;
	      @(cb_clk);	      
	      // 2
`ifndef FORCE_PROTOCOL_FAILURE
	      repeat(CDC_BITSYNC_INTERVAL)
`endif
		@(cb_clk);
	   end
	 repeat(2*CDC_BITSYNC_INTERVAL)
	   @(cb_clk);
      end // block: tx
      
      begin : timer_start
	 tlaunch_queue.delete();
	 forever
	   begin
	      @(posedge play_in) begin
//		 $info("TX");
		 tlaunch_queue.push_back($realtime);
	      end
	   end
      end : timer_start

      begin : timer_end
	 forever
	   begin
	      @(posedge play_out) begin
//		 $info("RX");		      
		 tcapture = $realtime;
		 tlaunch = tlaunch_queue.pop_front();
		 tlatency = tcapture - tlaunch;
		 if (tlatency > tmaxlatency) begin
		    tmaxlatency = tlatency;
//		    $info("latency = %f ns", tmaxlatency);
		 end
	      end
 	   end
      end : timer_end
   join_any
   disable fork;

   play_sync_latency = tmaxlatency;
   
   update_test_stats;
endtask




task automatic pulse_sync_test;
   real  tlaunch_queue[$];
   real  tlaunch;
   real  tcapture;
   real  tlatency;

   $info("T4: pulse_sync_test");

   // 1
   req_in = '0;
   test_mode_in = '0;   
   tmaxlatency = 0.0;

   @(cb_mclk);	
   
   fork
      begin : tx
	 repeat (50)
	   begin
	      cb_mclk.req_in <= '1;
	      @(cb_mclk);	
	      cb_mclk.req_in <= '0;
	      repeat(CDC_PULSESYNC_INTERVAL)
		@(cb_mclk);	
	   end
	 repeat(2*CDC_PULSESYNC_INTERVAL)
	   @(cb_mclk);	

      end : tx

      begin : timer_start
	 tlaunch_queue.delete();
	 forever
	   begin
	      @(posedge req_in) begin
//		 $info("TX");
		 tlaunch_queue.push_back($realtime);
	      end
	   end
      end : timer_start

      begin : timer_end
	 forever
	   begin
	      @(posedge req_out) begin
//		 $info("RX");		      
		 tcapture = $realtime;
		 tlaunch = tlaunch_queue.pop_front();
		 tlatency = tcapture - tlaunch;
		 if (tlatency > tmaxlatency) begin
		    tmaxlatency = tlatency;
//		    $info("latency = %f ns", tmaxlatency);
		 end
	      end
 	   end
      end : timer_end

   join_any
   disable fork;

   req_sync_latency = tmaxlatency;   
   
   update_test_stats;      
endtask


task automatic audio_sync_test;
   real  tlaunch_queue[$];
   real  tlaunch;
   real  tcapture;
   real  tlatency;
   $info("T5: audio_sync_test");

   // 1
   test_mode_in = '0;   
   tmaxlatency = 0.0;

   @(cb_clk);
   
   fork
      begin : tx
	 repeat(50)
	   begin
	      cb_clk.tick_in <= '1;
	      cb_clk.audio0_in <= $urandom;
	      cb_clk.audio1_in <= $urandom;
	      @(cb_clk);
	      cb_clk.tick_in <='0;
	      cb_clk.audio0_in <= '0;
	      cb_clk.audio1_in <= '0;	      
	      repeat (CDC_DATASYNC_INTERVAL-1)
		@(cb_clk);
	   end
	 repeat (2*CDC_DATASYNC_INTERVAL-1)
	   @(cb_clk);

      end : tx

      begin : timer_start
	 tlaunch_queue.delete();
	 forever
	   begin
	      @(posedge tick_in) begin
//		 $info("TX");
		 tlaunch_queue.push_back($realtime);
	      end
	   end
      end : timer_start

      begin : timer_end
	 forever
	   begin
	      @(posedge tick_out) begin
//		 $info("RX");		      
		 tcapture = $realtime;
		 tlaunch = tlaunch_queue.pop_front();
		 tlatency = tcapture - tlaunch;
		 if (tlatency > tmaxlatency) begin
		    tmaxlatency = tlatency;
//		    $info("latency = %f ns", tmaxlatency);
		 end
	      end
 	   end
      end : timer_end

   join_any
   disable fork;

   audio_sync_latency = tmaxlatency;   
   
   update_test_stats;
endtask
