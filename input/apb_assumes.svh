// ---------------------------------------------------------------------------         
// f_reset
// ---------------------------------------------------------------------------

property f_reset;
   @(posedge clk, negedge clk) // OneSpin seems to require this to keep PSEL/PENABLE low in reset
     !rst_n |-> !PSEL && !PENABLE;
endproperty

mf_reset: assume property(f_reset)
  else $error("PSEL or PENABLE not zero during reset");

// ---------------------------------------------------------------------------         
// f_psel_1
// ---------------------------------------------------------------------------
   
property f_psel_1;
   @(posedge clk) disable iff (rst_n == '0)
     (PADDR >= AUDIOPORT_START_ADDRESS && PADDR <= AUDIOPORT_END_ADDRESS) |-> PSEL;
endproperty

mf_psel_1: assume property(f_psel_1)
  else $error("PSEL != '1 while PADDR in AUDIOPORT range.");


// ---------------------------------------------------------------------------         
// f_psel_0
// ---------------------------------------------------------------------------
   
property f_psel_0;
   @(posedge clk) disable iff (rst_n == '0)
     !(PADDR >= AUDIOPORT_START_ADDRESS && PADDR <= AUDIOPORT_END_ADDRESS) |-> !PSEL;
endproperty

mf_psel_0: assume property(f_psel_0)
  else $error("PSEL 1= '0 while PADDR outside AUDIOPORT range.");

// ---------------------------------------------------------------------------         
// f_psel_before_penable
// ---------------------------------------------------------------------------

property f_psel_before_penable;
   @(posedge clk) disable iff (rst_n == '0)
     $rose(PSEL) |-> !PENABLE ##1 PENABLE;
endproperty

mf_psel_before_penable: assume property(f_psel_before_penable);

// ---------------------------------------------------------------------------         
// f_penable_fall
// ---------------------------------------------------------------------------

property f_penable_fall;
   @(posedge clk) disable iff (rst_n == '0)
     (PENABLE && PREADY) |=> !PENABLE;
endproperty

mf_penable_fall: assume property(f_penable_fall);

// ---------------------------------------------------------------------------         
// f_penable_hold
// ---------------------------------------------------------------------------

property f_penable_hold;
   @(posedge clk) disable iff (rst_n == '0)
     (PSEL && PENABLE && !PREADY) |=> (PSEL && PENABLE);
endproperty

mf_penable_hold: assume property(f_penable_hold);

// ---------------------------------------------------------------------------         
// f_bus_stable
// ---------------------------------------------------------------------------

property f_bus_hold;
   @(posedge clk) disable iff (rst_n == '0)
     PSEL && PENABLE |-> $stable(PADDR) && $stable(PWDATA) && $stable(PWRITE);
endproperty

mf_bus_hold: assume property(f_bus_hold);

// ---------------------------------------------------------------------------         
// f_apb_access
// ---------------------------------------------------------------------------

sequence s_apb_setup;
   PSEL && !PENABLE;
endsequence

sequence s_apb_access;
   ($stable(PADDR) && $stable(PWRITE) && PSEL && PENABLE && !PREADY) [* 0:32] ##1 
   ($stable(PADDR) && $stable(PWRITE) && PSEL && PENABLE && PREADY) ##1 
   !PENABLE;
endsequence

property f_apb_access;
   @(posedge clk) disable iff (rst_n == '0)
     s_apb_setup |=> s_apb_access;
endproperty

mf_apb_access: assume property(f_apb_access);

// ---------------------------------------------------------------------------      
// f_paddr_align
// ---------------------------------------------------------------------------      

property f_paddr_align;
   @(posedge clk) disable iff (rst_n == '0)
     PSEL |-> PADDR[1:0] == 2'b00;
endproperty

mf_paddr_align: assume property(f_paddr_align)
  else $error("PADDR not properly aligned, PADDR[1:0] != 2'b00");

// ---------------------------------------------------------------------------      
// s_apb_write
// ---------------------------------------------------------------------------      

sequence s_apb_write (paddr, pwdata);
 (PSEL && !PENABLE && PWRITE && (PADDR == paddr) && (pwdata == PWDATA)) ##1
 (PSEL && PENABLE && PWRITE &&  (PADDR == paddr) && (pwdata == PWDATA) && PREADY);
endsequence
