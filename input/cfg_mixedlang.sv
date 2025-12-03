`define actual_tb_name(head) head``_tb

config SYSTEMC_INSTANCE_CFG;

   design systemc_lib.`DESIGN_NAME_MACRO;
   default liblist systemc_lib;   

endconfig

config MIXEDLANG_SIMULATION_CFG;   

   design work.`actual_tb_name(`DESIGN_NAME_MACRO);
   default liblist work systemc_lib;
   instance `actual_tb_name(`DESIGN_NAME_MACRO).DUT_INSTANCE use work.SYSTEMC_INSTANCE_CFG:config;
//   instance `actual_tb_name(`DESIGN_NAME_MACRO).DUT_INSTANCE use work.`DESIGN_NAME_MACRO;   
   
endconfig
   


   

