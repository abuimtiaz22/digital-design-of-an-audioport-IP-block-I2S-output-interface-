`define actual_tb_name(head) head``_tb

config POSTLAYOUT_HIERARCHY_CFG;
   design postlayout_lib.`DESIGN_NAME_MACRO;
   default liblist postlayout_lib;
endconfig
   
config POSTLAYOUT_POWER_SIMULATION_CFG;
   design work.`actual_tb_name(`DESIGN_NAME_MACRO);
   default liblist work;
   instance `actual_tb_name(`DESIGN_NAME_MACRO).DUT_INSTANCE use work.POSTLAYOUT_HIERARCHY_CFG:config;
endconfig
   


   

