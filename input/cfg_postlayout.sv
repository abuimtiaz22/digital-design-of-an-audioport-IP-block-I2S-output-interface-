`define actual_tb_name(head) head``_tb

`ifndef POSTLAYOUT_VS_RTL

config GATELEVEL_HIERARCHY_CFG;
   
   design gatelevel_lib.`DESIGN_NAME_MACRO;
   default liblist gatelevel_lib;

endconfig

config POSTLAYOUT_HIERARCHY_CFG;
   
   design postlayout_lib.`DESIGN_NAME_MACRO;
   default liblist postlayout_lib;

endconfig
   
config POSTLAYOUT_SIMULATION_CFG;
  design work.`actual_tb_name(`DESIGN_NAME_MACRO);
   default liblist work postlayout_lib;
   instance `actual_tb_name(`DESIGN_NAME_MACRO).DUT_INSTANCE use work.POSTLAYOUT_HIERARCHY_CFG:config;
   instance `actual_tb_name(`DESIGN_NAME_MACRO).REF_MODEL.REF_INSTANCE use work.GATELEVEL_HIERARCHY_CFG:config;
   
endconfig
   
`else // !`ifndef POSTLAYOUT_VS_RTL

config POSTLAYOUT_HIERARCHY_CFG;
   
   design postlayout_lib.`DESIGN_NAME_MACRO;
   default liblist postlayout_lib;

endconfig

// Configure test bench
   
config POSTLAYOUT_SIMULATION_CFG;   
   design work.`actual_tb_name(`DESIGN_NAME_MACRO);
   default liblist work;
   instance `actual_tb_name(`DESIGN_NAME_MACRO).DUT_INSTANCE use work.POSTLAYOUT_HIERARCHY_CFG:config;
   instance `actual_tb_name(`DESIGN_NAME_MACRO).REF_MODEL.REF_INSTANCE use work.`DESIGN_NAME_MACRO;      
endconfig


 `endif
   

   

