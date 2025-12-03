`define actual_tb_name(head) head``_tb

`ifndef RTL_VS_SYSTEMC

config RTL_SIMULATION_CFG;

   design work.`actual_tb_name(`DESIGN_NAME_MACRO);
   
endconfig
   
`else



config RTL_INSTANCE_CFG;

   design work.`DESIGN_NAME_MACRO;
   default liblist work;   

endconfig
   
config SYSTEMC_INSTANCE_CFG;

   design systemc_lib.`DESIGN_NAME_MACRO;
   default liblist systemc_lib;   

endconfig

config RTL_SIMULATION_CFG;   

   design work.`actual_tb_name(`DESIGN_NAME_MACRO);
   default liblist work systemc_lib;
   instance `actual_tb_name(`DESIGN_NAME_MACRO).DUT_INSTANCE use work.RTL_INSTANCE_CFG:config;
   instance `actual_tb_name(`DESIGN_NAME_MACRO).REF_MODEL.REF_INSTANCE use work.SYSTEMC_INSTANCE_CFG:config;
   
endconfig
   


`endif
   


   

   

