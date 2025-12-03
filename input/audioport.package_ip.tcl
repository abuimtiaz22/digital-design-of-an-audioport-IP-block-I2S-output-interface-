# Define APB interface 

ipx::add_bus_interface apb_slave [ipx::current_core]

set_property abstraction_type_vlnv xilinx.com:interface:apb_rtl:1.0 [ipx::get_bus_interfaces apb_slave -of_objects [ipx::current_core]]

set_property bus_type_vlnv xilinx.com:interface:apb:1.0 [ipx::get_bus_interfaces apb_slave -of_objects [ipx::current_core]]

ipx::add_port_map PADDR [ipx::get_bus_interfaces apb_slave -of_objects [ipx::current_core]]
set_property physical_name PADDR [ipx::get_port_maps PADDR -of_objects [ipx::get_bus_interfaces apb_slave -of_objects [ipx::current_core]]]

ipx::add_port_map PREADY [ipx::get_bus_interfaces apb_slave -of_objects [ipx::current_core]]
set_property physical_name PREADY [ipx::get_port_maps PREADY -of_objects [ipx::get_bus_interfaces apb_slave -of_objects [ipx::current_core]]]

ipx::add_port_map PSLVERR [ipx::get_bus_interfaces apb_slave -of_objects [ipx::current_core]]
set_property physical_name PSLVERR [ipx::get_port_maps PSLVERR -of_objects [ipx::get_bus_interfaces apb_slave -of_objects [ipx::current_core]]]

ipx::add_port_map PENABLE [ipx::get_bus_interfaces apb_slave -of_objects [ipx::current_core]]
set_property physical_name PENABLE [ipx::get_port_maps PENABLE -of_objects [ipx::get_bus_interfaces apb_slave -of_objects [ipx::current_core]]]

ipx::add_port_map PWRITE [ipx::get_bus_interfaces apb_slave -of_objects [ipx::current_core]]
set_property physical_name PWRITE [ipx::get_port_maps PWRITE -of_objects [ipx::get_bus_interfaces apb_slave -of_objects [ipx::current_core]]]

ipx::add_port_map PRDATA [ipx::get_bus_interfaces apb_slave -of_objects [ipx::current_core]]
set_property physical_name PRDATA [ipx::get_port_maps PRDATA -of_objects [ipx::get_bus_interfaces apb_slave -of_objects [ipx::current_core]]]

ipx::add_port_map PWDATA [ipx::get_bus_interfaces apb_slave -of_objects [ipx::current_core]]
set_property physical_name PWDATA [ipx::get_port_maps PWDATA -of_objects [ipx::get_bus_interfaces apb_slave -of_objects [ipx::current_core]]]

ipx::add_port_map PSEL [ipx::get_bus_interfaces apb_slave -of_objects [ipx::current_core]]
set_property physical_name PSEL [ipx::get_port_maps PSEL -of_objects [ipx::get_bus_interfaces apb_slave -of_objects [ipx::current_core]]]
