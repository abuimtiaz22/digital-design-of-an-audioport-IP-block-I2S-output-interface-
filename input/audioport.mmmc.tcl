
create_library_set -name MaxLibSet -timing [list $INNOVUS_MMMC_MAX_LIBRARY_SET ]
create_library_set -name MinLibSet -timing [list $INNOVUS_MMMC_MIN_LIBRARY_SET ] 

create_opcond -name MaxOpCond -process 1 -voltage 1.08 -temperature 125
create_opcond -name MinOpCond -process 1 -voltage 1.08 -temperature -40

create_rc_corner -name BestRCCorner -cap_table $INNOVUS_MMMC_BEST_CAPTABLE
create_rc_corner -name WorstRCCorner -cap_table $INNOVUS_MMMC_WORST_CAPTABLE

create_timing_condition -name MaxTC -library_sets MaxLibSet -opcond MaxOpCond
create_timing_condition -name MinTC -library_sets MaxLibSet -opcond MinOpCond

create_delay_corner -name WorstDelayCorner -timing_condition { MaxTC PD_TOP@MaxTC} -rc_corner WorstRCCorner
create_delay_corner -name BestDelayCorner  -timing_condition { MinTC PD_TOP@MaxTC} -rc_corner BestRCCorner

create_constraint_mode -name Func -sdc_files [list ${RESULTS_DIR}/${DESIGN_NAME}_gatelevel.sdc ]

create_analysis_view -name FuncMax -constraint_mode Func -delay_corner WorstDelayCorner
create_analysis_view -name FuncMin -constraint_mode Func -delay_corner BestDelayCorner

set_analysis_view -setup [list FuncMax] -hold [list FuncMin]
