///////////////////////////////////////////////////////////
//
// audioport_scoreboard
//
// This component instantiates the audioprot_comparator and 
// audioport_predictor and connects them
//
///////////////////////////////////////////////////////////
   
class audioport_scoreboard extends uvm_scoreboard;
   `uvm_component_utils(audioport_scoreboard)

   audioport_predictor m_predictor;
   audioport_comparator m_comparator;   
   uvm_analysis_export #(apb_transaction) bus_analysis_export;
   uvm_analysis_export #(i2s_transaction) audio_analysis_export;   

   function new(string name, uvm_component parent);
      super.new(name, parent);
      bus_analysis_export = new("bus_analysis_export", this);
      audio_analysis_export = new("audio_analysis_export", this);      
   endfunction 
   
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      m_predictor = audioport_predictor::type_id::create("m_predictor", this);
      m_comparator = audioport_comparator::type_id::create("m_comparator", this);                  
   endfunction
     
   function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      bus_analysis_export.connect(m_predictor.bus_analysis_export);
      audio_analysis_export.connect(m_comparator.audio_analysis_export);
      m_comparator.predictor_get_port.connect(m_predictor.predictor_get_export);
   endfunction
     
endclass
