#ifndef tlm_defs_h
#define tlm_defs_h

// Constants for loose timing modeling

#define TLM_BUS_ACCESS_DELAY    10
#define TLM_DATA_WRITE_DELAY    10
#define TLM_DATA_READ_DELAY     10
#define TLM_COMMAND_WRITE_DELAY 80
#define TLM_DSP_DELAY           1000
#define TLM_INTERRUPT_LATENCY   1000
#define TLM_REQ_DELAY           100
#define TLM_TICK_DELAY          100

//Audio data type for TLM model

class audio_data_t 
{ 
 public:
  sc_int<DATABITS> left, right; 

  // constructor
  audio_data_t (sc_int<DATABITS> left_ = 0, sc_int<DATABITS> right_ = 0) {
      left = left_;
      right = right_;
    }
    
    inline bool operator == (const audio_data_t & rhs) const {
      return (rhs.left == left && rhs.right == right );
    }

    inline audio_data_t& operator = (const audio_data_t& rhs) {
      left = rhs.left;
      right = rhs.right;
      return *this;
    }

    inline friend void sc_trace(sc_trace_file *tf, const audio_data_t & v,
    const std::string & NAME ) {
      sc_trace(tf,v.left, NAME + ".left");
      sc_trace(tf,v.right, NAME + ".right");
    }

    inline friend ostream& operator << ( ostream& os,  audio_data_t const & v ) {
      os << "(" << v.left << "," <<  v.right << ")";
      return os;
    }

};

// Global reset event
extern sc_event scoreboard_reset;



#endif
