#ifndef cdc_handshake_h
#define cdc_handshake_h

#include "systemc_headers.h"
#include "audioport_defs.h"

#ifdef HLS_RTL
#include "cdc_handshake_sc_foreign_module.h"
#else

#define TX_IDLE 1
#define TX_REQ  2
#define TX_ACK  4

#define RX_IDLE 1
#define RX_ACK  2

SC_MODULE(cdc_handshake) {
public:
    sc_in_clk                   clk1;
    sc_in<bool>                 rst1_n;
    sc_in_clk                   clk2;
    sc_in<bool>                 rst2_n;
    sc_in<bool>                 tx_en_in;
    sc_in< sc_uint<2*DATABITS> >     tx_in;
    sc_out<bool>                rx_en_out;
    sc_out< sc_uint<2*DATABITS> >    rx_out;

    sc_signal<bool>             txr_en;
    sc_signal< sc_uint<2*DATABITS> > txr;
    sc_signal<bool>             req;
    sc_signal<bool>             ack_ff1;
    sc_signal<bool>             ack_ff2;
    sc_signal < sc_uint<3> >    tx_state_r;
    sc_signal < sc_uint<3> >    tx_nextstate;
   
    sc_signal<bool>             rxr_en;
    sc_signal< sc_uint<2*DATABITS> > rxr;
    sc_signal<bool>             ack;
    sc_signal<bool>             req_ff1;
    sc_signal<bool>             req_ff2;
    sc_signal < sc_uint<3> >    rx_state_r;
    sc_signal < sc_uint<3> >    rx_nextstate;

    void hs_tx_regs()
    {
      if (rst1_n.read() == 0)
	{
	  txr = 0;
	  ack_ff1 = 0;
	  ack_ff2 = 0;
	  tx_state_r = TX_IDLE;
	}
      else
	{
	  if (txr_en == 1)
	    txr = tx_in;
	  tx_state_r = tx_nextstate;
	  ack_ff1 = ack;
	  ack_ff2 = ack_ff1;
	}
    }
    
    
    void hs_tx_logic()
    {
      
      switch(tx_state_r.read())
	{
	case TX_IDLE:
	  if (ack_ff2 == 0 && tx_en_in == 1)
	    {
	      tx_nextstate = TX_REQ;
	      txr_en = 1;
	    }
	  else
	    {
	      tx_nextstate = TX_IDLE;
	      txr_en = 0;
	    }
	  break;
	  
	case TX_REQ:
	  txr_en = 0;
	  if (ack_ff2 == 1)
	    {
	      tx_nextstate = TX_ACK;
	    }
	  else
	    {
	      tx_nextstate = TX_REQ;
	    }
	  break;
	  
	case TX_ACK:
	  txr_en = 0;
	  if (ack_ff2 == 0)
	    {
	      tx_nextstate = TX_IDLE;	      
	    }
	  else
	    {
	      tx_nextstate = TX_ACK;	      
	    }
	  break;
	  
	default: 
	  txr_en = 0;
	  tx_nextstate = TX_IDLE;	            
	}
      
      req = tx_state_r.read()[1];
      
    }
    

    void hs_rx_regs()
    {
      if (rst2_n.read() == 0)
	{
	  rxr = 0;
	  req_ff1 = 0;
	  req_ff2 = 0;
	  rx_state_r = RX_IDLE;
	}
      else
	{
	  if (req_ff2 == 1)
	    rxr = txr;
	  rx_state_r = rx_nextstate;
	  req_ff1 = req;
	  req_ff2 = req_ff1;
	}
    }
    
    
    void hs_rx_logic()
    {
      
      switch(rx_state_r.read())
	{
	case RX_IDLE:
	  rx_en_out = 0;
	  if (req_ff2 == 1)
	    rx_nextstate = RX_ACK;
	  else
	    rx_nextstate = RX_IDLE;
	  break;
	  
	case RX_ACK:
	  if (req_ff2 == 0)
	    {
	      rx_en_out = 1;
	      rx_nextstate = RX_IDLE;
	    }
	  else
	    {
	      rx_en_out = 0;
	      rx_nextstate = RX_ACK;
	    }
	  break;
	  
	default: 
	  rx_en_out = 0;
	  rx_nextstate = RX_IDLE;	            
	  
	}
      
      ack = rx_state_r.read()[1];
      rx_out = rxr;
    }
    
    SC_CTOR(cdc_handshake) {
      
      SC_METHOD(hs_tx_regs);
      sensitive << clk1.pos() << rst1_n.neg();
      dont_initialize();

      SC_METHOD(hs_tx_logic);
      sensitive << tx_en_in << tx_state_r << ack_ff2;
      dont_initialize();

      SC_METHOD(hs_rx_regs);
      sensitive << clk2.pos() << rst2_n.neg();
      dont_initialize();

      SC_METHOD(hs_rx_logic);
      sensitive << rx_state_r << req_ff2;
      dont_initialize();

    }

};

#endif
#endif
