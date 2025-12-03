`include "audioport.svh"

import audioport_pkg::*;

module cdc_unit
  (
   input logic 	       clk,
   input logic 	       rst_n,
   input logic 	       test_mode_in,
   input logic [23:0]  audio0_in,
   input logic [23:0]  audio1_in,
   input logic 	       play_in,
   input logic 	       tick_in,
   output logic        req_out,

   input logic 	       mclk,
   output logic        muxclk_out,
   output logic        muxrst_n_out,
   output logic [23:0] audio0_out,
   output logic [23:0] audio1_out, 
   output logic        play_out,
   output logic        tick_out,
   input logic 	       req_in		
   );
   
   logic 	       mrst_n;
   logic 	       muxrst_n;
   logic 	       muxclk;
   logic 	       rsync_clk;

// Internal signals for bit_sync logic
    logic play_in_sync1;          // First stage of play_in synchronizer
    logic play_in_sync2;          // Second stage of play_in synchronizer

// Internal signals for pulse_sync logic
    logic req_in_sync1;           // First stage of req_in synchronizer
    logic req_in_sync2;           // Second stage of req_in synchronizer
    logic req_in_prev;            // Previous state of req_in_sync2 (for edge detection)

// Internal signals for audio_sync logic
 reg [23:0] audio0_reg, audio1_reg;   // Register for input audio data
reg tick_reg;                        // Register for tick_in signal
reg handshake_req;                    // Handshake request signal in clk domain
reg handshake_ack;                    // Handshake acknowledgment in mclk domain

// Synchronization registers
reg handshake_req_sync1, handshake_req_sync2;
reg handshake_ack_sync1, handshake_ack_sync2;
reg tick_out_reg, tick_prev;



//--------------------------------------------------
    // TESTMUX Logic
    //--------------------------------------------------
    // Multiplex the clock and reset signals based on test_mode_in
    assign muxclk = test_mode_in ? clk : mclk;       // Select clk in test mode, mclk in normal mode
    assign rsync_clk = test_mode_in ? clk : ~mclk; 
    assign muxrst_n = test_mode_in ? rst_n : mrst_n; // Select rst_n in test mode, mrst_n in normal mode

    // Output the multiplexed clock and reset signals
    assign muxclk_out = muxclk;
    assign muxrst_n_out = muxrst_n;    // Internal signals for synchronization


//--------------------------------------------------
    // Reset Synchronization Logic (for mrst_n)
    //--------------------------------------------------
    logic mrst_n_sync1, mrst_n_sync2; // Synchronizer flip-flops

    always_ff @(posedge rsync_clk or negedge rst_n) begin
        if (!rst_n) begin
            mrst_n_sync1 <= 1'b0;
            mrst_n_sync2 <= 1'b0;
        end else begin
            mrst_n_sync1 <= 1'b1;       // Synchronize rst_n to muxclk domain
            mrst_n_sync2 <= mrst_n_sync1;
        end
    end

    assign mrst_n = mrst_n_sync2; // Synchronized reset signal for muxclk domain

//--------------------------------------------------
    // BIT_SYNC Logic (for play_in)
    //--------------------------------------------------
    always_ff @(posedge muxclk or negedge muxrst_n) begin
        if (!muxrst_n) begin
            play_in_sync1 <= 1'b0; // Reset synchronizer flip-flops
            play_in_sync2 <= 1'b0;
        end else begin
            play_in_sync1 <= play_in;    // First stage of synchronization
            play_in_sync2 <= play_in_sync1; // Second stage of synchronization
        end
    end

    assign play_out = play_in_sync2; // Synchronized play_in signal


 
//--------------------------------------------------
// PULSE_SYNC Logic (for req_in)
//--------------------------------------------------
// Step 1: Synchronize `req_in` to `clk` domain using 2 flip-flops
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        req_in_sync1 <= 1'b0;
        req_in_sync2 <= 1'b0;
        req_in_prev  <= 1'b0;  // Additional flip-flop to store previous state
    end 
    else begin
        req_in_sync1 <= req_in;     // First stage of synchronization
        req_in_sync2 <= req_in_sync1; // Second stage of synchronization
        req_in_prev  <= req_in_sync2; // Third flip-flop: Stores previous state
    end
end

// Step 2: Generate One-Cycle Pulse on Rising Edge of `req_in_sync2`
assign req_out = req_in_sync2 & ~req_in_prev;  // Rising edge detection 


//--------------------------------------------------
// AUDIO_SYNC Logic (Multi-Bit Synchronization with Handshaking)
//--------------------------------------------------

// Step 1: Capture `audio_in` and `tick_in` in `clk` domain
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        audio0_reg <= 24'b0;
        audio1_reg <= 24'b0;
        tick_reg <= 1'b0;
        handshake_req <= 1'b0;
    end else begin
        if (tick_in) begin
            audio0_reg <= audio0_in;
            audio1_reg <= audio1_in;
            tick_reg <= 1'b1;
            handshake_req <= 1'b1; // Start handshake request
        end else if (handshake_ack_sync2) begin
            tick_reg <= 1'b0;
            handshake_req <= 1'b0; // Clear request after acknowledgment
        end
    end
end

// Step 2: Synchronize `handshake_req` to `muxclk` domain
always_ff @(posedge muxclk or negedge muxrst_n) begin
    if (!muxrst_n) begin
        handshake_req_sync1 <= 1'b0;
        handshake_req_sync2 <= 1'b0;
    end else begin
        handshake_req_sync1 <= handshake_req;
        handshake_req_sync2 <= handshake_req_sync1;
    end
end

// Step 3: Generate `handshake_ack` in `muxclk` domain when `handshake_req_sync2` is received
always_ff @(posedge muxclk or negedge muxrst_n) begin
    if (!muxrst_n) begin
        handshake_ack <= 1'b0;
    end else begin
        if (handshake_req_sync2) begin
            handshake_ack <= 1'b1;
        end else begin
            handshake_ack <= 1'b0; // Immediately deassert after one cycle
        end
    end
end

// Step 4: Synchronize `handshake_ack` back to `clk` domain
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        handshake_ack_sync1 <= 1'b0;
        handshake_ack_sync2 <= 1'b0;
    end else begin
        handshake_ack_sync1 <= handshake_ack;
        handshake_ack_sync2 <= handshake_ack_sync1;
    end
end

// Step 5: Transfer synchronized audio data and generate `tick_out` for exactly one cycle
always_ff @(posedge muxclk or negedge muxrst_n) begin
    if (!muxrst_n) begin
        audio0_out <= 24'b0;
        audio1_out <= 24'b0;
        tick_out_reg <= 1'b0;
        tick_prev <= 1'b0;
    end else begin
        tick_prev <= handshake_req_sync2;

        if (handshake_req_sync2 && !tick_prev) begin  // Rising edge detection
            audio0_out <= audio0_reg;
            audio1_out <= audio1_reg;
            tick_out_reg <= 1'b1;
        end else begin
            tick_out_reg <= 1'b0; // Ensures tick_out is high for only **one** muxclk cycle
        end
    end
end

assign tick_out = tick_out_reg;



endmodule





