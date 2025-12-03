// assertion_tb.sv: Simple testbench for debugging assertions 
//
// Usage:
//      1. Create a scenario where an assertion a_X based on property X should
//         PASS and FAIL in the initial proceudre below
//      2. Run the script to verify that the waveforms look OK
//         vsim -do scripts/assertion_tb.tcl
//      3. Declare the property and assertions below the initial process
//      4. Run the script again. The script puts all assertions in the Wave window.
//         Expand an assertion (+) and its ActiveCount (+) to view evaluation details
//      5. To get a detailed view of assertion evaluation, do the following:
//         a) Activate the Assertions tab
//         b) Select an assertion
//         c) Using the right button, execure View ATV.. and select a specific
//            passing or failure of the assertion (ATV = assertion thread view)
//         d) You can now follow the evaluation of property expressions in time
// 

import audioport_pkg::*;
module assertion_tb;

    // Clock and reset
    logic clk = 0, rst_n = 0;
    always #10ns clk = ~clk;
    initial begin
        rst_n = 0;
        #20ns rst_n = 1;  // Active after two clock edges to ensure clean reset
    end

    logic play_out, tick_out, irq_out;
    logic PSEL, PENABLE, PWRITE, PREADY;
    logic [31:0] PADDR, PWDATA;
    parameter int AUDIO_FIFO_SIZE = 8;
    parameter LEFT_FIFO_ADDRESS = 32'h1000;
    parameter RIGHT_FIFO_ADDRESS = 32'h1004;
    parameter CMD_REG_ADDRESS = 32'h1008;
    parameter CMD_IRQACK = 32'hAAAA;

    ///////////////////////////////////////////////////////////////////
    // Test data generation process
    ///////////////////////////////////////////////////////////////////

    initial begin
        // Resetting signals
        play_out = 0;
        tick_out = 0;
        irq_out = 0;
        PSEL = 0;
        PENABLE = 0;
        PWRITE = 0;
        PREADY = 0;
        PADDR = 0;
        PWDATA = 0;
        @(posedge rst_n);
        @(negedge clk);

        // Case: PASS
        // Rising edge on play_out and tick_out pulse AUDIO_FIFO_SIZE times
        // without invalid PADDR or PWDATA settings
        $info("Testing f_irq_out_rise_first - PASS case");
        play_out = 1;
        repeat (AUDIO_FIFO_SIZE) begin
            tick_out = 1;
            @(negedge clk);
            tick_out = 0;
            @(negedge clk);
        end
        irq_out = 1; // irq_out should be asserted here
        @(negedge clk);

        // Case: FAIL
        // Introduce error by writing to LEFT_FIFO_ADDRESS with CMD_IRQACK
        $info("Testing f_irq_out_rise_first - FAIL case");
        play_out = 1; PSEL = 1; PENABLE = 1; PWRITE = 1; PREADY = 1;
        PADDR = LEFT_FIFO_ADDRESS; PWDATA = CMD_IRQACK;
        repeat (AUDIO_FIFO_SIZE) begin
            tick_out = 1;
            @(negedge clk);
            tick_out = 0;
            @(negedge clk);
        end
        irq_out = 0; // irq_out should not be asserted
        @(negedge clk);

        $finish;
    end

    ///////////////////////////////////////////////////////////////////
    // Properties and assertions
    ///////////////////////////////////////////////////////////////////

    // f_irq_out_rise_first property
    property f_irq_out_rise_first;
        @(posedge clk) disable iff (rst_n == 0)
            $rose(play_out) |-> 
            (##1 tick_out)[*AUDIO_FIFO_SIZE] ##1 1 ##1 1
            and (!(PSEL && PENABLE && PREADY && PWRITE && 
                  (PADDR == LEFT_FIFO_ADDRESS || PADDR == RIGHT_FIFO_ADDRESS || 
                   (PADDR == CMD_REG_ADDRESS && PWDATA == CMD_IRQACK))) throughout play_out)
            |-> irq_out;
    endproperty;

    assert property (f_irq_out_rise_first)
        else $error("f_irq_out_rise_first assertion failed.");

endmodule

