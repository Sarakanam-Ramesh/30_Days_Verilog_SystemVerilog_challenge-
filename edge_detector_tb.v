`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 25.02.2025 18:55:32
// Design Name: 
// Module Name: edge_detector_tb
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments: 
//////////////////////////////////////////////////////////////////////////////////
// Testbench for Edge Detector
module edge_detector_tb;
    // Testbench signals
    reg clk;
    reg reset;
    reg signal_in;
    wire rising_edge;
    wire falling_edge;
    
    // Instantiate the DUT
    edge_detector dut (
        .clk(clk),
        .reset(reset),
        .signal_in(signal_in),
        .rising_edge(rising_edge),
        .falling_edge(falling_edge)
    );
    // Clock generation (10ns period)
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    // Test sequence
    initial begin
        // Initialize
        reset = 1;
        signal_in = 0;
        // Display information
        $display("Edge Detector Testbench");
        $monitor("Time=%0t, signal_in=%b, rising_edge=%b, falling_edge=%b", $time, signal_in, rising_edge, falling_edge);
        // Release reset
        #20 reset = 0;
        // Create signal transitions to test edge detection
        #20 signal_in = 1;  // Rising edge
        #20 signal_in = 0;  // Falling edge
        #20 signal_in = 1;  // Rising edge
        #20 signal_in = 1;  // No edge
        #20 signal_in = 0;  // Falling edge
        // Run a bit longer and finish
        #20;
        $display("Simulation complete");
        $finish;
    end
endmodule
