`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 25.02.2025 19:45:56
// Design Name: 
// Module Name: sv_data_latch_tb
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
////////////////////////////////////////////////////////////////////////////////////
// SystemVerilog Testbench for Latch Implementation
module sv_latch_tb;
    // Testbench signals
    logic   clk, reset, enable, clear;
    logic [7:0]  data_in;
    logic [7:0]  simple_latch_out;
    logic [7:0]  registered_latch_out;
    // Instantiate the simple latch DUT
    sv_data_latch #( .WIDTH(8) ) simple_latch ( .enable(enable), .data_in(data_in), .data_out(simple_latch_out));
    // Instantiate the registered latch DUT
    sv_registered_latch registered_latch ( .clk(clk), .reset(reset), .enable(enable), .clear(clear), .data_in(data_in), .data_out(registered_latch_out) );
    // Clock generation (10ns period)
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    // Test sequence
    initial begin
        // Initialize signals
        reset = 1'b1;
        enable = 1'b0;
        clear = 1'b0;
        data_in = 8'h00;
        // Display information
        $display("SystemVerilog Latch Testbench");
        $monitor("Time=%0t, enable=%b, clear=%b, data_in=%h, simple_latch=%h, registered_latch=%h", $time, enable, clear, data_in, simple_latch_out, registered_latch_out);
        #20 reset = 1'b0;        // Release reset
        // Test latch behavior
        #10 data_in = 8'h55;      // Data changes but not latched
        #10 enable = 1'b1;        // Enable latch to capture data
        #10 data_in = 8'hAA;      // Change data while enabled (transparent)
        #10 enable = 1'b0;        // Disable latch to hold data
        #10 data_in = 8'h33;      // Change data but shouldn't affect output
        // Test clear operation
        #10 clear = 1'b1;         // Clear the latch
        #10 clear = 1'b0;
        // Test latch again after clear
        #10 enable = 1'b1;        // Enable latch
        #10 data_in = 8'h77;      // New data
        #10 enable = 1'b0;        // Disable latch
        // End simulation
        #20; $display("Simulation complete");
        $finish;
    end
endmodule
