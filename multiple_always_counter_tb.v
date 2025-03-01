`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 25.02.2025 19:23:09
// Design Name: 
// Module Name: multiple_always_counter_tb
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
// Testbench for Multiple Always Block Counter
module multiple_always_counter_tb;
    reg clk; reg reset; reg enable; reg up_down; reg load; reg [7:0] data_in; wire [7:0] count;    // Testbench signals
    // Instantiate the DUT
    multiple_always_counter dut ( .clk(clk), .reset(reset), .enable(enable), .up_down(up_down),  .load(load), .data_in(data_in), .count(count));
    // Clock generation (10ns period)
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    // Test sequence
    initial begin
        // Initialize signals
        reset = 1;
        enable = 0;
        up_down = 1;
        load = 0;
        data_in = 8'h00;
        // Display information
        $display("Multiple Always Block Counter Testbench");
        $monitor("Time=%0t, reset=%b, enable=%b, up_down=%b, load=%b, data_in=%h, count=%h", $time, reset, enable, up_down, load, data_in, count);
        #20 reset = 0;        // Release reset
        // Test load functionality
        #10 load = 1; data_in = 8'h50;
        #10 load = 0;
        // Test count up
        #10 enable = 1; up_down = 1;
        #40;
        // Test count down
        #10 up_down = 0;
        #40;
        // Test load during count
        #10 load = 1; data_in = 8'hA0;
        #10 load = 0;
        // Test count after load
        #40;
        // Test reset
        #10 reset = 1;
        #10 reset = 0;
        // Run a bit longer and finish
        #10;
        $display("Simulation complete");
        $finish;
    end
endmodule
