`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 08.03.2025 16:16:02
// Design Name: 
// Module Name: clock_synchronizer_tb
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
// 
//////////////////////////////////////////////////////////////////////////////////


module clock_synchronizer_tb();
    reg fast_clk, slow_clk, rst, data_in;
    wire data_out_fast, data_out_slow;
    
    // Clock periods
    parameter FAST_CLK_PERIOD = 10;
    parameter SLOW_CLK_PERIOD = 33;
    
    // Instantiate the clock synchronizer
    clock_synchronizer uut (
        .fast_clk(fast_clk),
        .slow_clk(slow_clk),
        .rst(rst),
        .data_in(data_in),
        .data_out_fast(data_out_fast),
        .data_out_slow(data_out_slow)
    );
    
    // Clock generation
    always #(FAST_CLK_PERIOD/2) fast_clk = ~fast_clk;
    always #(SLOW_CLK_PERIOD/2) slow_clk = ~slow_clk;
    
    // Monitor output
    initial begin
        $monitor("Time=%0dns: data_in=%b, data_out_fast=%b, data_out_slow=%b", 
                 $time, data_in, data_out_fast, data_out_slow);
    end
    
    // Test sequence
    initial begin
        $display("Starting Clock Synchronizer Test");
        fast_clk = 0;
        slow_clk = 0;
        rst = 1;
        data_in = 0;
        
        // Release reset
        #25 rst = 0;
        
        // Test data transitions
        #10 data_in = 1;
        #50 data_in = 0;
        #30 data_in = 1;
        #20 data_in = 0;
        #40 data_in = 1;
        
        // Run for a while to observe synchronization
        #200;
        
        $display("Test Complete");
        $finish;
    end
    
endmodule
