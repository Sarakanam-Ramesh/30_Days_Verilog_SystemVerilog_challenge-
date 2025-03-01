`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 25.02.2025 18:43:59
// Design Name: 
// Module Name: clock_divider_tb
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


// Testbench for Clock Divider
module clock_divider_tb;
    // Parameters
    parameter DIVIDE_BY = 4;
    parameter CLK_PERIOD = 10;
    
    // Testbench signals
    reg clk_in;
    reg reset;
    wire clk_out;
    
    // Instantiate the DUT with parameter override
    clock_divider #( .DIVIDE_BY(DIVIDE_BY)) dut ( .clk_in(clk_in), .reset(reset), .clk_out(clk_out));
    
    // Clock generation
    initial begin
        clk_in = 0;
        forever #(CLK_PERIOD/2) clk_in = ~clk_in;
    end
    
    // Test sequence
    initial begin
        // Initialize
        reset = 1;
        
        // Display information
        $display("Clock Divider Testbench - Dividing by %0d", DIVIDE_BY);
        $monitor("Time=%0t, clk_in=%b, reset=%b, clk_out=%b", 
                $time, clk_in, reset, clk_out);
        
        // Release reset after a few clock cycles
        #(CLK_PERIOD*3) reset = 0;
        
        // Run simulation for enough cycles to see the divided clock
        #(CLK_PERIOD*DIVIDE_BY*5);
        
        // End simulation
        $display("Simulation complete");
        $finish;
    end
endmodule
