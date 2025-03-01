`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 22.02.2025 21:31:28
// Design Name: 
// Module Name: counter_structural_tb
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


module counter_structural_tb;
    reg clk;
    reg rst;
    wire [7:0] count;

    // Instantiate the counter
    counter_structural dut (
        .clk(clk),
        .clear(rst),
        .q(count)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Test stimulus
    initial begin

        // Reset sequence
        rst = 1;
        #10 rst = 0;

        // Let counter run for some cycles
        #1000;

        // End simulation
        $finish;
    end

    // Monitor changes
    initial begin
        $monitor("Time=%0t rst=%b count=%d", $time, rst, count);
    end

endmodule
