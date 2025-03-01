`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 25.02.2025 19:36:46
// Design Name: 
// Module Name: sv_clock_divider_tb
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


// SystemVerilog Testbench for Clock Divider
module sv_clock_divider_tb;
    // Parameters
    localparam int DIVIDE_BY = 4;
    localparam int CLK_PERIOD = 10;
    
    // Testbench signals
    logic clk_in;
    logic reset;
    logic clk_out;
    
    // Instantiate the DUT with parameter override
    sv_clock_divider #(
        .DIVIDE_BY(DIVIDE_BY)
    ) dut (
        .clk_in(clk_in),
        .reset(reset),
        .clk_out(clk_out)
    );
    
    // Clock generation
    initial begin
        clk_in = 1'b0;
        forever #(CLK_PERIOD/2) clk_in = ~clk_in;
    end
    // Test sequence
    initial begin
        // Initialize
        reset = 1'b1;
        // Display information
        $display("SystemVerilog Clock Divider Testbench - Dividing by %0d", DIVIDE_BY);
        $monitor("Time=%0t, clk_in=%b, reset=%b, clk_out=%b", $time, clk_in, reset, clk_out);
        // Release reset after a few clock cycles
        #(CLK_PERIOD*3) reset = 1'b0;
        // Run simulation for enough cycles to see the divided clock
        #(CLK_PERIOD*DIVIDE_BY*5);
        // End simulation
        $display("Simulation complete");
        $finish;
    end
endmodule
