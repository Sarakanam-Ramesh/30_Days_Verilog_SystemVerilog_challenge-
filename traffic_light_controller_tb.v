`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 03.03.2025 18:57:27
// Design Name: 
// Module Name: traffic_light_controller_tb
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


module traffic_light_tb;
    // Signals
    reg clk;
    reg rst_n;
    wire red, yellow, green;
    
    // Instantiate the DUT
    traffic_light_controller dut (
        .clk(clk),
        .rst_n(rst_n),
        .red(red),
        .yellow(yellow),
        .green(green)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 10ns period
    end
    
    // Test sequence
    initial begin
        $display("Time\tReset\tRed\tYellow\tGreen");
        $monitor("%0t\t%b\t%b\t%b\t%b", $time, rst_n, red, yellow, green);
        
        // Reset sequence
        rst_n = 0;
        repeat(2) @(posedge clk);
        rst_n = 1;
        
        // Run for 30 cycles to observe multiple state transitions
        repeat(30) @(posedge clk);
        
        // Reset again and run a bit more
        rst_n = 0;
        repeat(2) @(posedge clk);
        rst_n = 1;
        repeat(20) @(posedge clk);
        
        $display("Simulation complete");
        $finish;
    end
endmodule
