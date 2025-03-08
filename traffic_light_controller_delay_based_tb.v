`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 08.03.2025 15:41:37
// Design Name: 
// Module Name: traffic_light_controller_delay_based_tb
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


module traffic_light_controller_delay_based_tb();
    reg clk, rst;
    wire red, yellow, green;
    
    // Instantiate the traffic light controller
    traffic_light_controller_delay_based uut (
        .clk(clk),
        .rst(rst),
        .red(red),
        .yellow(yellow),
        .green(green)
    );
    
    // Clock generation
    always #5 clk = ~clk;
    
    // Monitor signals
    initial begin
        $monitor("Time=%0dns: RST=%b RED=%b YELLOW=%b GREEN=%b", 
                 $time, rst, red, yellow, green);
    end
    
    // Test sequence
    initial begin
        $display("Starting Traffic Light Controller Test");
        
        // Initialize
        clk = 0;
        rst = 1;
        
        // Release reset
        #20 rst = 0;
        
        // Run for full cycle plus more
        #1000;
        
        $display("Test Complete");
        $finish;
    end
    
endmodule
