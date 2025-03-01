`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 23.02.2025 11:54:08
// Design Name: 
// Module Name: status_register_tb
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


module status_register_tb;
    reg clk;
    reg rst;
    reg error_in;
    reg busy_in;
    reg done_in;
    wire [2:0] status;

    // Instantiate the status register
    status_register dut (.clk(clk), .rst(rst), .error_in(error_in), .busy_in(busy_in), .done_in(done_in), .status(status));

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Test stimulus
    initial begin

        // Initialize inputs
        rst = 1;
        error_in = 0;
        busy_in = 0;
        done_in = 0;
        #10 rst = 0;

        // Test different status combinations
        #10 error_in = 1;
        #10 busy_in = 1;
        #10 done_in = 1;
        #10 error_in = 0; busy_in = 0;
        #10 done_in = 0;

        #100 $finish;
    end

    // Monitor changes
    initial begin
        $monitor("Time=%0t rst=%b error=%b busy=%b done=%b status=%b", 
                 $time, rst, error_in, busy_in, done_in, status);
    end
endmodule
