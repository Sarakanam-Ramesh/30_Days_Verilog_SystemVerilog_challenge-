`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 23.02.2025 11:58:50
// Design Name: 
// Module Name: sv_status_flags_tb
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


module sv_status_flags_tb;
    logic clk;
    logic rst;
    logic [1:0] state_in;
    logic [1:0] state_out;

    // Instantiate the status flags module
    sv_status_flags dut (.*);

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Test stimulus
    initial begin

        // Test reset
        rst = 1;
        state_in = 2'b00;
        #10 rst = 0;

        // Test all states
        #10 state_in = 2'b00; // IDLE
        #10 state_in = 2'b01; // BUSY
        #10 state_in = 2'b10; // DONE
        #10 state_in = 2'b11; // ERROR

        #100 $finish;
    end

    // Monitor changes
    initial begin
        $monitor("Time=%0t rst=%b state_in=%b state_out=%b", 
                 $time, rst, state_in, state_out);
    end

endmodule
