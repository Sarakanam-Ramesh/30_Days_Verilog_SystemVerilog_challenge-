`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 23.02.2025 12:00:51
// Design Name: 
// Module Name: sv_packet_tb
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


module sv_packet_tb;
    logic clk;
    logic rst;
    logic [7:0] data_in;
    logic [3:0] dest_in;
    logic valid_in;
    logic [13:0] packet_out;

    sv_packet dut (.*); // Instantiate the packet module

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Test stimulus
    initial begin
        // Initialize inputs
        rst = 1;
        data_in = 0;
        dest_in = 0;
        valid_in = 0;
        #10 rst = 0;
        // Test different packet configurations
        #10 data_in = 8'hA5;
        dest_in = 4'h3;
        valid_in = 1;
        #10 data_in = 8'h55;
        dest_in = 4'h7;
        valid_in = 1;
        #10;
        valid_in = 0;
        #100 $finish;
    end

    // Monitor changes
    initial begin
        $monitor("Time=%0t rst=%b valid_in=%b dest_in=%h data_in=%h packet_out=%h", 
                 $time, rst, valid_in, dest_in, data_in, packet_out);
    end
endmodule