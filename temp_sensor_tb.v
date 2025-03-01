`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 23.02.2025 11:51:50
// Design Name: 
// Module Name: temp_sensor_tb
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


module temp_sensor_tb;
    reg clk;
    reg rst;
    reg [7:0] sensor_in;
    wire [7:0] temp_out;

    // Instantiate the temperature sensor
    temp_sensor dut (
        .clk(clk),
        .rst(rst),
        .sensor_in(sensor_in),
        .temp_out(temp_out)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Test stimulus
    initial begin

        // Initialize inputs
        rst = 1;
        sensor_in = 0;
        #10 rst = 0;

        // Test different temperature values
        #10 sensor_in = 8'd20;
        #10 sensor_in = 8'd40;
        #10 sensor_in = 8'd60;
        #10 sensor_in = 8'd80;

        #100 $finish;
    end

    // Monitor changes
    initial begin
        $monitor("Time=%0t rst=%b sensor_in=%d temp_out=%d", 
                 $time, rst, sensor_in, temp_out);
    end
endmodule