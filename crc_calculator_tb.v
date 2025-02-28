`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 28.02.2025 22:07:05
// Design Name: 
// Module Name: crc_calculator_tb
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


module crc_calculator_tb;
    // Testbench signals
    reg clk;
    reg rst_n;
    reg data_in;
    reg data_valid;
    wire [7:0] crc_out;
    wire crc_valid;
    
    // Test data (8'hA5 = 10100101)
    reg [7:0] test_data;
    integer i;
    
    // Instantiate the device under test
    crc_calculator dut (
        .clk(clk),
        .rst_n(rst_n),
        .data_in(data_in),
        .data_valid(data_valid),
        .crc_out(crc_out),
        .crc_valid(crc_valid)
    );
    
    // Clock generation
    always #5 clk = ~clk;
    
    // Test stimulus
    initial begin
        // Initialize signals
        clk = 0;
        rst_n = 0;
        data_in = 0;
        data_valid = 0;
        test_data = 8'hA5; // Test data
        
        // Release reset
        #20 rst_n = 1;
        
        // Send test data bit by bit
        #10;
        $display("Sending test data: %h (binary: %b)", test_data, test_data);
        
        for (i = 7; i >= 0; i = i - 1) begin
            data_in = test_data[i];
            data_valid = 1;
            #10;
        end
        
        data_valid = 0;
        
        // Wait for CRC valid
        wait(crc_valid);
        $display("CRC output: %h", crc_out);
        
        // Test another data pattern (8'h3C = 00111100)
        #20;
        test_data = 8'h3C;
        $display("Sending test data: %h (binary: %b)", test_data, test_data);
        
        for (i = 7; i >= 0; i = i - 1) begin
            data_in = test_data[i];
            data_valid = 1;
            #10;
        end
        
        data_valid = 0;
        
        // Wait for CRC valid
        wait(crc_valid);
        $display("CRC output: %h", crc_out);
        
        #20 $finish;
    end
endmodule
