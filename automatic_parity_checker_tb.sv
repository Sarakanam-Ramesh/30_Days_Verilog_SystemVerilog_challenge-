`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 28.02.2025 22:14:23
// Design Name: 
// Module Name: automatic_parity_checker_tb
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


module automatic_parity_checker_tb;
    // Testbench signals
    logic clk;
    logic rst_n;
    logic [15:0] data_in;
    logic data_valid;
    logic parity_error;
    
    // Instantiate the device under test
    automatic_parity_checker dut (
        .clk(clk),
        .rst_n(rst_n),
        .data_in(data_in),
        .data_valid(data_valid),
        .parity_error(parity_error)
    );
    
    // Clock generation
    always #5 clk = ~clk;
    
    // Calculate parity for verification
    function automatic logic calc_parity(input logic [15:0] data, input int size);
        logic parity = 1'b0;
        for (int i = 0; i < size; i++) begin
            parity ^= data[i];
        end
        return parity;
    endfunction
    
    // Test stimulus
    initial begin
        // Initialize signals
        clk = 0;
        rst_n = 0;
        data_in = 16'h0000;
        data_valid = 0;
        
        // Release reset
        #20 rst_n = 1;
        
        // Test case 1: 8-bit data with correct parity
        #10;
        // Data: 0x55 = 01010101, parity = 0, put in bits 7:0
        // Parity bit in position 8
        data_in = {7'b0000000, 1'b0, 8'h55};
        data_valid = 1;
        #10;
        data_valid = 0;
        #10;
        $display("Test Case 1: 8-bit data with correct parity");
        $display("Data: %h, Expected parity: %b, Parity error: %b", 
                 data_in[7:0], data_in[8], parity_error);
        
        // Test case 2: 8-bit data with incorrect parity
        #10;
        // Data: 0xAA = 10101010, parity = 0, but send wrong parity (1)
        data_in = {7'b0000000, 1'b1, 8'hAA};
        data_valid = 1;
        #10;
        data_valid = 0;
        #10;
        $display("Test Case 2: 8-bit data with incorrect parity");
        $display("Data: %h, Expected parity: %b, Actual parity: %b, Parity error: %b", 
                 data_in[7:0], data_in[8], calc_parity(data_in[7:0], 8), parity_error);
        
        // Test case 3: 16-bit data with correct parity
        #10;
        // Data: 0x8123 (set MSB to indicate 16-bit mode)
        // Set LSB to correct parity value
        data_in = 16'h8122; // Even parity for 0x8122 is 0
        if (calc_parity(16'h8122, 16) == 1'b1)
            data_in = 16'h8123; // Set LSB to 1 for odd parity
        data_valid = 1;
        #10;
        data_valid = 0;
        #10;
        $display("Test Case 3: 16-bit data with correct parity");
        $display("Data: %h, Expected parity: %b, Parity error: %b", 
                 data_in, data_in[0], parity_error);
        
        // Test case 4: 16-bit data with incorrect parity
        #10;
        // Data: 0x8456, but with incorrect parity
        data_in = 16'h8456;
        if (calc_parity(16'h8456, 16) == 1'b0)
            data_in = 16'h8457; // Set wrong parity
        else
            data_in = 16'h8456; // Set wrong parity
        data_valid = 1;
        #10;
        data_valid = 0;
        #10;
        $display("Test Case 4: 16-bit data with incorrect parity");
        $display("Data: %h, Expected parity: %b, Actual parity: %b, Parity error: %b", 
                 data_in, data_in[0], calc_parity(data_in, 16), parity_error);
        
        #20 $finish;
    end
endmodule
