`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 28.02.2025 21:55:37
// Design Name: 
// Module Name: parity_generator_tb
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


module parity_generator_tb;
    // Testbench signals
    reg clk;
    reg rst_n;
    reg [7:0] data_in;
    reg data_valid;
    wire even_parity;
    wire odd_parity;
    
    // Instantiate the device under test
    parity_generator dut (
        .clk(clk),
        .rst_n(rst_n),
        .data_in(data_in),
        .data_valid(data_valid),
        .even_parity(even_parity),
        .odd_parity(odd_parity)
    );
    
    // Clock generation
    always #5 clk = ~clk;
    
    // Test stimulus
    initial begin
        // Initialize signals
        clk = 0;
        rst_n = 0;
        data_in = 8'h00;
        data_valid = 0;
        
        // Release reset
        #20 rst_n = 1;
        
        // Test case 1: Data with even number of 1's
        #10;
        data_in = 8'b10101010; // 4 ones
        data_valid = 1;
        #10;
        data_valid = 0;
        #10;
        $display("Test Case 1: Data = %b (4 ones)", data_in);
        $display("Even Parity = %b (Expected: 0)", even_parity);
        $display("Odd Parity = %b (Expected: 1)", odd_parity);
        
        // Test case 2: Data with odd number of 1's
        #10;
        data_in = 8'b10101011; // 5 ones
        data_valid = 1;
        #10;
        data_valid = 0;
        #10;
        $display("Test Case 2: Data = %b (5 ones)", data_in);
        $display("Even Parity = %b (Expected: 1)", even_parity);
        $display("Odd Parity = %b (Expected: 0)", odd_parity);
        
        // Test case 3: All zeros
        #10;
        data_in = 8'b00000000; // 0 ones
        data_valid = 1;
        #10;
        data_valid = 0;
        #10;
        $display("Test Case 3: Data = %b (0 ones)", data_in);
        $display("Even Parity = %b (Expected: 0)", even_parity);
        $display("Odd Parity = %b (Expected: 1)", odd_parity);
        
        // Test case 4: All ones
        #10;
        data_in = 8'b11111111; // 8 ones
        data_valid = 1;
        #10;
        data_valid = 0;
        #10;
        $display("Test Case 4: Data = %b (8 ones)", data_in);
        $display("Even Parity = %b (Expected: 0)", even_parity);
        $display("Odd Parity = %b (Expected: 1)", odd_parity);
        
        #20 $finish;
    end
endmodule
