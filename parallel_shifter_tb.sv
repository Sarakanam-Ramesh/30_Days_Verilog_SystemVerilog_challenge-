`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06.03.2025 18:51:35
// Design Name: 
// Module Name: parallel_shifter_tb
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


module parallel_shifter_tb;
    parameter WIDTH = 8;
    parameter MAX_SHIFT = 4;
    
    logic clk, rst_n;
    logic [WIDTH-1:0] data_in;
    logic [$clog2(MAX_SHIFT+1)-1:0] shift_amt;
    logic shift_left;
    logic [WIDTH-1:0] data_out;
    
    // Instantiate the DUT
    parallel_shifter #(
        .WIDTH(WIDTH),
        .MAX_SHIFT(MAX_SHIFT)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .data_in(data_in),
        .shift_amt(shift_amt),
        .shift_left(shift_left),
        .data_out(data_out)
    );
    
    // Clock generation
    always #5 clk = ~clk;
    
    // Display results
    initial begin
        $monitor("Time=%0t: data_in=%b, shift_amt=%d, shift_left=%b, data_out=%b", 
                 $time, data_in, shift_amt, shift_left, data_out);
    end
    
    // Test vectors
    initial begin
        // Initialize
        clk = 0; rst_n = 0; data_in = 8'h55; shift_amt = 0; shift_left = 0;
        
        // Release reset
        #15 rst_n = 1;
        
        // Test all shift amounts with left shift
        shift_left = 1;
        for (int i = 0; i <= MAX_SHIFT; i++) begin
            shift_amt = i;
            #10;
        end
        
        // Test all shift amounts with right shift
        shift_left = 0;
        for (int i = 0; i <= MAX_SHIFT; i++) begin
            shift_amt = i;
            #10;
        end
        
        // Test with different data patterns
        data_in = 8'hAA;
        
        // Test all shift amounts with left shift
        shift_left = 1;
        for (int i = 0; i <= MAX_SHIFT; i++) begin
            shift_amt = i;
            #10;
        end
        
        // Test all shift amounts with right shift
        shift_left = 0;
        for (int i = 0; i <= MAX_SHIFT; i++) begin
            shift_amt = i;
            #10;
        end
        
        // Test invalid shift amount (should trigger assertion)
        shift_amt = MAX_SHIFT + 1;
        #10;
        
        // End simulation
        #10 $finish;
    end
endmodule