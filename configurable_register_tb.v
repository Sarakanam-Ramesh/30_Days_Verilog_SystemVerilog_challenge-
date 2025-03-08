`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06.03.2025 18:27:45
// Design Name: 
// Module Name: configurable_register_tb
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


module configurable_register_tb;
    parameter WIDTH = 32;
    
    reg clk, rst_n, en;
    reg [WIDTH-1:0] d;
    wire [WIDTH-1:0] q;
    
    // Instantiate the DUT
    configurable_register #(
        .WIDTH(WIDTH)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .en(en),
        .d(d),
        .q(q)
    );
    
    // Clock generation
    always #5 clk = ~clk;
    
    // Display results
    initial begin
        $monitor("Time=%0t: en=%b, d=%h, q=%h", $time, en, d, q);
    end
    
    // Test vectors
    initial begin
        // Initialize
        clk = 0; rst_n = 0; en = 0; d = 0;
        
        // Release reset
        #15 rst_n = 1;
        
        // Test case 1: Load a value with enable high
        #10 en = 1; d = 32'hA5A5A5A5;
        
        // Test case 2: Disable the register and change input
        #10 en = 0; d = 32'h5A5A5A5A;
        
        // Test case 3: Enable again with new value
        #10 en = 1; d = 32'hFFFF0000;
        
        // Test case 4: Apply reset
        #10 rst_n = 0;
        
        // Test case 5: Release reset, load new value
        #10 rst_n = 1; d = 32'h12345678;
        
        // End simulation
        #10 $finish;
    end
endmodule