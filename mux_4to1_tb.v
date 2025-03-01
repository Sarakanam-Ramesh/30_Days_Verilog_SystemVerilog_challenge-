`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 26.02.2025 20:59:04
// Design Name: 
// Module Name: mux_4to1_tb
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


module mux_4to1_tb;
    // Testbench signals
    reg [1:0] sel;
    reg [3:0] data_in;
    wire out;
    
    // Instantiate the DUT (Device Under Test)
    mux_4to1 DUT (
        .sel(sel),
        .data_in(data_in),
        .out(out)
    );
    
    // Test stimulus
    initial begin
        
        // Test Case 1: All different inputs
        data_in = 4'b1010;
        sel = 2'b00; #10;  // Should select data_in[0] = 0
        sel = 2'b01; #10;  // Should select data_in[1] = 1
        sel = 2'b10; #10;  // Should select data_in[2] = 0
        sel = 2'b11; #10;  // Should select data_in[3] = 1
        
        // Test Case 2: All zeros
        data_in = 4'b0000;
        sel = 2'b00; #10;
        sel = 2'b01; #10;
        sel = 2'b10; #10;
        sel = 2'b11; #10;
        
        // Test Case 3: All ones
        data_in = 4'b1111;
        sel = 2'b00; #10;
        sel = 2'b01; #10;
        sel = 2'b10; #10;
        sel = 2'b11; #10;
        
        $display("Test completed");
        $finish;
    end
endmodule