`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 24.02.2025 20:27:45
// Design Name: 
// Module Name: binary_to_gray_tb
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


module binary_to_gray_tb;
    // Testbench signals
    reg [3:0] binary_in;
    wire [3:0] gray_out;
    
    // Instantiate the DUT (Device Under Test)
    binary_to_gray DUT (
        .binary_in(binary_in),
        .gray_out(gray_out)
    );
    
    // Test stimulus
    initial begin
        $display("Binary to Gray Code Converter Test");
        $display("Binary\tGray");
        $display("------\t----");
        
        for (binary_in = 0; binary_in < 16; binary_in = binary_in + 1) begin
            #10; // Wait for outputs to settle
            $display("%b\t%b", binary_in, gray_out);
        end
        
        #10 $finish;
    end
endmodule
