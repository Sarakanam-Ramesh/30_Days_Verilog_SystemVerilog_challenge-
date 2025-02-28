`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 28.02.2025 21:45:33
// Design Name: 
// Module Name: bcd_to_7seg
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


module bcd_to_7seg (
    input [3:0] bcd_in,
    output reg [6:0] seg_out
);
    // Function to convert BCD to 7-segment display code
    // seg_out[6:0] represents segments a,b,c,d,e,f,g (active low)
    function [6:0] bcd_decode;
        input [3:0] bcd;
        begin
            case (bcd)
                4'd0: bcd_decode = 7'b1000000; // 0
                4'd1: bcd_decode = 7'b1111001; // 1
                4'd2: bcd_decode = 7'b0100100; // 2
                4'd3: bcd_decode = 7'b0110000; // 3
                4'd4: bcd_decode = 7'b0011001; // 4
                4'd5: bcd_decode = 7'b0010010; // 5
                4'd6: bcd_decode = 7'b0000010; // 6
                4'd7: bcd_decode = 7'b1111000; // 7
                4'd8: bcd_decode = 7'b0000000; // 8
                4'd9: bcd_decode = 7'b0010000; // 9
                default: bcd_decode = 7'b1111111; // All segments off for invalid input
            endcase
        end
    endfunction

    // Use the function to drive the output
    always @(*) begin
        seg_out = bcd_decode(bcd_in);
    end
endmodule 
