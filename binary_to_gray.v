`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 24.02.2025 20:26:58
// Design Name: 
// Module Name: binary_to_gray
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


module binary_to_gray (
    input [3:0] binary_in,
    output [3:0] gray_out
);
    // Gray code conversion: G[i] = B[i] ^ B[i+1]
    // For the MSB, G[3] = B[3]
    assign gray_out[3] = binary_in[3];
    assign gray_out[2] = binary_in[3] ^ binary_in[2];
    assign gray_out[1] = binary_in[2] ^ binary_in[1];
    assign gray_out[0] = binary_in[1] ^ binary_in[0];

endmodule