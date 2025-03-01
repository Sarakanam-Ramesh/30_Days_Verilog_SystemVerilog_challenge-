`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 24.02.2025 20:31:29
// Design Name: 
// Module Name: magnitude_comparator
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


module magnitude_comparator (
    input [3:0] a,
    input [3:0] b,
    output a_gt_b,    // a > b
    output a_eq_b,    // a = b
    output a_lt_b     // a < b
);
    // Compare equality
    assign a_eq_b = (a == b);
    
    // Compare greater than
    assign a_gt_b = (a > b);
    
    // Compare less than
    assign a_lt_b = (a < b);

endmodule
