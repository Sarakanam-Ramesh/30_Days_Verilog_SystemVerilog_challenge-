`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 24.02.2025 20:35:41
// Design Name: 
// Module Name: bitwise_operator_demo
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


module bitwise_operator_demo (
    input [3:0] a,
    input [3:0] b,
    output [3:0] and_result,
    output [3:0] or_result,
    output [3:0] xor_result,
    output [3:0] not_a,
    output [3:0] nand_result,
    output [3:0] nor_result,
    output [3:0] xnor_result
);
    // Bitwise AND
    assign and_result = a & b;
    
    // Bitwise OR
    assign or_result = a | b;
    
    // Bitwise XOR
    assign xor_result = a ^ b;
    
    // Bitwise NOT (complement)
    assign not_a = ~a;
    
    // Bitwise NAND
    assign nand_result = ~(a & b);
    
    // Bitwise NOR
    assign nor_result = ~(a | b);
    
    // Bitwise XNOR
    assign xnor_result = ~(a ^ b);

endmodule
