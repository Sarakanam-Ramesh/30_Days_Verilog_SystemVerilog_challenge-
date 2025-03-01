`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 24.02.2025 20:35:58
// Design Name: 
// Module Name: bitwise_operator_demo _tb
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


module bitwise_operator_demo_tb;
    // Testbench signals
    reg [3:0] a, b;
    wire [3:0] and_result, or_result, xor_result, not_a;
    wire [3:0] nand_result, nor_result, xnor_result;
    
    // Instantiate the DUT
    bitwise_operator_demo DUT (
        .a(a),
        .b(b),
        .and_result(and_result),
        .or_result(or_result),
        .xor_result(xor_result),
        .not_a(not_a),
        .nand_result(nand_result),
        .nor_result(nor_result),
        .xnor_result(xnor_result)
    );
    
    // Test stimulus
    initial begin
        $display("Bitwise Operator Demonstration");
        $display("A\tB\tA&B\tA|B\tA^B\t~A\t~(A&B)\t~(A|B)\t~(A^B)");
        $display("--\t--\t---\t---\t---\t---\t------\t------\t------");
        
        // Test case 1
        a = 4'b1010; b = 4'b1100;
        #10;
        $display("%b\t%b\t%b\t%b\t%b\t%b\t%b\t%b\t%b", 
                 a, b, and_result, or_result, xor_result, not_a, 
                 nand_result, nor_result, xnor_result);
                 
        // Test case 2
        a = 4'b0011; b = 4'b0101;
        #10;
        $display("%b\t%b\t%b\t%b\t%b\t%b\t%b\t%b\t%b", 
                 a, b, and_result, or_result, xor_result, not_a, 
                 nand_result, nor_result, xnor_result);
        
        #10 $finish;
    end
endmodule
