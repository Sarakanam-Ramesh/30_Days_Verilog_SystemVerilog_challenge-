`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 24.02.2025 20:31:52
// Design Name: 
// Module Name: magnitude_comparator_tb
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


module magnitude_comparator_tb;
    // Testbench signals
    reg [3:0] a, b;
    wire a_gt_b, a_eq_b, a_lt_b;
    
    // Instantiate the DUT
    magnitude_comparator DUT (
        .a(a),
        .b(b),
        .a_gt_b(a_gt_b),
        .a_eq_b(a_eq_b),
        .a_lt_b(a_lt_b)
    );
    
    // Test stimulus
    initial begin
        $display("4-bit Magnitude Comparator Test");
        $display("A\tB\tA>B\tA=B\tA<B");
        $display("--\t--\t---\t---\t---");
        
        // Test cases
        a = 4'd5; b = 4'd3;
        #10 $display("%d\t%d\t%b\t%b\t%b", a, b, a_gt_b, a_eq_b, a_lt_b);
        
        a = 4'd7; b = 4'd7;
        #10 $display("%d\t%d\t%b\t%b\t%b", a, b, a_gt_b, a_eq_b, a_lt_b);
        
        a = 4'd2; b = 4'd10;
        #10 $display("%d\t%d\t%b\t%b\t%b", a, b, a_gt_b, a_eq_b, a_lt_b);
        
        a = 4'd0; b = 4'd0;
        #10 $display("%d\t%d\t%b\t%b\t%b", a, b, a_gt_b, a_eq_b, a_lt_b);
        
        a = 4'd15; b = 4'd8;
        #10 $display("%d\t%d\t%b\t%b\t%b", a, b, a_gt_b, a_eq_b, a_lt_b);
        
        #10 $finish;
    end
endmodule
