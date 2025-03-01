`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 24.02.2025 20:43:56
// Design Name: 
// Module Name: sv_enhanced_comparator_tb
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


module sv_enhanced_comparator_tb;
    // Testbench signals
    logic [3:0] data;
    logic in_range1, in_range2, in_range3;
    
    // Instantiate the DUT
    sv_enhanced_comparator DUT (
        .data(data),
        .in_range1(in_range1),
        .in_range2(in_range2),
        .in_range3(in_range3)
    );
    
    // Test stimulus
    initial begin
        $display("Enhanced Comparator Test Using Inside Operator");
        $display("Data\tRange[3:7]\tValues{2,5,9}\tRange[10:15]");
        $display("----\t---------\t------------\t-----------");
        
        // Test all possible 4-bit values
        for (data = 0; data < 16; data++) begin
            #10;
            $display("%d\t%b\t\t%b\t\t%b", data, in_range1, in_range2, in_range3);
        end
        
        #10 $finish;
    end
endmodule
