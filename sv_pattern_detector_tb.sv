`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 24.02.2025 20:48:15
// Design Name: 
// Module Name: sv_pattern_detector_tb
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


module sv_pattern_detector_tb;
    // Testbench signals
    logic [7:0] data;
    logic has_pattern1, has_pattern2, has_pattern3;
    
    // Instantiate the DUT
    sv_pattern_detector DUT (
        .data(data),
        .has_pattern1(has_pattern1),
        .has_pattern2(has_pattern2),
        .has_pattern3(has_pattern3)
    );
    
    // Test stimulus
    initial begin
        $display("Pattern Detector Test Using Wildcard Equality");
        $display("Data\t\t10xx01xx\t11??00??\tx1x0x1x0");
        $display("--------\t--------\t--------\t--------");
        
        // Test specific patterns
        data = 8'b10110100; #10;
        $display("%b\t%b\t\t%b\t\t%b", data, has_pattern1, has_pattern2, has_pattern3);
        
        data = 8'b11000011; #10;
        $display("%b\t%b\t\t%b\t\t%b", data, has_pattern1, has_pattern2, has_pattern3);
        
        data = 8'b01001010; #10;
        $display("%b\t%b\t\t%b\t\t%b", data, has_pattern1, has_pattern2, has_pattern3);
        
        data = 8'b10010111; #10;
        $display("%b\t%b\t\t%b\t\t%b", data, has_pattern1, has_pattern2, has_pattern3);
        
        data = 8'b11100010; #10;
        $display("%b\t%b\t\t%b\t\t%b", data, has_pattern1, has_pattern2, has_pattern3);
        
        #10 $finish;
    end
endmodule
