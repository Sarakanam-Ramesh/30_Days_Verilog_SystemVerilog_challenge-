`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 28.02.2025 21:45:57
// Design Name: 
// Module Name: bcd_to_7seg_tb
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


module bcd_to_7seg_tb;
    // Testbench signals
    reg [3:0] bcd_in;
    wire [6:0] seg_out;
    
    // Instantiate the device under test
    bcd_to_7seg dut (
        .bcd_in(bcd_in),
        .seg_out(seg_out)
    );
    
    // Task to display segment pattern
    task display_segment;
        input [6:0] seg;
        begin
            $display(" _");
            $display("|%s|%s", seg[6] ? " " : "_", seg[0] ? " " : "_");
            $display("|%s|%s", seg[5] ? " " : "_", seg[1] ? " " : "_");
            $display(" %s", seg[3] ? " " : "_");
        end
    endtask
    
    // Test stimulus
    initial begin
        $display("BCD to 7-segment Decoder Test");
        $display("---------------------------");
        
        // Test all valid BCD inputs (0-9)
        for (bcd_in = 0; bcd_in <= 9; bcd_in = bcd_in + 1) begin
            #10;
            $display("BCD Input: %0d, 7-Segment Output: %b", bcd_in, seg_out);
            display_segment(seg_out);
        end
        
        // Test invalid BCD inputs
        bcd_in = 10; #10;
        $display("BCD Input: %0d (invalid), 7-Segment Output: %b", bcd_in, seg_out);
        
        bcd_in = 15; #10;
        $display("BCD Input: %0d (invalid), 7-Segment Output: %b", bcd_in, seg_out);
        
        $finish;
    end
endmodule
