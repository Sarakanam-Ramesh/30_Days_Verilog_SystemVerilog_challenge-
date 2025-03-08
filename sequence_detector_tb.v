`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 03.03.2025 19:12:09
// Design Name: 
// Module Name: sequence_detector_tb
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


module sequence_detector_tb;
    // Signals
    reg clk;
    reg rst_n;
    reg data_in;
    wire detected;
    
    // Test sequence
    reg [15:0] test_sequence = 16'b0101101010110101;
    integer i;
    
    // Instantiate the DUT
    sequence_detector dut (
        .clk(clk),
        .rst_n(rst_n),
        .data_in(data_in),
        .detected(detected)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 10ns period
    end
    
    // Test sequence
    initial begin
        $display("Time\tInput\tDetected\tSequence");
        
        // Reset sequence
        rst_n = 0;
        data_in = 0;
        #10 rst_n = 1;
        
        // Apply test sequence
        for (i = 0; i < 16; i = i + 1) begin
            @(posedge clk);
            data_in = test_sequence[15-i];
            #1; // Small delay to let outputs stabilize
            $display("%0t\t%b\t%b\t%s", $time, data_in, detected, 
                     detected ? "101 Detected!" : "Searching...");
        end
        
        // Test a few explicit sequences
        // Sequence 1: 10101 (should detect 101 twice)
        #10 rst_n = 0;
        #10 rst_n = 1;
        
        @(posedge clk) data_in = 1; #1 $display("%0t\t%b\t%b", $time, data_in, detected);
        @(posedge clk) data_in = 0; #1 $display("%0t\t%b\t%b", $time, data_in, detected);
        @(posedge clk) data_in = 1; #1 $display("%0t\t%b\t%b", $time, data_in, detected);
        @(posedge clk) data_in = 0; #1 $display("%0t\t%b\t%b", $time, data_in, detected);
        @(posedge clk) data_in = 1; #1 $display("%0t\t%b\t%b", $time, data_in, detected);
        
        $display("Simulation complete");
        $finish;
    end
endmodule
