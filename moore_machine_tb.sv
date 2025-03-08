`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 03.03.2025 19:33:10
// Design Name: 
// Module Name: moore_machine_tb
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


module moore_machine_tb;
    // Signals
    logic clk;
    logic rst_n;
    logic data_in;
    logic [1:0] data_out;
    
    // Test sequence
    logic [15:0] test_sequence = 16'b0101101010110101;
    integer i;
    
    // Instantiate the DUT
    moore_machine dut (
        .clk(clk),
        .rst_n(rst_n),
        .data_in(data_in),
        .data_out(data_out)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 10ns period
    end
    
    // Test sequence
    initial begin
        $display("Time\tReset\tInput\tOutput\tState");
        $monitor("%0t\t%b\t%b\t%b", $time, rst_n, data_in, data_out);
        
        // Reset sequence
        rst_n = 0;
        data_in = 0;
        repeat(2) @(posedge clk);
        rst_n = 1;
        
        // Apply test sequence
        for (i = 0; i < 16; i = i + 1) begin
            @(posedge clk);
            data_in = test_sequence[15-i];
            #1; // Small delay to let outputs stabilize
        end
        
        // Test specific sequence: 110100
        rst_n = 0;
        @(posedge clk);
        rst_n = 1;
        
        @(posedge clk) data_in = 1; // S0->S1
        @(posedge clk) data_in = 1; // S1->S2
        @(posedge clk) data_in = 0; // S2->S3
        @(posedge clk) data_in = 1; // S3->S4
        @(posedge clk) data_in = 0; // S4->S0
        @(posedge clk) data_in = 0; // S0->S0
        
        repeat(5) @(posedge clk);
        
        $display("Simulation complete");
        $finish;
    end
endmodule
