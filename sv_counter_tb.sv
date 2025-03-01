`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 23.02.2025 11:56:20
// Design Name: 
// Module Name: sv_counter_tb
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


module sv_counter_tb;
    logic clk;
    logic rst;
    logic [7:0] count;

    // Instantiate the counter
    sv_counter dut (.*);

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end

    // Test stimulus
    initial begin
    
        // Test reset
        rst = 1;
        #10 rst = 0;

        // Let it count for a while
        repeat(260) @(posedge clk);

        $finish;
    end

    // Assertions
    property count_increment;
        @(posedge clk) disable iff (rst)
        count |=> count == ($past(count) + 1);
    endproperty

    assert property (count_increment)
        else $error("Counter did not increment correctly");

endmodule
