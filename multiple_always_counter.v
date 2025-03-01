`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 25.02.2025 19:22:52
// Design Name: 
// Module Name: multiple_always_counter
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


// RTL: Multiple Always Block Counter
module multiple_always_counter (
    input wire clk,            // System clock
    input wire reset,          // Active high reset
    input wire enable,         // Counter enable
    input wire up_down,        // 1: Count up, 0: Count down
    input wire load,           // Load value from data_in
    input wire [7:0] data_in,  // Input data for loading
    output reg [7:0] count     // Current counter value
);
    // Counter logic - synchronous reset
    always @(posedge clk) begin
        if (reset) begin
            count <= 8'h00;
        end
    end
    
    // Counter logic - load operation
    always @(posedge clk) begin
        if (!reset && load) begin
            count <= data_in;
        end
    end
    
    // Counter logic - counting operation
    always @(posedge clk) begin
        if (!reset && !load && enable) begin
            if (up_down)
                count <= count + 1;  // Count up
            else
                count <= count - 1;  // Count down
        end
    end
    
endmodule


