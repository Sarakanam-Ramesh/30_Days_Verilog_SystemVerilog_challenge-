`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 25.02.2025 18:43:14
// Design Name: 
// Module Name: clock_divider
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


// RTL: Clock Divider using Always Block
module clock_divider #(
    parameter DIVIDE_BY = 2  // Default divider value
)(
    input wire clk_in,       // Input clock
    input wire reset,        // Active high reset
    output reg clk_out       // Divided output clock
);

    // Counter to track clock cycles
    reg [$clog2(DIVIDE_BY)-1:0] counter;
    
    // Clock division logic
    always @(posedge clk_in or posedge reset) begin
        if (reset) begin
            counter <= 0;
            clk_out <= 0;
        end else begin
            if (counter == DIVIDE_BY/2 - 1) begin
                clk_out <= ~clk_out;
                counter <= 0;
            end else begin
                counter <= counter + 1;
            end
        end
    end
endmodule

