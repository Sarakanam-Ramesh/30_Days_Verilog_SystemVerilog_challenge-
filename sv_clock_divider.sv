`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 25.02.2025 19:35:57
// Design Name: 
// Module Name: sv_clock_divider
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


// RTL: Clock Divider using always_ff
module sv_clock_divider #(
    parameter int DIVIDE_BY = 2  // Default divider value
)(
    input  logic clk_in,         // Input clock
    input  logic reset,          // Active high reset
    output logic clk_out         // Divided output clock
);

    // Counter to track clock cycles
    logic [$clog2(DIVIDE_BY)-1:0] counter;
    
    // Clock division logic using always_ff for sequential logic
    always_ff @(posedge clk_in or posedge reset) begin
        if (reset) begin
            counter <= '0;
            clk_out <= 1'b0;
        end else begin
            if (counter == DIVIDE_BY/2 - 1) begin
                clk_out <= ~clk_out;
                counter <= '0;
            end else begin
                counter <= counter + 1'b1;
            end
        end
    end
endmodule


