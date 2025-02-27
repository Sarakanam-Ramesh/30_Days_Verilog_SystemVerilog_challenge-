`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 27.02.2025 20:59:13
// Design Name: 
// Module Name: shift_register
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


module shift_register #(
    parameter WIDTH = 8
)(
    input wire clk,
    input wire reset,
    input wire shift_en,
    input wire direction, // 0 for left shift, 1 for right shift
    input wire data_in,
    output wire [WIDTH-1:0] data_out
);

    reg [WIDTH-1:0] shift_reg;
    
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            shift_reg <= {WIDTH{1'b0}}; // Reset to all zeros
        end else if (shift_en) begin
            if (direction == 0) begin
                // Left shift (shift in from right)
                shift_reg <= {shift_reg[WIDTH-2:0], data_in};
            end else begin
                // Right shift (shift in from left)
                shift_reg <= {data_in, shift_reg[WIDTH-1:1]};
            end
        end
    end
    
    assign data_out = shift_reg;
    
endmodule
