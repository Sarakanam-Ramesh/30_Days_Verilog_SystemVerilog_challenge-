`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06.03.2025 18:27:19
// Design Name: 
// Module Name: configurable_register
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


module configurable_register #(
    parameter WIDTH = 32
)(
    input clk,
    input rst_n,
    input en,
    input [WIDTH-1:0] d,
    output reg [WIDTH-1:0] q
);
    
    genvar i;
    generate
        for (i = 0; i < WIDTH; i = i + 1) begin : reg_bit
            always @(posedge clk or negedge rst_n) begin
                if (!rst_n)
                    q[i] <= 1'b0;
                else if (en)
                    q[i] <= d[i];
            end
        end
    endgenerate
endmodule
