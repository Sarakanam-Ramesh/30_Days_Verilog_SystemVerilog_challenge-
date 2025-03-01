`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 26.02.2025 21:12:02
// Design Name: 
// Module Name: basic_alu
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


module basic_alu (
    input [7:0] a, b,
    input [1:0] op_code,
    output reg [7:0] result
);

    always @(*) begin
        if (op_code == 2'b00) begin
            // ADD
            result = a + b;
        end else if (op_code == 2'b01) begin
            // SUB
            result = a - b;
        end else if (op_code == 2'b10) begin
            // AND
            result = a & b;
        end else begin
            // OR
            result = a | b;
        end
    end

endmodule
