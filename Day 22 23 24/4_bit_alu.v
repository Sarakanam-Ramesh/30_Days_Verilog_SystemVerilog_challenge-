`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 14.03.2025 23:31:05
// Design Name: 
// Module Name: 4_bit_alu
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


module alu_4bit (
    input wire clk,
    input wire rst_n,
    input wire [3:0] a,
    input wire [3:0] b,
    input wire [2:0] op_code,
    output reg [4:0] result,
    output reg zero_flag
);

    // Operation codes
    localparam ADD = 3'b000;
    localparam SUB = 3'b001;
    localparam AND = 3'b010;
    localparam OR  = 3'b011;
    localparam XOR = 3'b100;
    localparam SHL = 3'b101;
    localparam SHR = 3'b110;
    
    // ALU operation logic
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            result <= 5'b0;
            zero_flag <= 1'b0;
        end else begin
            case (op_code)
                ADD: result <= a + b;
                SUB: result <= a - b;
                AND: result <= a & b;
                OR:  result <= a | b;
                XOR: result <= a ^ b;
                SHL: result <= a << 1;
                SHR: result <= a >> 1;
                default: result <= 5'b0;
            endcase
            
            // Update zero flag
            zero_flag <= (result == 5'b0) ? 1'b1 : 1'b0;
        end
    end

endmodule
