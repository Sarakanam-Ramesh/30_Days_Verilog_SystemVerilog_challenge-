`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 25.02.2025 19:41:00
// Design Name: 
// Module Name: sv_alu
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


// RTL: Combinational Logic using always_comb
module sv_alu (
    input  logic [7:0] a,           // First operand
    input  logic [7:0] b,           // Second operand
    input  logic [2:0] operation,   // Operation selection
    output logic [7:0] result,      // Result of operation
    output logic       zero_flag,   // Set if result is zero
    output logic       carry_flag   // Carry out from operation
);

    // Internal 9-bit result to capture carry
    logic [8:0] internal_result;
    
    // ALU operation using always_comb for combinational logic
    always_comb begin
        // Default values
        internal_result = 9'h000;
        
        // Perform operation based on selection
        case (operation)
            3'b000: internal_result = {1'b0, a};                // Pass A
            3'b001: internal_result = {1'b0, b};                // Pass B
            3'b010: internal_result = {1'b0, a} + {1'b0, b};    // A + B
            3'b011: internal_result = {1'b0, a} - {1'b0, b};    // A - B
            3'b100: internal_result = {1'b0, a & b};            // A AND B
            3'b101: internal_result = {1'b0, a | b};            // A OR B
            3'b110: internal_result = {1'b0, a ^ b};            // A XOR B
            3'b111: internal_result = {1'b0, ~a};               // NOT A
        endcase
        
        // Set result and flags
        result = internal_result[7:0];
        carry_flag = internal_result[8];
        zero_flag = (result == 8'h00);
    end
    
endmodule

