`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 26.02.2025 21:51:49
// Design Name: 
// Module Name: enhanced_alu_sv
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


module enhanced_alu_sv (
    input logic [7:0] a, b,
    input logic [2:0] op_code,
    output logic [7:0] result,
    output logic zero_flag
);

    always_comb begin
        // Default values
        result = 8'b0;
        zero_flag = 1'b0;
        
        case (op_code)
            3'b000: result = a + b;     // ADD
            3'b001: result = a - b;     // SUB
            3'b010: result = a & b;     // AND
            3'b011: result = a | b;     // OR
            3'b100: result = a ^ b;     // XOR
            3'b101: result = ~a;        // NOT
            3'b110: begin               // Compare
                if (a < b)
                    result = 8'b00000001;
                else
                    result = 8'b00000000;
            end
            3'b111: result = a << b[2:0]; // Shift left
            default: result = 8'b0;
        endcase
        
        // Set zero flag if result is zero
        if (result == 8'b0)
            zero_flag = 1'b1;
    end

endmodule
