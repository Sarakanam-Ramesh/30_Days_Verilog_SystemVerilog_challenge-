`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 26.02.2025 21:05:47
// Design Name: 
// Module Name: priority_encoder_3bit
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


module priority_encoder_3bit (
    input [2:0] in,
    output reg [1:0] out,
    output reg valid
);

    always @(*) begin
        case (in)
            3'b000: begin
                out = 2'b00;
                valid = 1'b0;
            end
            3'b001, 3'b011, 3'b101, 3'b111: begin
                out = 2'b00;
                valid = 1'b1;
            end
            3'b010, 3'b110: begin
                out = 2'b01;
                valid = 1'b1;
            end
            3'b100: begin
                out = 2'b10;
                valid = 1'b1;
            end
            default: begin
                out = 2'b00;
                valid = 1'b0;
            end
        endcase
    end

endmodule
