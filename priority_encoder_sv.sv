`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 26.02.2025 21:44:44
// Design Name: 
// Module Name: priority_encoder_sv
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


module priority_encoder_sv (
    input logic [2:0] in,
    output logic [1:0] out,
    output logic valid
);

    always_comb begin
        valid = 1'b0;
        out = 2'b00;
        
        priority case (1'b1)
            in[2]: begin
                out = 2'b10;
                valid = 1'b1;
            end
            in[1]: begin
                out = 2'b01;
                valid = 1'b1;
            end
            in[0]: begin
                out = 2'b00;
                valid = 1'b1;
            end
            default: begin
                out = 2'b00;
                valid = 1'b0;
            end
        endcase
    end

endmodule
