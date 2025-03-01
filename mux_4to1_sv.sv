`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 26.02.2025 21:35:01
// Design Name: 
// Module Name: mux_4to1_sv
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


module mux_4to1_sv (
    input logic [1:0] sel,
    input logic [3:0] data_in,
    output logic out
);

    always_comb begin
        unique if (sel == 2'b00)
            out = data_in[0];
        else if (sel == 2'b01)
            out = data_in[1];
        else if (sel == 2'b10)
            out = data_in[2];
        else // sel == 2'b11
            out = data_in[3];
    end

endmodule
