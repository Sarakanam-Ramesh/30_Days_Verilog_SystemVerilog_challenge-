`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 23.02.2025 11:55:38
// Design Name: 
// Module Name: sv_counter
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


module sv_counter (
    input  logic clk,
    input  logic rst,
    output logic [7:0] count
);

    always_ff @(posedge clk or posedge rst) begin
        if (rst)
            count <= 8'h00;
        else
            count <= count + 1'b1;
    end

endmodule
