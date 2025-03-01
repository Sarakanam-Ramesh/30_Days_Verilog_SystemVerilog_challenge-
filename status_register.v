`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 23.02.2025 11:52:41
// Design Name: 
// Module Name: status_register
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


module status_register (
    input wire clk,
    input wire rst,
    input wire error_in,
    input wire busy_in,
    input wire done_in,
    output reg [2:0] status
);

    // Status bits definition
    // status[0] = error
    // status[1] = busy
    // status[2] = done

    always @(posedge clk or posedge rst) begin
        if (rst) begin
            status <= 3'b000;
        end
        else begin
            status[0] <= error_in;
            status[1] <= busy_in;
            status[2] <= done_in;
        end
    end

endmodule
