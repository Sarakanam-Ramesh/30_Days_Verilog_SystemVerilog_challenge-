`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 23.02.2025 11:43:11
// Design Name: 
// Module Name: counter_int
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


module counter_int(
    input wire clk,
    input wire rst,
    output reg [7:0] count
    );
    
    integer counter;
    
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            counter <= 0;
            count <= 8'b0;
        end
        else begin
            if (counter == 255)
                counter <= 0;
            else
                counter <= counter + 1;
            
            count <= counter[7:0];
        end
    end
endmodule
