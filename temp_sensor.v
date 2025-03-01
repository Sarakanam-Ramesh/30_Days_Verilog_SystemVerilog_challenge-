`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 23.02.2025 11:50:53
// Design Name: 
// Module Name: temp_sensor
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


module temp_sensor (
    input wire clk,
    input wire rst,
    input wire [7:0] sensor_in,
    output reg [7:0] temp_out
);

    real temp_celsius;
    real conversion_factor;

    initial begin
        conversion_factor = 0.5; // Example conversion factor
    end

    always @(posedge clk or posedge rst) begin
        if (rst) begin
            temp_celsius = 0.0;
            temp_out <= 8'b0;
        end
        else begin
            // Convert sensor input to temperature
            temp_celsius = sensor_in * conversion_factor;
            
            // Convert real to fixed-point for output
            temp_out <= temp_celsius;
        end
    end

endmodule
