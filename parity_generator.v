`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 28.02.2025 21:55:13
// Design Name: 
// Module Name: parity_generator
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


module parity_generator (
    input clk,
    input rst_n,
    input [7:0] data_in,
    input data_valid,
    output reg even_parity,
    output reg odd_parity
);
    // Task to generate parity bits
    task generate_parity;
        input [7:0] data;
        output even, odd;
        begin
            // Calculate even parity: 1 when odd number of 1's
            even = ^data;
            // Calculate odd parity: 1 when even number of 1's
            odd = ~(^data);
        end
    endtask
    
    // Generate parity bits when new data is valid
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            even_parity <= 1'b0;
            odd_parity <= 1'b0;
        end else if (data_valid) begin
            generate_parity(data_in, even_parity, odd_parity);
        end
    end
endmodule