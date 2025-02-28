`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 28.02.2025 22:05:47
// Design Name: 
// Module Name: crc_calculator
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


module crc_calculator (
    input clk,
    input rst_n,
    input data_in,
    input data_valid,
    output reg [7:0] crc_out,
    output reg crc_valid
);
    reg [7:0] crc_reg;
    reg [3:0] bit_counter;
    
    // Function to calculate CRC-8 with polynomial x^8 + x^2 + x + 1 (0x07)
    function [7:0] calculate_crc_bit;
        input data_bit;
        input [7:0] crc_in;
        reg feedback;
        begin
            feedback = data_bit ^ crc_in[7];
            calculate_crc_bit = {crc_in[6:0], 1'b0};
            
            if (feedback) begin
                calculate_crc_bit = calculate_crc_bit ^ 8'h07;
            end
        end
    endfunction
    
    // CRC calculation state machine
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            crc_reg <= 8'h00;
            bit_counter <= 4'h0;
            crc_valid <= 1'b0;
            crc_out <= 8'h00;
        end else if (data_valid) begin
            crc_reg <= calculate_crc_bit(data_in, crc_reg);
            
            // Count 8 bits to form a byte
            if (bit_counter == 4'd7) begin
                bit_counter <= 4'h0;
                crc_valid <= 1'b1;
                crc_out <= calculate_crc_bit(data_in, crc_reg);
            end else begin
                bit_counter <= bit_counter + 1'b1;
                crc_valid <= 1'b0;
            end
        end else begin
            crc_valid <= 1'b0;
        end
    end
endmodule
