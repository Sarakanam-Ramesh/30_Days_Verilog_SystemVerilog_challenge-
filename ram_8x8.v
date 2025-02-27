`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 27.02.2025 20:45:24
// Design Name: 
// Module Name: ram_8x8
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


module ram_8x8 (
    input wire clk,
    input wire reset,
    input wire write_en,
    input wire [2:0] addr,
    input wire [7:0] data_in,
    output reg [7:0] data_out
);

    // 8x8 RAM (8 addresses, 8 bits per address)
    reg [7:0] mem [0:7];
    integer i;

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            // Reset all memory locations to 0
            for (i = 0; i < 8; i = i + 1) begin
                mem[i] <= 8'h00;
            end
            data_out <= 8'h00;
        end else begin
            // Read operation (always performed)
            data_out <= mem[addr];
            
            // Write operation (when write_en is high)
            if (write_en) begin
                mem[addr] <= data_in;
            end
        end
    end
endmodule