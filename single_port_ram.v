`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 05.03.2025 21:16:25
// Design Name: 
// Module Name: single_port_ram
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


// Single Port RAM Design
module single_port_ram #(
    parameter DATA_WIDTH = 8,
    parameter ADDR_WIDTH = 4
)(
    input wire clk,
    input wire we,  // Write enable
    input wire [ADDR_WIDTH-1:0] addr,
    input wire [DATA_WIDTH-1:0] din,
    output reg [DATA_WIDTH-1:0] dout
);

    // Memory array declaration
    reg [DATA_WIDTH-1:0] memory [(1 << ADDR_WIDTH)-1:0];

    // Read/Write logic
    always @(posedge clk) begin
        if (we) begin
            // Write operation
            memory[addr] <= din;
        end
        // Read operation
        dout <= memory[addr];
    end
endmodule
