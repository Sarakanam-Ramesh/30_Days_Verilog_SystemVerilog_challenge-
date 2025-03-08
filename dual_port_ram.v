`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 05.03.2025 21:24:20
// Design Name: 
// Module Name: dual_port_ram
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


// Dual Port RAM Design
module dual_port_ram #(
    parameter DATA_WIDTH = 8,
    parameter ADDR_WIDTH = 4
)(
    input wire clk,
    // Port A
    input wire we_a,
    input wire [ADDR_WIDTH-1:0] addr_a,
    input wire [DATA_WIDTH-1:0] din_a,
    output reg [DATA_WIDTH-1:0] dout_a,
    
    // Port B
    input wire we_b,
    input wire [ADDR_WIDTH-1:0] addr_b,
    input wire [DATA_WIDTH-1:0] din_b,
    output reg [DATA_WIDTH-1:0] dout_b
);

    // Memory array declaration
    reg [DATA_WIDTH-1:0] memory [(1 << ADDR_WIDTH)-1:0];

    // Port A Read/Write logic
    always @(posedge clk) begin
        if (we_a) begin
            memory[addr_a] <= din_a;
        end
        dout_a <= memory[addr_a];
    end

    // Port B Read/Write logic
    always @(posedge clk) begin
        if (we_b) begin
            memory[addr_b] <= din_b;
        end
        dout_b <= memory[addr_b];
    end
endmodule
