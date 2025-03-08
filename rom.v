`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 05.03.2025 21:33:50
// Design Name: 
// Module Name: rom
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


// ROM Implementation
module rom #(
    parameter DATA_WIDTH = 8,
    parameter ADDR_WIDTH = 4
)(
    input wire clk,
    input wire [ADDR_WIDTH-1:0] addr,
    output reg [DATA_WIDTH-1:0] dout
);

    // ROM memory array
    reg [DATA_WIDTH-1:0] memory [(1 << ADDR_WIDTH)-1:0];
    integer i;
    // Initialize ROM with predefined values
    initial begin
        // Example: Initializing with a pattern
        memory[0] = 8'h00;
        memory[1] = 8'h11;
        memory[2] = 8'h22;
        memory[3] = 8'h33;
        memory[4] = 8'h44;
        memory[5] = 8'h55;
        memory[6] = 8'h66;
        memory[7] = 8'h77;
        // Fill remaining locations if needed
        for( i = 8; i < (1 << ADDR_WIDTH); i= i+1) begin
            memory[i] = 8'hFF;  // Default fill value
        end
    end

    // Read operation
    always @(posedge clk) begin
        dout <= memory[addr];
    end
endmodule
