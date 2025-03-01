`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 23.02.2025 12:00:05
// Design Name: 
// Module Name: sv_packet
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


module sv_packet (
    input  logic clk,
    input  logic rst,
    input  logic [7:0] data_in,
    input  logic [3:0] dest_in,
    input  logic valid_in,
    output logic [13:0] packet_out
);

    typedef struct packed {
        logic valid;
        logic [3:0] dest;
        logic [7:0] data;
    } packet_t;

    packet_t packet;

    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            packet <= '0;
        end
        else begin
            packet.valid <= valid_in;
            packet.dest  <= dest_in;
            packet.data  <= data_in;
        end
    end

    assign packet_out = packet;

endmodule
