`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 27.02.2025 21:11:58
// Design Name: 
// Module Name: fifo_buffer
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


module fifo_buffer #(
    parameter WIDTH = 8,
    parameter DEPTH = 16
)(
    input wire clk,
    input wire reset,
    input wire write_en,
    input wire read_en,
    input wire [WIDTH-1:0] data_in,
    output reg [WIDTH-1:0] data_out,
    output wire empty,
    output wire full
);

    // FIFO memory
    reg [WIDTH-1:0] fifo_mem [0:DEPTH-1];
    
    // Pointers and counter
    reg [$clog2(DEPTH):0] write_ptr; // Extra bit for full/empty detection
    reg [$clog2(DEPTH):0] read_ptr;  // Extra bit for full/empty detection
    
    // Full and empty flags
    assign empty = (write_ptr == read_ptr);
    assign full = (write_ptr[$clog2(DEPTH)] != read_ptr[$clog2(DEPTH)]) && 
                  (write_ptr[$clog2(DEPTH)-1:0] == read_ptr[$clog2(DEPTH)-1:0]);
    
    // Write logic
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            write_ptr <= 0;
        end else if (write_en && !full) begin
            fifo_mem[write_ptr[$clog2(DEPTH)-1:0]] <= data_in;
            write_ptr <= write_ptr + 1;
        end
    end
    
    // Read logic
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            read_ptr <= 0;
            data_out <= 0;
        end else if (read_en && !empty) begin
            data_out <= fifo_mem[read_ptr[$clog2(DEPTH)-1:0]];
            read_ptr <= read_ptr + 1;
        end
    end

endmodule