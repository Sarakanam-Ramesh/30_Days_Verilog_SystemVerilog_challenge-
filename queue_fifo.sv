`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 27.02.2025 21:43:43
// Design Name: 
// Module Name: queue_fifo
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


module queue_fifo #(
    parameter WIDTH = 8,
    parameter DEPTH = 16  // Changed from MAX_DEPTH to DEPTH for consistency
)(
    input  logic clk,
    input  logic reset,
    input  logic push,
    input  logic pop,
    input  logic [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out,
    output logic empty,
    output logic full,
    output logic [$clog2(DEPTH):0] count  // Ensure positive width
);

    // Use a standard memory array instead of a queue
    logic [WIDTH-1:0] fifo_mem [0:DEPTH-1];
    
    // Pointers for read and write operations
    logic [$clog2(DEPTH):0] write_ptr;  // Extra bit for full detection
    logic [$clog2(DEPTH):0] read_ptr;   // Extra bit for empty detection
    
    // FIFO status signals
    assign empty = (read_ptr == write_ptr);
    assign full = (write_ptr[$clog2(DEPTH)] != read_ptr[$clog2(DEPTH)]) && 
                  (write_ptr[$clog2(DEPTH)-1:0] == read_ptr[$clog2(DEPTH)-1:0]);
    
    // Counter for tracking number of elements
    assign count = write_ptr - read_ptr;
    
    // Write operation
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            write_ptr <= '0;
        end else if (push && !full) begin
            fifo_mem[write_ptr[$clog2(DEPTH)-1:0]] <= data_in;
            write_ptr <= write_ptr + 1'b1;
        end
    end
    
    // Read operation
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            read_ptr <= '0;
            data_out <= '0;
        end else if (pop && !empty) begin
            data_out <= fifo_mem[read_ptr[$clog2(DEPTH)-1:0]];
            read_ptr <= read_ptr + 1'b1;
        end
    end
    
endmodule
