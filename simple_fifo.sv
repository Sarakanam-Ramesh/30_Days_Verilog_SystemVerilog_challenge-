`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06.03.2025 18:46:26
// Design Name: 
// Module Name: simple_fifo
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


module simple_fifo #(
    parameter DATA_WIDTH = 8,
    parameter DEPTH = 16,
    parameter USE_ALMOST_FLAGS = 1,
    parameter ALMOST_FULL_THRESHOLD = DEPTH - 2,
    parameter ALMOST_EMPTY_THRESHOLD = 2
)(
    input clk,
    input rst_n,
    input push,
    input pop,
    input [DATA_WIDTH-1:0] data_in,
    output logic [DATA_WIDTH-1:0] data_out,
    output logic full,
    output logic empty,
    output logic almost_full,
    output logic almost_empty
);
    // FIFO storage
    logic [DATA_WIDTH-1:0] mem [DEPTH-1:0];
    logic [$clog2(DEPTH)-1:0] wr_ptr, rd_ptr;
    logic [$clog2(DEPTH):0] count;
    
    // Write pointer logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            wr_ptr <= '0;
        else if (push && !full)
            wr_ptr <= (wr_ptr == DEPTH-1) ? '0 : wr_ptr + 1'b1;
    end
    
    // Read pointer logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            rd_ptr <= '0;
        else if (pop && !empty)
            rd_ptr <= (rd_ptr == DEPTH-1) ? '0 : rd_ptr + 1'b1;
    end
    
    // Count logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            count <= '0;
        else if (push && !pop && !full)
            count <= count + 1'b1;
        else if (pop && !push && !empty)
            count <= count - 1'b1;
    end
    
    // Memory write
    always_ff @(posedge clk) begin
        if (push && !full)
            mem[wr_ptr] <= data_in;
    end
    
    // Output assignment
    assign data_out = mem[rd_ptr];
    assign full = (count == DEPTH);
    assign empty = (count == 0);
    
    // Generate conditional flags
    generate
        if (USE_ALMOST_FLAGS) begin : gen_almost_flags
            assign almost_full = (count >= ALMOST_FULL_THRESHOLD);
            assign almost_empty = (count <= ALMOST_EMPTY_THRESHOLD);
        end else begin : no_almost_flags
            assign almost_full = 1'b0;
            assign almost_empty = 1'b0;
        end
    endgenerate
endmodule