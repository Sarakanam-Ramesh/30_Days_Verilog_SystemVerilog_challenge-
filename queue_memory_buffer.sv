`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 05.03.2025 21:47:18
// Design Name: 
// Module Name: queue_memory_buffer_tb
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


// SystemVerilog Queue-based Memory Buffer
module queue_memory_buffer #(
    parameter DATA_WIDTH = 8,
    parameter MAX_DEPTH = 16
)(
    input wire clk,
    input wire rst_n,
    
    // Write interface
    input wire wr_en,
    input wire [DATA_WIDTH-1:0] wr_data,
    output logic wr_full,
    
    // Read interface
    input wire rd_en,
    output logic [DATA_WIDTH-1:0] rd_data,
    output logic rd_empty
);

    // Queue declaration
    logic [DATA_WIDTH-1:0] buffer_queue[$];

    // Write and read logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Reset
            buffer_queue = {}; // Clear the queue
            wr_full = 0;
            rd_empty = 1;
        end else begin
            // Write logic
            if (wr_en && !wr_full) begin
                if (buffer_queue.size() < MAX_DEPTH) begin
                    buffer_queue.push_back(wr_data);
                end
                
                // Update full flag
                wr_full = (buffer_queue.size() >= MAX_DEPTH);
            end

            // Read logic
            if (rd_en && !rd_empty) begin
                rd_data = buffer_queue.pop_front();
                // Update empty flag
                rd_empty = (buffer_queue.size() == 0);
            end

            // Additional status updates
            rd_empty = (buffer_queue.size() == 0);
            wr_full = (buffer_queue.size() >= MAX_DEPTH);
        end
    end
endmodule

