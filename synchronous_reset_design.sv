`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 08.03.2025 16:31:27
// Design Name: 
// Module Name: synchronous_reset_design
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


module synchronous_reset_design #(
    parameter WIDTH = 16
) (
    input  logic clk,
    input  logic async_rst_n,   // Asynchronous reset (active low)
    input  logic sync_rst,      // Synchronous reset (active high)
    input  logic [WIDTH-1:0] data_in,
    input  logic valid_in,
    output logic [WIDTH-1:0] data_out,
    output logic valid_out
);

    // Synchronize the asynchronous reset
    logic sync_rst_n_meta;
    logic sync_rst_n;
    
    // Reset synchronizer (2 stages)
    always_ff @(posedge clk or negedge async_rst_n) begin
        if (!async_rst_n) begin
            sync_rst_n_meta <= 1'b0;
            sync_rst_n <= 1'b0;
        end
        else begin
            sync_rst_n_meta <= 1'b1;
            sync_rst_n <= sync_rst_n_meta;
        end
    end
    
    // Combined reset signal (either async reset synchronized, or explicit sync reset)
    logic reset_active;
    assign reset_active = !sync_rst_n || sync_rst;
    
    // Example processing pipeline
    logic [WIDTH-1:0] data_stage1, data_stage2;
    logic valid_stage1, valid_stage2;
    
    // Stage 1: Input registration with synchronous reset
    always_ff @(posedge clk) begin
        if (reset_active) begin
            data_stage1 <= '0;
            valid_stage1 <= 1'b0;
        end
        else begin
            data_stage1 <= data_in;
            valid_stage1 <= valid_in;
        end
    end
    
    // Stage 2: Processing with synchronous reset
    always_ff @(posedge clk) begin
        if (reset_active) begin
            data_stage2 <= '0;
            valid_stage2 <= 1'b0;
        end
        else begin
            // Example processing: add 1 to data
            data_stage2 <= data_stage1 + 1'b1;
            valid_stage2 <= valid_stage1;
        end
    end
    
    // Output stage with synchronous reset
    always_ff @(posedge clk) begin
        if (reset_active) begin
            data_out <= '0;
            valid_out <= 1'b0;
        end
        else begin
            data_out <= data_stage2;
            valid_out <= valid_stage2;
        end
    end

endmodule