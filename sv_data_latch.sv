`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 25.02.2025 19:45:31
// Design Name: 
// Module Name: sv_data_latch
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


// RTL: Latch Implementation using always_latch
module sv_data_latch #(
    parameter int WIDTH = 8  // Default data width
)(
    input  logic             enable,   // Latch enable signal
    input  logic [WIDTH-1:0] data_in,  // Input data
    output logic [WIDTH-1:0] data_out);  // Latched output
    // Transparent latch using always_latch
    always_latch begin
        if (enable) begin
            data_out <= data_in;
        end
        // No else clause creates a latch behavior
    end
endmodule

// 8-bit registered latch with clear signal
module sv_registered_latch (
    input  logic        clk,       // Clock for register stage
    input  logic        reset,     // Active high reset
    input  logic        enable,    // Latch enable
    input  logic        clear,     // Asynchronous clear
    input  logic [7:0]  data_in,   // Input data
    output logic [7:0]  data_out   // Registered latch output
);
    // Internal signals
    logic [7:0] latch_out;
    // Latch stage using always_latch
    always_latch begin
        if (clear)
            latch_out <= 8'h00;
        else if (enable)
            latch_out <= data_in;
        // No else clause creates a latch behavior
    end
    // Register stage using always_ff
    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            data_out <= 8'h00;
        else
            data_out <= latch_out;
    end
endmodule

