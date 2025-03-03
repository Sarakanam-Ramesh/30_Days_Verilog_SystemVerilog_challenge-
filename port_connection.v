`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 02.03.2025 11:31:28
// Design Name: 
// Module Name: port_connection
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


// Example 1: Basic Module with explicit port connections
module adder (
    input  wire [7:0] a,
    input  wire [7:0] b,
    output wire [8:0] sum
);
    assign sum = a + b;
endmodule

// Example 2: Module with input/output/inout ports
module gpio_cell (
    input  wire       clk,
    input  wire       rst_n,
    input  wire       direction, // 1: output, 0: input
    input  wire       out_data,
    output reg        in_data,
    inout  wire       pad       // Bidirectional pad
);
    // Tri-state buffer for the pad
    assign pad = (direction) ? out_data : 1'bz;
    
    // Register input from pad
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            in_data <= 1'b0;
        else
            in_data <= pad;
    end
endmodule

// Example 3: Hierarchical module with connections
module port_connection (
    input  wire       clk,
    input  wire       rst_n,
    input  wire [7:0] data_a,
    input  wire [7:0] data_b,
    output wire [8:0] result,
    inout  wire       io_pin
);
    // Internal signals
    wire       gpio_direction;
    wire       gpio_out;
    wire       gpio_in;
    
    // Instantiate adder with named port connections
    adder u_adder (
        .a(data_a),
        .b(data_b),
        .sum(result)
    );
    
    // Instantiate GPIO with positional port connections
    gpio_cell u_gpio (
        clk,
        rst_n,
        gpio_direction,
        gpio_out,
        gpio_in,
        io_pin
    );
    
    // Simple control logic
    assign gpio_direction = result[0];  // Use LSB of result to control direction
    assign gpio_out = result[1];        // Use bit 1 of result for output
    
endmodule
