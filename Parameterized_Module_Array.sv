`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06.03.2025 18:39:09
// Design Name: 
// Module Name: Parameterized_Module_Array
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


module processing_element #(
    parameter WIDTH = 8,
    parameter ID = 0
)(
    input clk,
    input rst_n,
    input [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out
);
    // Each PE does a different operation based on its ID
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            data_out <= '0;
        else
            case (ID % 4)
                0: data_out <= data_in + 1;        // Increment
                1: data_out <= data_in - 1;        // Decrement
                2: data_out <= data_in << 1;       // Left shift
                3: data_out <= data_in >> 1;       // Right shift
            endcase
    end
endmodule

module processing_array #(
    parameter ARRAY_SIZE = 4,
    parameter DATA_WIDTH = 8
)(
    input clk,
    input rst_n,
    input [DATA_WIDTH-1:0] data_in,
    output logic [ARRAY_SIZE-1:0][DATA_WIDTH-1:0] data_out
);
    // Create an array of processing elements
    generate
        for (genvar i = 0; i < ARRAY_SIZE; i++) begin : pe_instances
            processing_element #(
                .WIDTH(DATA_WIDTH),
                .ID(i)
            ) pe (
                .clk(clk),
                .rst_n(rst_n),
                .data_in(data_in),
                .data_out(data_out[i])
            );
        end
    endgenerate
endmodule
