`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 28.02.2025 22:31:05
// Design Name: 
// Module Name: return_array_function
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


module return_array_function (
    input logic clk,
    input logic rst_n,
    input logic [7:0] data_in,
    input logic data_valid,
    input logic [1:0] op_select,
    output logic [7:0] result_array [0:3],
    output logic result_valid
);
    // Function to process data and fill the passed array
    function automatic void process_array(input logic [7:0] data, input logic [1:0] operation, 
                                         output logic [7:0] result[0:3]);
        case (operation)
            2'b00: begin // Increment by 1, 2, 3, 4
                result[0] = data + 8'd1;
                result[1] = data + 8'd2;
                result[2] = data + 8'd3;
                result[3] = data + 8'd4;
            end
            
            2'b01: begin // Left shift by 1, 2, 3, 4
                result[0] = data << 1;
                result[1] = data << 2;
                result[2] = data << 3;
                result[3] = data << 4;
            end
            
            2'b10: begin // Bit-wise NOT, AND with 0xF0, OR with 0x0F, XOR with 0xFF
                result[0] = ~data;
                result[1] = data & 8'hF0;
                result[2] = data | 8'h0F;
                result[3] = data ^ 8'hFF;
            end
            
            2'b11: begin // Various operations
                result[0] = data;
                result[1] = data * 2;
                result[2] = data / 2;
                result[3] = data % 10;
            end
        endcase
    endfunction
    
    // Temporary array for function results
    logic [7:0] temp_array[0:3];
    
    // Process data when valid
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < 4; i++) begin
                result_array[i] <= 8'h00;
            end
            result_valid <= 1'b0;
        end else if (data_valid) begin
            process_array(data_in, op_select, temp_array);
            result_array <= temp_array;
            result_valid <= 1'b1;
        end else begin
            result_valid <= 1'b0;
        end
    end
endmodule
