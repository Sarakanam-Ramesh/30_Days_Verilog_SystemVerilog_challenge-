`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 28.02.2025 22:13:48
// Design Name: 
// Module Name: automatic_parity_checker
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


module automatic_parity_checker (
    input logic clk,
    input logic rst_n,
    input logic [15:0] data_in,
    input logic data_valid,
    output logic parity_error
);
    // Automatic function that calculates parity for different data sizes
    // The 'automatic' keyword creates a new instance of the function for each call
    function automatic logic check_parity(input logic [15:0] data, input logic [3:0] size);
        logic parity;
        parity = 1'b0; // Initialize to even parity (0)
        
        case (size)
            4'd8: begin
                // Check parity for 8-bit data
                parity = ^data[7:0];
            end
            4'd16: begin
                // Check parity for 16-bit data
                parity = ^data;
            end
            default: begin
                // Default to 4-bit data
                parity = ^data[3:0];
            end
        endcase
        
        return parity;
    endfunction
    
    // Check the parity whenever valid data arrives
    logic expected_parity;
    logic actual_parity;
    logic [3:0] data_size;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            parity_error <= 1'b0;
            data_size <= 4'd8; // Default to 8-bit size
        end else if (data_valid) begin
            // Determine data size based on the MSB of data_in
            data_size <= (data_in[15]) ? 4'd16 : 4'd8;
            
            // Extract expected parity (assume it's in bit position based on data size)
            if (data_in[15])
                expected_parity <= data_in[0]; // For 16-bit, parity is in LSB
            else
                expected_parity <= data_in[8]; // For 8-bit, parity is in bit 8
                
            // Calculate actual parity
            actual_parity <= check_parity(data_in, data_size);
            
            // Compare expected and actual parity
            parity_error <= (expected_parity != actual_parity);
        end
    end
endmodule
