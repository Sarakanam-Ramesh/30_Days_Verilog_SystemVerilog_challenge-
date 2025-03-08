`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 03.03.2025 19:11:47
// Design Name: 
// Module Name: sequence_detector
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


module sequence_detector (
    input wire clk,
    input wire rst_n,
    input wire data_in,
    output reg detected
);

    // State encoding
    parameter S0 = 2'b00;  // Initial state
    parameter S1 = 2'b01;  // Detected '1'
    parameter S2 = 2'b10;  // Detected '10'
    parameter S3 = 2'b11;  // Detected '101'
    
    // State registers
    reg [1:0] current_state, next_state;
    
    // State register update
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_state <= S0;
        end else begin
            current_state <= next_state;
        end
    end
    
    // Next state logic
    always @(*) begin
        case (current_state)
            S0: next_state = data_in ? S1 : S0;
            S1: next_state = data_in ? S1 : S2;
            S2: next_state = data_in ? S3 : S0;
            S3: next_state = data_in ? S1 : S2;
            default: next_state = S0;
        endcase
    end
    
    // Output logic (Moore machine - output depends only on current state)
    always @(*) begin
        detected = (current_state == S3);
    end

endmodule