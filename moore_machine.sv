`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 03.03.2025 19:32:45
// Design Name: 
// Module Name: moore_machine
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


module moore_machine (
    input logic clk,
    input logic rst_n,
    input logic data_in,
    output logic [1:0] data_out
);

    // State definition using enumeration
    typedef enum logic [2:0] {
        S0 = 3'b000,
        S1 = 3'b001,
        S2 = 3'b010,
        S3 = 3'b011,
        S4 = 3'b100
    } state_t;
    
    // State registers
    state_t current_state, next_state;
    
    // State register with reset
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            current_state <= S0;
        else
            current_state <= next_state;
    end
    
    // Next state logic
    always_comb begin
        case (current_state)
            S0: next_state = data_in ? S1 : S0;
            S1: next_state = data_in ? S2 : S0;
            S2: next_state = data_in ? S2 : S3;
            S3: next_state = data_in ? S4 : S0;
            S4: next_state = data_in ? S2 : S0;
            default: next_state = S0;
        endcase
    end
    
    // Output logic (Moore machine - output depends only on current state)
    always_comb begin
        case (current_state)
            S0: data_out = 2'b00;
            S1: data_out = 2'b01;
            S2: data_out = 2'b10;
            S3: data_out = 2'b11;
            S4: data_out = 2'b00;
            default: data_out = 2'b00;
        endcase
    end

endmodule
