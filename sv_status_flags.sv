`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 23.02.2025 11:57:53
// Design Name: 
// Module Name: sv_status_flags
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


module sv_status_flags (
    input  logic clk,
    input  logic rst,
    input  logic [1:0] state_in,
    output logic [1:0] state_out
);

    typedef enum logic [1:0] {
        IDLE    = 2'b00,
        BUSY    = 2'b01,
        DONE    = 2'b10,
        ERROR   = 2'b11
    } state_t;

    state_t current_state;

    always_ff @(posedge clk or posedge rst) begin
        if (rst)
            current_state <= IDLE;
        else
            current_state <= state_t'(state_in);
    end

    assign state_out = current_state;

endmodule
