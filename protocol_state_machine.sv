`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 03.03.2025 19:25:57
// Design Name: 
// Module Name: protocol_state_machine
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


module protocol_state_machine (
    input logic clk,
    input logic rst_n,
    input logic req,         // Request signal
    input logic [7:0] data_in,
    output logic ack,        // Acknowledge signal
    output logic ready,      // Ready for new transaction
    output logic [7:0] data_out
);

    // State definition using enumeration
    typedef enum logic [2:0] {
        IDLE,
        WAIT_REQ,
        PROCESS,
        SEND_ACK,
        WAIT_DEASSERT
    } state_t;
    
    // State registers
    state_t current_state, next_state;
    
    // Data register
    logic [7:0] data_reg;
    
    // State register with reset
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_state <= IDLE;
            data_reg <= '0;
        end else begin
            current_state <= next_state;
            
            // Store data when in PROCESS state
            if (current_state == PROCESS)
                data_reg <= data_in;
        end
    end
    
    // Next state logic
    always_comb begin
        next_state = current_state; // Default is to stay in current state
        
        case (current_state)
            IDLE: 
                next_state = WAIT_REQ;
                
            WAIT_REQ:
                if (req)
                    next_state = PROCESS;
                    
            PROCESS:
                next_state = SEND_ACK;
                
            SEND_ACK:
                next_state = WAIT_DEASSERT;
                
            WAIT_DEASSERT:
                if (!req)
                    next_state = IDLE;
                    
            default: 
                next_state = IDLE;
        endcase
    end
    
    // Output logic
    always_comb begin
        // Default outputs
        ack = 1'b0;
        ready = 1'b0;
        data_out = data_reg;
        
        case (current_state)
            IDLE:
                ready = 1'b1;
                
            WAIT_REQ:
                ready = 1'b1;
                
            SEND_ACK:
                ack = 1'b1;
                
            WAIT_DEASSERT:
                ack = 1'b1;
                
            default: begin
                ack = 1'b0;
                ready = 1'b0;
            end
        endcase
    end

endmodule
