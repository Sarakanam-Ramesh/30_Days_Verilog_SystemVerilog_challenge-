`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 03.03.2025 19:20:27
// Design Name: 
// Module Name: traffic_light_sv
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


module traffic_light_sv (
    input logic clk,
    input logic rst_n,
    output logic red,
    output logic yellow,
    output logic green
);

    // State definition using enumeration
    typedef enum logic [1:0] {
        RED = 2'b00,
        GREEN = 2'b01,
        YELLOW = 2'b10
    } state_t;
    
    // State registers
    state_t current_state, next_state;
    
    // Timing parameters (in clock cycles)
    localparam RED_TIME = 10;
    localparam GREEN_TIME = 8;
    localparam YELLOW_TIME = 3;
    
    // Counter for timing
    logic [3:0] counter;
    
    // State register with reset
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_state <= RED;
            counter <= '0;
        end else begin
            if (counter == 0)
                current_state <= next_state;
                
            // Update counter
            case (current_state)
                RED:    counter <= (counter == RED_TIME-1) ? '0 : counter + 1;
                GREEN:  counter <= (counter == GREEN_TIME-1) ? '0 : counter + 1;
                YELLOW: counter <= (counter == YELLOW_TIME-1) ? '0 : counter + 1;
                default: counter <= '0;
            endcase
        end
    end
    
    // Next state logic
    always_comb begin
        case (current_state)
            RED: 
                next_state = (counter == RED_TIME-1) ? GREEN : RED;
            GREEN: 
                next_state = (counter == GREEN_TIME-1) ? YELLOW : GREEN;
            YELLOW: 
                next_state = (counter == YELLOW_TIME-1) ? RED : YELLOW;
            default: 
                next_state = RED;
        endcase
    end
    
    // Output logic
    always_comb begin
        // Default outputs (all off)
        red = 1'b0;
        yellow = 1'b0;
        green = 1'b0;
        
        case (current_state)
            RED:    red = 1'b1;
            GREEN:  green = 1'b1;
            YELLOW: yellow = 1'b1;
            default: red = 1'b1; // Default to red for safety
        endcase
    end

endmodule