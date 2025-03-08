`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 03.03.2025 18:56:57
// Design Name: 
// Module Name: traffic_light_controller
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


module traffic_light_controller (
    input wire clk,
    input wire rst_n,
    output reg red,
    output reg yellow,
    output reg green
);

    // State encoding
    parameter S_RED = 2'b00;
    parameter S_GREEN = 2'b01;
    parameter S_YELLOW = 2'b10;
    
    // Timing parameters (in clock cycles)
    parameter RED_TIME = 10;
    parameter GREEN_TIME = 8;
    parameter YELLOW_TIME = 3;
    
    // State registers
    reg [1:0] current_state, next_state;
    
    // Counter for timing
    reg [3:0] counter;
    
    // State register
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_state <= S_RED;
            counter <= 0;
        end else begin
            if (counter == 0)
                current_state <= next_state;
                
            // Update counter
            case (current_state)
                S_RED:    counter <= (counter == RED_TIME-1) ? 0 : counter + 1;
                S_GREEN:  counter <= (counter == GREEN_TIME-1) ? 0 : counter + 1;
                S_YELLOW: counter <= (counter == YELLOW_TIME-1) ? 0 : counter + 1;
                default:  counter <= 0;
            endcase
        end
    end
    
    // Next state logic
    always @(*) begin
        case (current_state)
            S_RED: 
                next_state = (counter == RED_TIME-1) ? S_GREEN : S_RED;
            S_GREEN: 
                next_state = (counter == GREEN_TIME-1) ? S_YELLOW : S_GREEN;
            S_YELLOW: 
                next_state = (counter == YELLOW_TIME-1) ? S_RED : S_YELLOW;
            default: 
                next_state = S_RED;
        endcase
    end
    
    // Output logic
    always @(*) begin
        red = 0; yellow = 0; green = 0;
        
        case (current_state)
            S_RED:    red = 1;
            S_GREEN:  green = 1;
            S_YELLOW: yellow = 1;
            default:  red = 1; // Default to red for safety
        endcase
    end

endmodule
