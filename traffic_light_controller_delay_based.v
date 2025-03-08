`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 08.03.2025 15:41:16
// Design Name: 
// Module Name: traffic_light_controller_delay_based
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


module traffic_light_controller_delay_based(
    input wire clk,
    input wire rst,
    output reg red,
    output reg yellow,
    output reg green
);

    // Traffic light states
    parameter S_RED = 2'b00;
    parameter S_YELLOW = 2'b01;
    parameter S_GREEN = 2'b10;
    
    reg [1:0] state, next_state;
    
    // Timing parameters (in clock cycles)
    parameter RED_TIME = 30;
    parameter YELLOW_TIME = 5;
    parameter GREEN_TIME = 20;
    
    // Counter for timing
    reg [5:0] counter;
    
    // State and counter update
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            state <= S_RED;
            counter <= 0;
        end
        else begin
            if (counter == 0) begin
                state <= next_state;
                case (next_state)
                    S_RED: counter <= RED_TIME - 1;
                    S_YELLOW: counter <= YELLOW_TIME - 1;
                    S_GREEN: counter <= GREEN_TIME - 1;
                    default: counter <= RED_TIME - 1;
                endcase
            end
            else begin
                counter <= counter - 1;
            end
        end
    end
    
    // Next state logic
    always @(*) begin
        case(state)
            S_RED: begin
                next_state = (counter == 0) ? S_GREEN : S_RED;
            end
            
            S_YELLOW: begin
                next_state = (counter == 0) ? S_RED : S_YELLOW;
            end
            
            S_GREEN: begin
                next_state = (counter == 0) ? S_YELLOW : S_GREEN;
            end
            
            default: begin
                next_state = S_RED;
            end
        endcase
    end
    
    // Output logic
    always @(*) begin
        case(state)
            S_RED: begin
                red = 1'b1;
                yellow = 1'b0;
                green = 1'b0;
            end
            
            S_YELLOW: begin
                red = 1'b0;
                yellow = 1'b1;
                green = 1'b0;
            end
            
            S_GREEN: begin
                red = 1'b0;
                yellow = 1'b0;
                green = 1'b1;
            end
            
            default: begin
                red = 1'b1;
                yellow = 1'b0;
                green = 1'b0;
            end
        endcase
    end

endmodule