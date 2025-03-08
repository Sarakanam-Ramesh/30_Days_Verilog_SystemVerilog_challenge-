`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 08.03.2025 15:47:31
// Design Name: 
// Module Name: event_scheduler
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


module event_scheduler(
    input wire clk,
    input wire rst,
    input wire event_a,
    input wire event_b,
    output reg task_1_active,
    output reg task_2_active,
    output reg task_3_active
);

    // Edge detection registers
    reg event_a_prev, event_b_prev;
    
    // Task timers
    reg [3:0] task_1_timer;
    reg [3:0] task_2_timer;
    reg [3:0] task_3_timer;
    
    // Task timer constants
    parameter TASK_1_DURATION = 10;
    parameter TASK_2_DURATION = 15;
    parameter TASK_3_DURATION = 5;
    
    // Edge detection
    wire event_a_posedge = event_a && !event_a_prev;
    wire event_b_negedge = !event_b && event_b_prev;
    
    // Update edge detection registers
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            event_a_prev <= 0;
            event_b_prev <= 0;
        end
        else begin
            event_a_prev <= event_a;
            event_b_prev <= event_b;
        end
    end
    
    // Task 1 timer control
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            task_1_timer <= 0;
            task_1_active <= 0;
        end
        else begin
            if (event_a_posedge && task_1_timer == 0) begin
                task_1_timer <= TASK_1_DURATION;
                task_1_active <= 1;
            end
            else if (task_1_timer > 0) begin
                task_1_timer <= task_1_timer - 1;
                if (task_1_timer == 1) begin
                    task_1_active <= 0;
                end
            end
        end
    end
    
    // Task 2 timer control
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            task_2_timer <= 0;
            task_2_active <= 0;
        end
        else begin
            if (event_b_negedge && task_2_timer == 0) begin
                task_2_timer <= TASK_2_DURATION;
                task_2_active <= 1;
            end
            else if (task_2_timer > 0) begin
                task_2_timer <= task_2_timer - 1;
                if (task_2_timer == 1) begin
                    task_2_active <= 0;
                end
            end
        end
    end
    
    // Task 3 timer control
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            task_3_timer <= 0;
            task_3_active <= 0;
        end
        else begin
            if (event_a && event_b && task_3_timer == 0) begin
                task_3_timer <= TASK_3_DURATION;
                task_3_active <= 1;
            end
            else if (task_3_timer > 0) begin
                task_3_timer <= task_3_timer - 1;
                if (task_3_timer == 1) begin
                    task_3_active <= 0;
                end
            end
        end
    end

endmodule
