`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 25.02.2025 18:55:00
// Design Name: 
// Module Name: edge_detector
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


// RTL: Edge Detector using Initial and Always
module edge_detector (
    input wire clk,            // System clock
    input wire reset,          // Active high reset
    input wire signal_in,      // Input signal to detect edges
    output wire rising_edge,   // Rising edge detected
    output wire falling_edge   // Falling edge detected
);
    // Internal signal to store previous value
    reg signal_delayed;
    
    // Initialize registers
    initial begin
        signal_delayed = 1'b0;
    end
    
    // Register the input signal
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            signal_delayed <= 1'b0;
        end else begin
            signal_delayed <= signal_in;
        end
    end
    
    // Edge detection
    assign rising_edge = signal_in & ~signal_delayed;
    assign falling_edge = ~signal_in & signal_delayed;
    
endmodule

