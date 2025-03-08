`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 08.03.2025 16:27:20
// Design Name: 
// Module Name: metastability_handler
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


module metastability_handler #(
    parameter WIDTH = 8,
    parameter STAGES = 3  // Number of synchronization stages
) (
    input  logic clk,
    input  logic rst_n,
    input  logic [WIDTH-1:0] async_data,
    input  logic async_valid,
    output logic [WIDTH-1:0] sync_data,
    output logic sync_valid
);

    // Synchronization registers for control signal (valid)
    logic [STAGES:0] valid_sync;  // One extra for the input capture
    
    // Synchronization registers for data bus
    logic [WIDTH-1:0] data_capture;
    logic [STAGES:0][WIDTH-1:0] data_sync;
    
    // Input capture (sample and hold on async_valid edge)
    // Changed to use synchronous sampling instead of async edge detection
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            valid_sync[0] <= 1'b0;
            data_sync[0] <= '0;
        end
        else begin
            valid_sync[0] <= async_valid;
            // Only capture new data when valid is asserted
            if (async_valid)
                data_sync[0] <= async_data;
        end
    end
    
    // Multi-stage synchronizer (for both valid and data)
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 1; i <= STAGES; i++) begin
                valid_sync[i] <= '0;
                data_sync[i] <= '0;
            end
        end
        else begin
            // Shift through synchronizer stages
            for (int i = 1; i <= STAGES; i++) begin
                valid_sync[i] <= valid_sync[i-1];
                // Only pass data through when valid
                if (valid_sync[i-1])
                    data_sync[i] <= data_sync[i-1];
            end
        end
    end
    
    // Output synchronized signals
    assign sync_valid = valid_sync[STAGES];
    assign sync_data = data_sync[STAGES];

endmodule