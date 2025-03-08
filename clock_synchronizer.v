`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 08.03.2025 16:15:37
// Design Name: 
// Module Name: clock_synchronizer
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


module clock_synchronizer(
    input wire fast_clk,
    input wire slow_clk,
    input wire rst,
    input wire data_in,
    output reg data_out_fast,
    output reg data_out_slow
);

    // Registers for synchronization
    reg data_sync_stage1_fast;
    reg data_sync_stage2_fast;
    reg data_sync_stage1_slow;
    reg data_sync_stage2_slow;
    
    // Synchronize data_in to fast_clk domain (2-stage synchronizer)
    always @(posedge fast_clk or posedge rst) begin
        if (rst) begin
            data_sync_stage1_fast <= 0;
            data_sync_stage2_fast <= 0;
            data_out_fast <= 0;
        end
        else begin
            data_sync_stage1_fast <= data_in;
            data_sync_stage2_fast <= data_sync_stage1_fast;
            data_out_fast <= data_sync_stage2_fast;
        end
    end
    
    // Synchronize data_in to slow_clk domain (2-stage synchronizer)
    always @(posedge slow_clk or posedge rst) begin
        if (rst) begin
            data_sync_stage1_slow <= 0;
            data_sync_stage2_slow <= 0;
            data_out_slow <= 0;
        end
        else begin
            data_sync_stage1_slow <= data_in;
            data_sync_stage2_slow <= data_sync_stage1_slow;
            data_out_slow <= data_sync_stage2_slow;
        end
    end

endmodule
