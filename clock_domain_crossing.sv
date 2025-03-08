`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 08.03.2025 16:20:38
// Design Name: 
// Module Name: clock_domain_crossing
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


module clock_domain_crossing (
    input  logic clk_src,
    input  logic clk_dst,
    input  logic rst_n,
    input  logic [7:0] data_src,
    input  logic valid_src,
    output logic ready_src,
    output logic [7:0] data_dst,
    output logic valid_dst,
    input  logic ready_dst
);

    // Source domain signals
    logic toggle_src;
    logic toggle_src_q;
    logic [7:0] data_src_q;
    
    // Destination domain signals
    logic toggle_dst_meta;
    logic toggle_dst;
    logic toggle_dst_q;
    
    // Source domain logic (clk_src)
    always_ff @(posedge clk_src or negedge rst_n) begin
        if (!rst_n) begin
            toggle_src <= 1'b0;
            toggle_src_q <= 1'b0;
            data_src_q <= 8'h00;
            ready_src <= 1'b1;
        end
        else begin
            toggle_src_q <= toggle_src;
            
            if (valid_src && ready_src) begin
                data_src_q <= data_src;
                toggle_src <= ~toggle_src_q;
                ready_src <= 1'b0;
            end
            
            if (toggle_src == toggle_src_q) begin
                ready_src <= 1'b1;
            end
        end
    end
    
    // Destination domain synchronizer (clk_dst)
    always_ff @(posedge clk_dst or negedge rst_n) begin
        if (!rst_n) begin
            toggle_dst_meta <= 1'b0;
            toggle_dst <= 1'b0;
            toggle_dst_q <= 1'b0;
            valid_dst <= 1'b0;
            data_dst <= 8'h00;
        end
        else begin
            // 2-stage synchronizer for toggle bit
            toggle_dst_meta <= toggle_src_q;
            toggle_dst <= toggle_dst_meta;
            toggle_dst_q <= toggle_dst;
            
            // Detect toggle change (new data available)
            if (toggle_dst != toggle_dst_q) begin
                data_dst <= data_src_q;
                valid_dst <= 1'b1;
            end
            else if (ready_dst && valid_dst) begin
                valid_dst <= 1'b0;
            end
        end
    end

endmodule
