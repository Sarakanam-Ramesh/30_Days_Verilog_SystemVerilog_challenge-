`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 02.03.2025 11:18:12
// Design Name: 
// Module Name: simple_bus
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


module simple_bus (
    input  wire       clk,
    input  wire       rst_n,
    // Master interface
    input  wire       m_req,
    input  wire       m_rw,   // 1: read, 0: write
    input  wire [7:0] m_addr,
    input  wire [7:0] m_wdata,
    output reg  [7:0] m_rdata,
    output reg        m_valid,
    // Slave interface
    output reg        s_req,
    output reg        s_rw,   // 1: read, 0: write
    output reg  [7:0] s_addr,
    output reg  [7:0] s_wdata,
    input  wire [7:0] s_rdata,
    input  wire       s_valid
);

    // Bus control logic
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            s_req   <= 1'b0;
            s_rw    <= 1'b0;
            s_addr  <= 8'h0;
            s_wdata <= 8'h0;
            m_rdata <= 8'h0;
            m_valid <= 1'b0;
        end
        else begin
            // Forward master request to slave
            s_req   <= m_req;
            s_rw    <= m_rw;
            s_addr  <= m_addr;
            s_wdata <= m_wdata;
            
            // Forward slave response to master
            m_rdata <= s_rdata;
            m_valid <= s_valid;
        end
    end

endmodule
