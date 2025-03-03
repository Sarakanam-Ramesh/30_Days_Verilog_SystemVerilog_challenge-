`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 02.03.2025 11:23:26
// Design Name: 
// Module Name: memory_interface
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


module memory_interface (
    input  wire        clk,
    input  wire        rst_n,
    // Host interface
    input  wire        req,
    input  wire        wr_en,
    input  wire [15:0] addr,
    input  wire [31:0] wdata,
    output reg  [31:0] rdata,
    output reg         ready,
    // Memory interface
    output reg         mem_cs,
    output reg         mem_we,
    output reg  [15:0] mem_addr,
    output reg  [31:0] mem_wdata,
    input  wire [31:0] mem_rdata,
    input  wire        mem_ack
);

    // FSM states
    localparam IDLE  = 2'b00;
    localparam SETUP = 2'b01;
    localparam WAIT  = 2'b10;
    localparam DONE  = 2'b11;
    
    reg [1:0] state, next_state;
    
    // State register
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= IDLE;
        else
            state <= next_state;
    end
    
    // Next state logic
    always @(*) begin
        next_state = state;
        
        case (state)
            IDLE: begin
                if (req)
                    next_state = SETUP;
            end
            
            SETUP: begin
                next_state = WAIT;
            end
            
            WAIT: begin
                if (mem_ack)
                    next_state = DONE;
            end
            
            DONE: begin
                next_state = IDLE;
            end
        endcase
    end
    
    // Output logic
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mem_cs    <= 1'b0;
            mem_we    <= 1'b0;
            mem_addr  <= 16'h0000;
            mem_wdata <= 32'h00000000;
            rdata     <= 32'h00000000;
            ready     <= 1'b0;
        end
        else begin
            case (state)
                IDLE: begin
                    mem_cs <= 1'b0;
                    ready  <= 1'b0;
                end
                
                SETUP: begin
                    mem_cs    <= 1'b1;
                    mem_we    <= wr_en;
                    mem_addr  <= addr;
                    mem_wdata <= wdata;
                end
                
                WAIT: begin
                    if (mem_ack) begin
                        if (!wr_en) 
                            rdata <= mem_rdata;
                    end
                end
                
                DONE: begin
                    mem_cs <= 1'b0;
                    ready  <= 1'b1;
                end
            endcase
        end
    end

endmodule