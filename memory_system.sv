`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 02.03.2025 11:56:02
// Design Name: 
// Module Name: memory_system
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


interface memory_if #(
    parameter ADDR_WIDTH = 16,
    parameter DATA_WIDTH = 32
)(
    input logic clk,
    input logic rst_n
);
    // Memory interface signals
    logic                    req;
    logic                    wr_en;
    logic [ADDR_WIDTH-1:0]   addr;
    logic [DATA_WIDTH-1:0]   wdata;
    logic [DATA_WIDTH-1:0]   rdata;
    logic                    ack;
    
    // Controller modport (initiator)
    modport controller (
        output req,
        output wr_en,
        output addr,
        output wdata,
        input  rdata,
        input  ack
    );
    
    // Memory modport (target)
    modport memory (
        input  req,
        input  wr_en,
        input  addr,
        input  wdata,
        output rdata,
        output ack
    );
    
    // Monitor modport
    modport monitor (
        input req,
        input wr_en,
        input addr,
        input wdata,
        input rdata,
        input ack
    );
    
endinterface

// Memory controller using the interface
module memory_controller (
    input logic clk,
    input logic rst_n,
    
    // Host signals
    input  logic                    host_req,
    input  logic                    host_wr_en,
    input  logic [15:0]             host_addr,
    input  logic [31:0]             host_wdata,
    output logic [31:0]             host_rdata,
    output logic                    host_ack,
    
    // Memory interface
    memory_if.controller            mem_if
);
    // Simple passthrough in this example
    assign mem_if.req   = host_req;
    assign mem_if.wr_en = host_wr_en;
    assign mem_if.addr  = host_addr;
    assign mem_if.wdata = host_wdata;
    assign host_rdata   = mem_if.rdata;
    assign host_ack     = mem_if.ack;
    
endmodule

// Memory model using the interface
module memory_model (
    input logic clk,
    input logic rst_n,
    memory_if.memory mem_if
);
    // Memory array
    logic [31:0] mem [0:1023];
    
    // Implement memory behavior
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mem_if.rdata <= '0;
            mem_if.ack   <= 1'b0;
            
            // Initialize memory with test pattern
            for (int i = 0; i < 1024; i++) begin
                mem[i] <= i;
            end
        end
        else begin
            // Default values
            mem_if.ack <= 1'b0;
            
            if (mem_if.req) begin
                if (mem_if.wr_en) begin
                    // Write operation
                    if (mem_if.addr[9:0] < 1024) begin
                        mem[mem_if.addr[9:0]] <= mem_if.wdata;
                    end
                end
                else begin
                    // Read operation
                    if (mem_if.addr[9:0] < 1024) begin
                        mem_if.rdata <= mem[mem_if.addr[9:0]];
                    end
                    else begin
                        mem_if.rdata <= '0;
                    end
                end
                
                // Acknowledge after 1 cycle
                mem_if.ack <= 1'b1;
            end
        end
    end
    
endmodule

// Top module connecting controller and memory
module memory_system (
    input logic clk,
    input logic rst_n,
    
    // Host interface
    input  logic        host_req,
    input  logic        host_wr_en,
    input  logic [15:0] host_addr,
    input  logic [31:0] host_wdata,
    output logic [31:0] host_rdata,
    output logic        host_ack
);
    // Instantiate the memory interface
    memory_if #(
        .ADDR_WIDTH(16),
        .DATA_WIDTH(32)
    ) mem_if (
        .clk(clk),
        .rst_n(rst_n)
    );
    
    // Instantiate the memory controller
    memory_controller u_controller (
        .clk(clk),
        .rst_n(rst_n),
        .host_req(host_req),
        .host_wr_en(host_wr_en),
        .host_addr(host_addr),
        .host_wdata(host_wdata),
        .host_rdata(host_rdata),
        .host_ack(host_ack),
        .mem_if(mem_if.controller)
    );
    
    // Instantiate the memory model
    memory_model u_memory (
        .clk(clk),
        .rst_n(rst_n),
        .mem_if(mem_if.memory)
    );
    
endmodule
