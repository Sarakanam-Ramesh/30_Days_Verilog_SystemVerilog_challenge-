`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 02.03.2025 11:39:21
// Design Name: 
// Module Name: APB_interface
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


interface apb_if (input logic pclk, input logic preset_n);
    // APB Signals
    logic        psel;
    logic        penable;
    logic [31:0] paddr;
    logic        pwrite;
    logic [31:0] pwdata;
    logic [31:0] prdata;
    logic        pready;
    logic        pslverr;
    
    // Master modport
    modport master (
        output psel,
        output penable,
        output paddr,
        output pwrite,
        output pwdata,
        input  prdata,
        input  pready,
        input  pslverr
    );
    
    // Slave modport
    modport slave (
        input  psel,
        input  penable,
        input  paddr,
        input  pwrite,
        input  pwdata,
        output prdata,
        output pready,
        output pslverr
    );
    
    // Monitor modport
    modport monitor (
        input psel,
        input penable,
        input paddr,
        input pwrite,
        input pwdata,
        input prdata,
        input pready,
        input pslverr
    );
    
endinterface

// Example APB Master
module apb_master (
    input  logic        clk,
    input  logic        rst_n,
    input  logic        req,
    input  logic        write,
    input  logic [31:0] addr,
    input  logic [31:0] wdata,
    output logic [31:0] rdata,
    output logic        ready,
    apb_if.master       apb
);
    // State machine states
    typedef enum logic [1:0] {
        IDLE    = 2'b00,
        SETUP   = 2'b01,
        ACCESS  = 2'b10,
        DONE    = 2'b11
    } state_t;
    
    state_t state, next_state;
    
    // State register
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= IDLE;
        else
            state <= next_state;
    end
    
    // Next state logic
    always_comb begin
        next_state = state;
        
        case (state)
            IDLE: begin
                if (req)
                    next_state = SETUP;
            end
            
            SETUP: begin
                next_state = ACCESS;
            end
            
            ACCESS: begin
                if (apb.pready)
                    next_state = DONE;
            end
            
            DONE: begin
                next_state = IDLE;
            end
        endcase
    end
    
    // APB control signals
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            apb.psel    <= 1'b0;
            apb.penable <= 1'b0;
            apb.paddr   <= '0;
            apb.pwrite  <= 1'b0;
            apb.pwdata  <= '0;
            rdata       <= '0;
            ready       <= 1'b0;
        end
        else begin
            case (state)
                IDLE: begin
                    apb.psel    <= 1'b0;
                    apb.penable <= 1'b0;
                    ready       <= 1'b0;
                end
                
                SETUP: begin
                    apb.psel    <= 1'b1;
                    apb.penable <= 1'b0;
                    apb.paddr   <= addr;
                    apb.pwrite  <= write;
                    apb.pwdata  <= wdata;
                end
                
                ACCESS: begin
                    apb.penable <= 1'b1;
                    
                    if (apb.pready) begin
                        if (!apb.pwrite) begin
                            rdata <= apb.prdata;
                        end
                    end
                end
                
                DONE: begin
                    apb.psel    <= 1'b0;
                    apb.penable <= 1'b0;
                    ready       <= 1'b1;
                end
            endcase
        end
    end
    
endmodule

// Example APB Slave
module apb_slave (
    apb_if.slave apb,
    input  logic clk,
    input  logic rst_n
);
    // Simple register bank
    logic [31:0] regs [0:15];
    
    // APB response
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            apb.prdata  <= '0;
            apb.pready  <= 1'b0;
            apb.pslverr <= 1'b0;
            
            // Initialize registers
            for (int i = 0; i < 16; i++) begin
                regs[i] <= i;
            end
        end
        else begin
            // Default values
            apb.pready  <= 1'b1;  // Always ready in this simple example
            apb.pslverr <= 1'b0;  // No errors
            
            if (apb.psel && apb.penable) begin  // APB transfer
                if (apb.pwrite) begin  // Write
                    if (apb.paddr[5:2] < 16) begin
                        regs[apb.paddr[5:2]] <= apb.pwdata;
                    end else begin
                        apb.pslverr <= 1'b1;  // Address out of range
                    end
                end else begin  // Read
                    if (apb.paddr[5:2] < 16) begin
                        apb.prdata <= regs[apb.paddr[5:2]];
                    end else begin
                        apb.prdata <= '0;
                        apb.pslverr <= 1'b1;  // Address out of range
                    end
                end
            end
        end
    end
    
endmodule
