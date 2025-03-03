`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 02.03.2025 12:06:27
// Design Name: 
// Module Name: Clocking_block
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


interface spi_if (
    input logic clk,
    input logic rst_n
);
    // SPI signals
    logic sclk;
    logic cs_n;
    logic mosi;
    logic miso;
    
    // Master modport
    modport master (
        output sclk,
        output cs_n,
        output mosi,
        input  miso
    );
    
    // Slave modport
    modport slave (
        input  sclk,
        input  cs_n,
        input  mosi,
        output miso
    );
    
    // Clocking block for testbench - sampling at posedge clk
    clocking cb_master @(posedge clk);
        output sclk;
        output cs_n;
        output mosi;
        input  miso;
    endclocking
    
    // Clocking block for testbench - sampling at negedge clk with skew
    clocking cb_monitor @(negedge clk);
        default input #1ns output #1ns;  // Add skew for sampling and driving
        input sclk;
        input cs_n;
        input mosi;
        input miso;
    endclocking
    
    // Modport for testbench using clocking block
    modport tb_master (clocking cb_master);
    modport tb_monitor (clocking cb_monitor);
    
endinterface

// SPI Master module
module spi_master (
    input  logic       clk,
    input  logic       rst_n,
    
    // Control interface
    input  logic       start_transaction,
    input  logic [7:0] tx_data,
    output logic [7:0] rx_data,
    output logic       busy,
    output logic       done,
    
    // SPI interface
    spi_if.master      spi
);
    // SPI clock divider (example: system_clk/4)
    logic [1:0] clk_div;
    
    // SPI state machine
    typedef enum logic [1:0] {
        IDLE    = 2'b00,
        START   = 2'b01,
        TRANSFER = 2'b10,
        COMPLETE = 2'b11
    } state_t;
    
    state_t state, next_state;
    
    // Counters and data registers
    logic [2:0] bit_count;
    logic [7:0] tx_shift_reg;
    logic [7:0] rx_shift_reg;
    
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
                if (start_transaction)
                    next_state = START;
            end
            
            START: begin
                next_state = TRANSFER;
            end
            
            TRANSFER: begin
                if (bit_count == 3'b111 && clk_div == 2'b11)
                    next_state = COMPLETE;
            end
            
            COMPLETE: begin
                next_state = IDLE;
            end
        endcase
    end
    
    // SPI clock generation
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            clk_div <= 2'b00;
        end else if (state == TRANSFER) begin
            clk_div <= clk_div + 1'b1;
        end else begin
            clk_div <= 2'b00;
        end
    end
    
    // SPI control signals
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            spi.sclk <= 1'b0;
            spi.cs_n <= 1'b1;
            spi.mosi <= 1'b0;
            rx_data  <= 8'h00;
            busy     <= 1'b0;
            done     <= 1'b0;
            bit_count <= 3'b000;
            tx_shift_reg <= 8'h00;
            rx_shift_reg <= 8'h00;
        end else begin
            case (state)
                IDLE: begin
                    spi.cs_n <= 1'b1;
                    spi.sclk <= 1'b0;
                    busy     <= 1'b0;
                    done     <= 1'b0;
                    
                    if (start_transaction) begin
                        tx_shift_reg <= tx_data;
                        busy <= 1'b1;
                    end
                end
                
                START: begin
                    spi.cs_n   <= 1'b0;
                    bit_count <= 3'b000;
                end
                
                TRANSFER: begin
                    // Generate SPI clock
                    spi.sclk <= clk_div[1];
                    
                    // Set MOSI on falling edge of SPI clock
                    if (clk_div == 2'b01) begin
                        spi.mosi <= tx_shift_reg[7];
                    end
                    
                    // Sample MISO on rising edge of SPI clock
                    if (clk_div == 2'b11) begin
                        rx_shift_reg <= {rx_shift_reg[6:0], spi.miso};
                        tx_shift_reg <= {tx_shift_reg[6:0], 1'b0};
                        bit_count <= bit_count + 1'b1;
                    end
                end
                
                COMPLETE: begin
                    spi.cs_n <= 1'b1;
                    spi.sclk <= 1'b0;
                    rx_data  <= rx_shift_reg;
                    done     <= 1'b1;
                    busy     <= 1'b0;
                end
            endcase
        end
    end
    
endmodule

// SPI Slave module
module spi_slave (
    input  logic      clk,
    input  logic      rst_n,
    
    // Control interface
    input  logic [7:0] tx_data,
    output logic [7:0] rx_data,
    output logic       rx_valid,
    
    // SPI interface
    spi_if.slave       spi
);
    // Shift registers
    logic [7:0] tx_shift_reg;
    logic [7:0] rx_shift_reg;
    
    // Edge detection for SPI clock
    logic sclk_prev;
    logic sclk_posedge;
    logic sclk_negedge;
    
    // Bit counter
    logic [2:0] bit_count;
    
    // Edge detection
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            sclk_prev <= 1'b0;
        end else begin
            sclk_prev <= spi.sclk;
        end
    end
    
    assign sclk_posedge = spi.sclk && !sclk_prev;
    assign sclk_negedge = !spi.sclk && sclk_prev;
    
    // SPI slave logic
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rx_shift_reg <= 8'h00;
            tx_shift_reg <= 8'h00;
            rx_data      <= 8'h00;
            rx_valid     <= 1'b0;
            bit_count    <= 3'b000;
            spi.miso     <= 1'b0;
        end else begin
            // Default values
            rx_valid <= 1'b0;
            
            // Chip select activated
            if (!spi.cs_n) begin
                // Load TX data when CS is first asserted
                if (bit_count == 3'b000 && sclk_prev == 1'b0 && spi.sclk == 1'b0) begin
                    tx_shift_reg <= tx_data;
                    spi.miso     <= tx_data[7];  // Set first bit
                end
                
                // Sample MOSI on rising edge of SPI clock
                if (sclk_posedge) begin
                    rx_shift_reg <= {rx_shift_reg[6:0], spi.mosi};
                    bit_count <= bit_count + 1'b1;
                    
                    // Check if full byte received
                    if (bit_count == 3'b111) begin
                        rx_data  <= {rx_shift_reg[6:0], spi.mosi};
                        rx_valid <= 1'b1;
                        bit_count <= 3'b000;
                    end
                end
                
                // Update MISO on falling edge of SPI clock
                if (sclk_negedge) begin
                    tx_shift_reg <= {tx_shift_reg[6:0], 1'b0};
                    spi.miso     <= tx_shift_reg[6];  // Next bit
                end
            end else begin
                // Reset when CS is deasserted
                bit_count <= 3'b000;
            end
        end
    end
    
endmodule
