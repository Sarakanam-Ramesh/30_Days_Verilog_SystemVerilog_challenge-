`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 05.03.2025 21:47:18
// Design Name: 
// Module Name: queue_memory_buffer_tb
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


// Testbench for Queue Memory Buffer
module tb_queue_memory_buffer();
    parameter DATA_WIDTH = 8;
    parameter MAX_DEPTH = 16;

    // Signals
    logic clk;
    logic rst_n;
    
    // Write interface
    logic wr_en;
    logic [DATA_WIDTH-1:0] wr_data;
    logic wr_full;
    
    // Read interface
    logic rd_en;
    logic [DATA_WIDTH-1:0] rd_data;
    logic rd_empty;

    // Instantiate DUT
    queue_memory_buffer #(
        .DATA_WIDTH(DATA_WIDTH),
        .MAX_DEPTH(MAX_DEPTH)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .wr_en(wr_en),
        .wr_data(wr_data),
        .wr_full(wr_full),
        .rd_en(rd_en),
        .rd_data(rd_data),
        .rd_empty(rd_empty)
    );

    // Clock generation
    always #5 clk = ~clk;

    // Stimulus
    initial begin
        // Initialize
        clk = 0;
        rst_n = 0;
        wr_en = 0;
        rd_en = 0;
        wr_data = 0;

        // Reset sequence
        #10 rst_n = 1;

        // Write some data
        @(posedge clk);
        wr_en = 1;
        
        // Fill the buffer
        for (int i = 0; i < MAX_DEPTH; i++) begin
            wr_data = i + 8'hA0;
            @(posedge clk);
        end

        // Try to write when full
        wr_data = 8'hFF;
        @(posedge clk);
        
        // Read data
        wr_en = 0;
        rd_en = 1;
        
        for (int i = 0; i < MAX_DEPTH; i++) begin
            @(posedge clk);
        end

        // Finish simulation
        #20 $finish;
    end

    // Optional: Waveform dump
    initial begin
        $dumpfile("queue_memory_buffer.vcd");
        $dumpvars(0, tb_queue_memory_buffer);
    end
endmodule
