`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06.03.2025 18:46:45
// Design Name: 
// Module Name: simple_fifo_tb
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


module simple_fifo_tb;
    parameter DATA_WIDTH = 8;
    parameter DEPTH = 16;
    parameter TEST_WITH_FLAGS = 1; // Change to 0 to test without almost flags
    
    logic clk, rst_n;
    logic push, pop;
    logic [DATA_WIDTH-1:0] data_in;
    logic [DATA_WIDTH-1:0] data_out;
    logic full, empty;
    logic almost_full, almost_empty;
    
    // Instantiate the DUT
    simple_fifo #(
        .DATA_WIDTH(DATA_WIDTH),
        .DEPTH(DEPTH),
        .USE_ALMOST_FLAGS(TEST_WITH_FLAGS),
        .ALMOST_FULL_THRESHOLD(DEPTH - 2),
        .ALMOST_EMPTY_THRESHOLD(2)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .push(push),
        .pop(pop),
        .data_in(data_in),
        .data_out(data_out),
        .full(full),
        .empty(empty),
        .almost_full(almost_full),
        .almost_empty(almost_empty)
    );
    
    // Clock generation
    always #5 clk = ~clk;
    
    // Display status
    always @(posedge clk) begin
        if (TEST_WITH_FLAGS)
            $display("Time=%0t: push=%b, pop=%b, data_in=%h, data_out=%h, full=%b, empty=%b, almost_full=%b, almost_empty=%b", 
                     $time, push, pop, data_in, data_out, full, empty, almost_full, almost_empty);
        else
            $display("Time=%0t: push=%b, pop=%b, data_in=%h, data_out=%h, full=%b, empty=%b", 
                     $time, push, pop, data_in, data_out, full, empty);
    end
    
    // Test vectors
    initial begin
        // Initialize
        clk = 0; rst_n = 0; push = 0; pop = 0; data_in = 0;
        
        // Release reset
        #15 rst_n = 1;
        
        // Fill the FIFO
        for (int i = 0; i < DEPTH; i++) begin
            push = 1; pop = 0; data_in = i;
            #10;
        end
        
        // FIFO should be full now
        push = 0; pop = 0;
        #10;
        
        // Empty the FIFO
        for (int i = 0; i < DEPTH; i++) begin
            push = 0; pop = 1;
            #10;
        end
        
        // FIFO should be empty now
        push = 0; pop = 0;
        #10;
        
        // Test almost flags by filling to almost full threshold
        for (int i = 0; i < DEPTH-3; i++) begin
            push = 1; pop = 0; data_in = 8'hA0 + i;
            #10;
        end
        push = 0; pop = 0;
        #10;
        
        // Empty to almost empty threshold
        for (int i = 0; i < DEPTH-5; i++) begin
            push = 0; pop = 1;
            #10;
        end
        
        // End simulation
        #10 $finish;
    end
endmodule