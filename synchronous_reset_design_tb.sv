`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 08.03.2025 16:31:53
// Design Name: 
// Module Name: synchronous_reset_design_tb
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


module synchronous_reset_tb;
    // Testbench signals
    logic clk;
    logic async_rst_n;
    logic sync_rst;
    logic [15:0] data_in;
    logic valid_in;
    logic [15:0] data_out;
    logic valid_out;
    
    // Clock period
    parameter CLK_PERIOD = 10;
    
    // Instantiate DUT
    synchronous_reset_design dut (
        .clk(clk),
        .async_rst_n(async_rst_n),
        .sync_rst(sync_rst),
        .data_in(data_in),
        .valid_in(valid_in),
        .data_out(data_out),
        .valid_out(valid_out)
    );
    
    // Clock generation
    always #(CLK_PERIOD/2) clk = ~clk;
    
    // Test sequence
    initial begin
        $display("Starting Synchronous Reset Design Test");
        
        // Initialize signals
        clk = 0;
        async_rst_n = 0;
        sync_rst = 0;
        data_in = 16'h0000;
        valid_in = 0;
        
        // Release asynchronous reset
        #25 async_rst_n = 1;
        
        // Send some data
        for (int i = 1; i <= 5; i++) begin
            @(posedge clk);
            data_in = 16'h1000 + i;
            valid_in = 1;
            @(posedge clk);
            valid_in = 0;
            @(posedge clk);
            @(posedge clk);
        end
        
        // Apply synchronous reset
        @(posedge clk);
        sync_rst = 1;
        @(posedge clk);
        sync_rst = 0;
        
        // Send more data
        for (int i = 1; i <= 3; i++) begin
            @(posedge clk);
            data_in = 16'h2000 + i;
            valid_in = 1;
            @(posedge clk);
            valid_in = 0;
            @(posedge clk);
        end
        
        // Apply asynchronous reset at a non-clock edge
        #3 async_rst_n = 0;
        #10 async_rst_n = 1;
        
        // Send final data
        for (int i = 1; i <= 2; i++) begin
            @(posedge clk);
            data_in = 16'h3000 + i;
            valid_in = 1;
            @(posedge clk);
            valid_in = 0;
            @(posedge clk);
        end
        
        // Run a bit longer
        #50;
        
        $display("Test Complete");
        $finish;
    end
    
    // Monitor
    initial begin
        $monitor("Time=%0dns: async_rst_n=%b, sync_rst=%b, valid_in=%b, data_in=%h, valid_out=%b, data_out=%h",
                 $time, async_rst_n, sync_rst, valid_in, data_in, valid_out, data_out);
    end
    
endmodule
