`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 08.03.2025 16:27:48
// Design Name: 
// Module Name: metastability_handler_tb
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


module metastability_handler_tb;
    // Testbench signals
    logic clk;
    logic rst_n;
    logic [7:0] async_data;
    logic async_valid;
    logic [7:0] sync_data;
    logic sync_valid;
    
    // Clock period
    parameter CLK_PERIOD = 10;
    
    // Instantiate DUT
    metastability_handler #(
        .WIDTH(8),
        .STAGES(3)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .async_data(async_data),
        .async_valid(async_valid),
        .sync_data(sync_data),
        .sync_valid(sync_valid)
    );
    
    // Clock generation
    always #(CLK_PERIOD/2) clk = ~clk;
    
    // Test sequence
    initial begin
        $display("Starting Metastability Handler Test");
        
        // Initialize signals
        clk = 0;
        rst_n = 0;
        async_data = 8'h00;
        async_valid = 0;
        
        // Release reset
        #25 rst_n = 1;
        
        // Test asynchronous data transitions
        #3 async_data = 8'hA5;
           async_valid = 1;
        #7 async_valid = 0;
        
        // Wait for synchronization
        #30;
        
        // Send more data, some with more challenging timing
        for (int i = 1; i <= 5; i++) begin
            #(CLK_PERIOD * 0.3);  // Offset from clock edge
            async_data = 8'h10 + i;
            async_valid = 1;
            #5 async_valid = 0;
            #(CLK_PERIOD * 2);
        end
        
        // Run a bit longer
        #100;
        
        $display("Test Complete");
        $finish;
    end
    
    // Monitor
    initial begin
        $monitor("Time=%0dns: async_valid=%b, async_data=%h, sync_valid=%b, sync_data=%h",
                 $time, async_valid, async_data, sync_valid, sync_data);
    end
    
endmodule
