`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 08.03.2025 16:21:32
// Design Name: 
// Module Name: clock_domain_crossing_tb
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


module clock_domain_crossing_tb;
    // Testbench signals
    logic clk_src;
    logic clk_dst;
    logic rst_n;
    logic [7:0] data_src;
    logic valid_src;
    logic ready_src;
    logic [7:0] data_dst;
    logic valid_dst;
    logic ready_dst;
    
    // Clock periods
    parameter SRC_CLK_PERIOD = 10;
    parameter DST_CLK_PERIOD = 15;
    
    // Instantiate DUT
    clock_domain_crossing dut (
        .clk_src(clk_src),
        .clk_dst(clk_dst),
        .rst_n(rst_n),
        .data_src(data_src),
        .valid_src(valid_src),
        .ready_src(ready_src),
        .data_dst(data_dst),
        .valid_dst(valid_dst),
        .ready_dst(ready_dst)
    );
    
    // Source clock generation
    always #(SRC_CLK_PERIOD/2) clk_src = ~clk_src;
    
    // Destination clock generation
    always #(DST_CLK_PERIOD/2) clk_dst = ~clk_dst;
    
    // Test sequence
    initial begin
        $display("Starting Clock Domain Crossing Test");
        
        // Initialize signals
        clk_src = 0;
        clk_dst = 0;
        rst_n = 0;
        data_src = 8'h00;
        valid_src = 0;
        ready_dst = 1;
        
        // Release reset
        #30 rst_n = 1;
        
        // Send several data values
        for (int i = 1; i <= 10; i++) begin
            @(posedge clk_src);
            wait(ready_src);
            data_src = i * 10;  // Example data: 10, 20, 30...
            valid_src = 1;
            @(posedge clk_src);
            valid_src = 0;
            
            // Wait for data to be transferred to destination domain
            wait(valid_dst);
            @(posedge clk_dst);
            $display("Time=%0dns: Data transferred: src=%0d, dst=%0d", 
                     $time, data_src, data_dst);
            
            // Control destination ready signal
            if (i % 3 == 0) begin
                ready_dst = 0;
                repeat(2) @(posedge clk_dst);
                ready_dst = 1;
            end
        end
        
        // Run a bit longer
        #100;
        
        $display("Test Complete");
        $finish;
    end
    
    // Monitor
    initial begin
        $monitor("Time=%0dns: valid_src=%b, ready_src=%b, valid_dst=%b, ready_dst=%b",
                 $time, valid_src, ready_src, valid_dst, ready_dst);
    end
    
endmodule
