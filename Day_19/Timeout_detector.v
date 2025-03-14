`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 13.03.2025 16:22:20
// Design Name: 
// Module Name: Timeout_detector
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


module timeout_detector #(
    parameter TIMEOUT_COUNT = 1000
) (
    input wire clk,
    input wire rst_n,
    input wire signal_in,
    output reg timeout_flag
);

    // Internal signals
    reg [31:0] counter;
    reg signal_in_prev;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            counter <= 32'h0;
            timeout_flag <= 1'b0;
            signal_in_prev <= 1'b0;
        end else begin
            signal_in_prev <= signal_in;
            
            // Reset counter when signal changes
            if (signal_in != signal_in_prev) begin
                counter <= 32'h0;
                timeout_flag <= 1'b0;
            end else begin
                // Increment counter and check for timeout
                if (counter >= TIMEOUT_COUNT - 1) begin
                    timeout_flag <= 1'b1;
                end else begin
                    counter <= counter + 1'b1;
                end
            end
        end
    end

endmodule

`timescale 1ns/1ps

module timeout_detector_tb();
    // Parameters
    localparam TIMEOUT_COUNT = 20; // Smaller value for simulation
    
    // Testbench signals
    reg clk;
    reg rst_n;
    reg signal_in;
    wire timeout_flag;
    
    // Instantiate the DUT
    timeout_detector #(
        .TIMEOUT_COUNT(TIMEOUT_COUNT)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .signal_in(signal_in),
        .timeout_flag(timeout_flag)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 100MHz clock
    end
    
    // Test sequence
    initial begin
        // Initialize
        rst_n = 0;
        signal_in = 0;
        #20;
        
        // Release reset
        rst_n = 1;
        #10;
        
        // Generate some activity
        signal_in = 1;
        #10;
        signal_in = 0;
        #10;
        signal_in = 1;
        #10;
        
        // Hold signal constant to trigger timeout
        // Wait for TIMEOUT_COUNT + a few extra cycles
        #((TIMEOUT_COUNT + 5) * 10);
        
        // Change signal again
        signal_in = 0;
        #20;
        
        // Complete the simulation
        #100;
        $display("Simulation completed");
        $finish;
    end
    
    // Monitor
    initial begin
        $monitor("Time=%0t, signal_in=%b, timeout_flag=%b", 
                 $time, signal_in, timeout_flag);
    end
    
endmodule
