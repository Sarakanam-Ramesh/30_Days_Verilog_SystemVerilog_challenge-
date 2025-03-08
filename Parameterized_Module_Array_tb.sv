`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06.03.2025 18:39:30
// Design Name: 
// Module Name: Parameterized_Module_Array_tb
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


module processing_array_tb;
    parameter ARRAY_SIZE = 4;
    parameter DATA_WIDTH = 8;
    
    logic clk, rst_n;
    logic [DATA_WIDTH-1:0] data_in;
    logic [ARRAY_SIZE-1:0][DATA_WIDTH-1:0] data_out;
    
    // Instantiate the DUT
    processing_array #(
        .ARRAY_SIZE(ARRAY_SIZE),
        .DATA_WIDTH(DATA_WIDTH)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .data_in(data_in),
        .data_out(data_out)
    );
    
    // Clock generation
    always #5 clk = ~clk;
    
    // Test vectors and display
    initial begin
        // Initialize
        clk = 0; rst_n = 0; data_in = 8'h10;
        
        // Release reset
        #15 rst_n = 1;
        
        // Test different input values
        for (int i = 0; i < 5; i++) begin
            data_in = 8'h10 * (i + 1);
            #10;
            $display("Time=%0t: data_in=0x%h, data_out=[0x%h, 0x%h, 0x%h, 0x%h]", 
                     $time, data_in, 
                     data_out[0], data_out[1], data_out[2], data_out[3]);
        end
        
        // End simulation
        $finish;
    end
endmodule
