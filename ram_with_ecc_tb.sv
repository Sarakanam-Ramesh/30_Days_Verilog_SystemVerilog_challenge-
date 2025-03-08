`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 05.03.2025 21:38:38
// Design Name: 
// Module Name: ram_with_ecc
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


// Testbench for RAM with Error Checking
module tb_ram_with_ecc();
    parameter DATA_WIDTH = 8;
    parameter ADDR_WIDTH = 4;

    logic clk;
    logic we;
    logic [ADDR_WIDTH-1:0] addr;
    logic [DATA_WIDTH-1:0] din;
    logic [DATA_WIDTH-1:0] dout;
    logic single_bit_error;
    logic double_bit_error;

    // Instantiate DUT
    ram_with_ecc #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH)
    ) dut (
        .clk(clk),
        .we(we),
        .addr(addr),
        .din(din),
        .dout(dout),
        .single_bit_error(single_bit_error),
        .double_bit_error(double_bit_error)
    );

    // Clock generation
    always #5 clk = ~clk;

    // Stimulus
    initial begin
        // Initialize
        clk = 0;
        we = 0;
        addr = 0;
        din = 0;

        // Write some data
        @(posedge clk);
        we = 1;
        addr = 4'h3;
        din = 8'hA5;

        @(posedge clk);
        we = 0;
        addr = 4'h3;

        // Simulate error detection scenarios
        @(posedge clk);
        // Additional test scenarios for error checking

        // Finish simulation
        #20 $finish;
    end
endmodule
