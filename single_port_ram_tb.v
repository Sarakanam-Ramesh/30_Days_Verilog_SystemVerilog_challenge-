`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 05.03.2025 21:17:05
// Design Name: 
// Module Name: single_port_ram_tb
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


// Testbench for Single Port RAM
module tb_single_port_ram();
    // Parameters
    parameter DATA_WIDTH = 8;
    parameter ADDR_WIDTH = 4;

    // Signals
    reg clk;
    reg we;
    reg [ADDR_WIDTH-1:0] addr;
    reg [DATA_WIDTH-1:0] din;
    wire [DATA_WIDTH-1:0] dout;

    // Instantiate DUT
    single_port_ram #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH)
    ) dut (
        .clk(clk),
        .we(we),
        .addr(addr),
        .din(din),
        .dout(dout)
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
        addr = 4'h7;
        din = 8'h5A;

        // Read operations
        @(posedge clk);
        we = 0;
        addr = 4'h3;

        @(posedge clk);
        addr = 4'h7;

        // Finish simulation
        #20 $finish;
    end
endmodule