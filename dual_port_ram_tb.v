`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 05.03.2025 21:26:14
// Design Name: 
// Module Name: dual_port_ram_tb
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


// Testbench for Dual Port RAM
module tb_dual_port_ram();
    // Parameters
    parameter DATA_WIDTH = 8;
    parameter ADDR_WIDTH = 4;

    // Signals
    reg clk;
    reg we_a, we_b;
    reg [ADDR_WIDTH-1:0] addr_a, addr_b;
    reg [DATA_WIDTH-1:0] din_a, din_b;
    wire [DATA_WIDTH-1:0] dout_a, dout_b;

    // Instantiate DUT
    dual_port_ram #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH)
    ) dut (
        .clk(clk),
        .we_a(we_a),
        .addr_a(addr_a),
        .din_a(din_a),
        .dout_a(dout_a),
        .we_b(we_b),
        .addr_b(addr_b),
        .din_b(din_b),
        .dout_b(dout_b)
    );

    // Clock generation
    always #5 clk = ~clk;

    // Stimulus
    initial begin
        // Initialize
        clk = 0;
        we_a = 0;
        we_b = 0;
        addr_a = 0;
        addr_b = 0;
        din_a = 0;
        din_b = 0;

        // Simultaneous writes and reads
        @(posedge clk);
        we_a = 1;
        addr_a = 4'h3;
        din_a = 8'hA5;

        we_b = 1;
        addr_b = 4'h7;
        din_b = 8'h5A;

        @(posedge clk);
        we_a = 0;
        we_b = 0;
        addr_a = 4'h3;
        addr_b = 4'h7;

        // Finish simulation
        #20 $finish;
    end
endmodule