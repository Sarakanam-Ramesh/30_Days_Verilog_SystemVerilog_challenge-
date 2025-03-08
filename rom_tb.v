`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 05.03.2025 21:34:25
// Design Name: 
// Module Name: rom_tb
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


// Testbench for ROM
module tb_rom();
    // Parameters
    parameter DATA_WIDTH = 8;
    parameter ADDR_WIDTH = 4;

    // Signals
    reg clk;
    reg [ADDR_WIDTH-1:0] addr;
    wire [DATA_WIDTH-1:0] dout;

    // Instantiate DUT
    rom #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH)
    ) dut (
        .clk(clk),
        .addr(addr),
        .dout(dout)
    );

    // Clock generation
    always #5 clk = ~clk;

    // Stimulus
    initial begin
        // Initialize
        clk = 0;
        addr = 0;

        // Read from different addresses
        repeat(8) begin
            @(posedge clk);
            addr = addr + 1;
        end

        // Finish simulation
        #20 $finish;
    end
endmodule
