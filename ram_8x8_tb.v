`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// Create Date: 27.02.2025 20:45:51
// Design Name: 
// Module Name: ram_8x8_tb
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// Dependencies: 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
//////////////////////////////////////////////////////////////////////////////////
module ram_8x8_tb;
    // Testbench signals
    reg clk; reg reset; reg write_en; reg [2:0] addr; reg [7:0] data_in; wire [7:0] data_out;
    // Instantiate the RAM module
    ram_8x8 dut ( .clk(clk), .reset(reset), .write_en(write_en), .addr(addr), .data_in(data_in), .data_out(data_out));
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 10ns period clock
    end
    // Test sequence
    initial begin
        // Initialize signals
        reset = 1;
        write_en = 0;
        addr = 0;
        data_in = 0;
        // Apply reset
        #20; reset = 0;
        #10; write_en = 1;           // Write data to different addresses
        addr = 3'b000;          // Write to address 0
        data_in = 8'hA5;
        #10; addr = 3'b011;          // Write to address 3
        data_in = 8'h3C;
        #10; addr = 3'b111;          // Write to address 7
        data_in = 8'hF0;
        #10; write_en = 0;           // Read operations
        addr = 3'b000;          // Read from address 0
        #10; $display("Read from address 0: %h", data_out);
        addr = 3'b011;          // Read from address 3
        #10; $display("Read from address 3: %h", data_out);
        addr = 3'b111;          // Read from address 7
        #10; $display("Read from address 7: %h", data_out);
        addr = 3'b010;          // Read from unwritten address
        #10; $display("Read from address 2: %h", data_out);
        // End simulation
        #10; $finish;
    end
    // Monitor changes
    initial begin
        $monitor("Time: %0t, Reset: %b, WriteEn: %b, Addr: %b, DataIn: %h, DataOut: %h",  $time, reset, write_en, addr, data_in, data_out);
    end
endmodule
