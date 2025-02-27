`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// Create Date: 27.02.2025 20:59:57
// Design Name: 
// Module Name: shift_register_tb
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// Dependencies: 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
//////////////////////////////////////////////////////////////////////////////////
module shift_register_tb;
    parameter WIDTH = 8;    // Parameters
    // Testbench signals
    reg clk; reg reset; reg shift_en; reg direction; reg data_in; wire [WIDTH-1:0] data_out;
    // Instantiate the shift register module
    shift_register #( .WIDTH(WIDTH)) dut ( .clk(clk), .reset(reset), .shift_en(shift_en), .direction(direction), .data_in(data_in), .data_out(data_out));
    // Clock generation
    initial begin
        clk = 0; forever #5 clk = ~clk; // 10ns period clock
    end
    // Test sequence
    initial begin
        // Initialize signals
        reset = 1; shift_en = 0;
        direction = 0; data_in = 0;
        // Apply reset
        #20; reset = 0; #10;
        // Test left shift (direction = 0)
        shift_en = 1; direction = 0;
        // Shift in pattern 10101010
        data_in = 1; #10; data_in = 0; #10; data_in = 1; #10; data_in = 0; #10;
        data_in = 1; #10; data_in = 0; #10; data_in = 1; #10; data_in = 0; #10;
        // Pause shifting to observe result
        shift_en = 0;
        #20;  $display("After left shift pattern: %b", data_out);
        // Reset
        reset = 1; #20; 
        reset = 0; #10;
        // Test right shift (direction = 1)
        shift_en = 1; direction = 1;
        // Shift in pattern 10101010 from the left
        data_in = 1; #10; data_in = 0; #10; data_in = 1; #10; data_in = 0; #10;
        data_in = 1; #10; data_in = 0; #10; data_in = 1; #10; data_in = 0; #10;
        // Pause shifting to observe result
        shift_en = 0;
        #20; $display("After right shift pattern: %b", data_out);
        // End simulation
        #10; $finish;
    end
    // Monitor changes
    initial begin
        $monitor("Time: %0t, Reset: %b, ShiftEn: %b, Direction: %b, DataIn: %b, DataOut: %b", $time, reset, shift_en, direction, data_in, data_out);
    end
endmodule