`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 26.02.2025 21:45:41
// Design Name: 
// Module Name: priority_encoder_sv_tb
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


module priority_encoder_sv_tb;
    // Testbench signals
    logic [2:0] in;
    logic [1:0] out;
    logic valid;
    
    // Instantiate the DUT
    priority_encoder_sv DUT (
        .in(in),
        .out(out),
        .valid(valid)
    );
    
    // Test stimulus
    initial begin
        // Initialize display formatting
        $display("Time\tin\tout\tvalid\tComment");
        // Test all input combinations
        in = 3'b000; #10;
        $display("%0d\t%b\t%b\t%b\tNo bits set", $time, in, out, valid);
        in = 3'b001; #10;
        $display("%0d\t%b\t%b\t%b\tBit 0 set", $time, in, out, valid);
        in = 3'b010; #10;
        $display("%0d\t%b\t%b\t%b\tBit 1 set", $time, in, out, valid);
        in = 3'b100; #10;
        $display("%0d\t%b\t%b\t%b\tBit 2 set", $time, in, out, valid);
        in = 3'b011; #10;
        $display("%0d\t%b\t%b\t%b\tBits 0,1 set (priority to bit 1)", $time, in, out, valid);
        in = 3'b101; #10;
        $display("%0d\t%b\t%b\t%b\tBits 0,2 set (priority to bit 2)", $time, in, out, valid);
        in = 3'b110; #10;
        $display("%0d\t%b\t%b\t%b\tBits 1,2 set (priority to bit 2)", $time, in, out, valid);
        in = 3'b111; #10;
        $display("%0d\t%b\t%b\t%b\tAll bits set (priority to bit 2)", $time, in, out, valid);
        $display("Test completed");
        $finish;
    end
endmodule