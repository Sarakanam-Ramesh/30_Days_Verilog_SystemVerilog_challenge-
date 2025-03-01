`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 26.02.2025 21:07:17
// Design Name: 
// Module Name: priority_encoder_3bit_tb
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


module priority_encoder_3bit_tb;
    // Testbench signals
    reg [2:0] in;
    wire [1:0] out;
    wire valid;
    
    // Instantiate the DUT
    priority_encoder_3bit DUT (
        .in(in),
        .out(out),
        .valid(valid)
    );
    
    // Test stimulus
    initial begin
        // Initialize display formatting
        $display("Time\tin\tout\tvalid");
        $monitor("%0d\t%b\t%b\t%b", $time, in, out, valid);
        
        // Test all possible input combinations
        in = 3'b000; #10;  // Should output valid=0
        in = 3'b001; #10;  // Should output out=00, valid=1
        in = 3'b010; #10;  // Should output out=01, valid=1
        in = 3'b011; #10;  // Should output out=00, valid=1 (priority to bit 0)
        in = 3'b100; #10;  // Should output out=10, valid=1
        in = 3'b101; #10;  // Should output out=00, valid=1 (priority to bit 0)
        in = 3'b110; #10;  // Should output out=01, valid=1 (priority to bit 1)
        in = 3'b111; #10;  // Should output out=00, valid=1 (priority to bit 0)
        
        $display("Test completed");
        $finish;
    end
endmodule
