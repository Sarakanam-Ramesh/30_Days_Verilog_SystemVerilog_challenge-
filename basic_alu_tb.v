`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 26.02.2025 21:12:37
// Design Name: 
// Module Name: basic_alu_tb
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


module basic_alu_tb;
    // Testbench signals
    reg [7:0] a, b;
    reg [1:0] op_code;
    wire [7:0] result;
    
    // Instantiate the DUT
    basic_alu DUT (
        .a(a),
        .b(b),
        .op_code(op_code),
        .result(result)
    );
    
    // Test stimulus
    initial begin
        // Initialize display formatting
        $display("Time\ta\tb\top_code\tresult\tExpected");
        
        // Test cases for each operation
        // ADD (op_code = 00)
        a = 8'd10; b = 8'd5; op_code = 2'b00; #10;
        $display("%0d\t%d\t%d\t%b\t%d\t%d", $time, a, b, op_code, result, (a + b));
        a = 8'd255; b = 8'd1; op_code = 2'b00; #10;
        $display("%0d\t%d\t%d\t%b\t%d\t%d", $time, a, b, op_code, result, (a + b));
        // SUB (op_code = 01)
        a = 8'd10; b = 8'd5; op_code = 2'b01; #10;
        $display("%0d\t%d\t%d\t%b\t%d\t%d", $time, a, b, op_code, result, (a - b));
        a = 8'd5; b = 8'd10; op_code = 2'b01; #10;
        $display("%0d\t%d\t%d\t%b\t%d\t%d", $time, a, b, op_code, result, (a - b));
        // AND (op_code = 10)
        a = 8'b10101010; b = 8'b11001100; op_code = 2'b10; #10;
        $display("%0d\t%b\t%b\t%b\t%b\t%b", $time, a, b, op_code, result, (a & b));
        // OR (op_code = 11)
        a = 8'b10101010; b = 8'b11001100; op_code = 2'b11; #10;
        $display("%0d\t%b\t%b\t%b\t%b\t%b", $time, a, b, op_code, result, (a | b));
        $display("Test completed");
        $finish;
    end
endmodule
