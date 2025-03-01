`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// Create Date: 26.02.2025 21:52:33
// Design Name: 
// Module Name: enhanced_alu_sv_tb
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// Dependencies: 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
//////////////////////////////////////////////////////////////////////////////////
module enhanced_alu_sv_tb;
    logic [7:0] a, b; logic [2:0] op_code; logic [7:0] result; logic zero_flag;     // Testbench signals
    enhanced_alu_sv DUT ( .a(a), .b(b), .op_code(op_code), .result(result), .zero_flag(zero_flag));     // Instantiate the DUT
    task display_test;      // Helper task to display test results
        input string op_name;
        begin   $display("%0d\t%d\t%d\t%b\t%s\t%h\t%b",  $time, a, b, op_code, op_name, result, zero_flag);   end
    endtask
    // Test stimulus
    initial begin
        // Initialize display formatting
        $display("Time\ta\tb\top\tOperation\tResult\tZero");
        // Test ADD (op_code = 000)
        a = 8'd10; b = 8'd20; op_code = 3'b000; #10;
        display_test("ADD");
        // Test SUB (op_code = 001)
        a = 8'd30; b = 8'd15; op_code = 3'b001; #10;
        display_test("SUB");
        // Test SUB with zero result
        a = 8'd15; b = 8'd15; op_code = 3'b001; #10;
        display_test("SUB(zero)");
        // Test AND (op_code = 010)
        a = 8'hAA; b = 8'h55; op_code = 3'b010; #10;
        display_test("AND");
        // Test OR (op_code = 011)
        a = 8'hAA; b = 8'h55; op_code = 3'b011; #10;
        display_test("OR");
        // Test XOR (op_code = 100)
        a = 8'hFF; b = 8'h0F; op_code = 3'b100; #10;
        display_test("XOR");
        // Test NOT (op_code = 101)
        a = 8'hAA; b = 8'h00; op_code = 3'b101; #10;
        display_test("NOT");
        // Test Compare (op_code = 110)
        a = 8'd10; b = 8'd20; op_code = 3'b110; #10;
        display_test("CMP(a<b)");
        a = 8'd20; b = 8'd10; op_code = 3'b110; #10;
        display_test("CMP(a>b)");
        // Test Shift (op_code = 111)
        a = 8'h01; b = 8'h03; op_code = 3'b111; #10;
        display_test("SHIFT");
        $display("Test completed");
        $finish;
    end
endmodule
