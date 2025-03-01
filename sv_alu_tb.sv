`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 25.02.2025 19:41:24
// Design Name: 
// Module Name: sv_alu_tb
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


// SystemVerilog Testbench for ALU
module sv_alu_tb;
    // Testbench signals
    logic [7:0] a;
    logic [7:0] b;
    logic [2:0] operation;
    logic [7:0] result;
    logic       zero_flag;
    logic       carry_flag;
    
    // Instantiate the DUT
    sv_alu dut (
        .a(a),
        .b(b),
        .operation(operation),
        .result(result),
        .zero_flag(zero_flag),
        .carry_flag(carry_flag)
    );
    // Test routine
    initial begin
        // Display information
        $display("SystemVerilog ALU Testbench (Combinational Logic)");
        $monitor("Time=%0t, A=%h, B=%h, Op=%b, Result=%h, Zero=%b, Carry=%b", $time, a, b, operation, result, zero_flag, carry_flag);
        // Test each operation
        a = 8'h33; b = 8'h55; operation = 3'b000; #10; // Pass A
        a = 8'h33; b = 8'h55; operation = 3'b001; #10; // Pass B
        a = 8'h33; b = 8'h55; operation = 3'b010; #10; // A + B
        a = 8'h33; b = 8'h22; operation = 3'b011; #10; // A - B
        a = 8'h33; b = 8'h55; operation = 3'b100; #10; // A AND B
        a = 8'h33; b = 8'h55; operation = 3'b101; #10; // A OR B
        a = 8'h33; b = 8'h55; operation = 3'b110; #10; // A XOR B
        a = 8'h33; b = 8'h55; operation = 3'b111; #10; // NOT A
        // Test overflow condition
        a = 8'hFF; b = 8'h01; operation = 3'b010; #10; // A + B (with carry)
        // Test zero flag
        a = 8'h55; b = 8'h55; operation = 3'b110; #10; // A XOR B (should be zero)
        // End simulation
        $display("Simulation complete");
        $finish;
    end
endmodule
