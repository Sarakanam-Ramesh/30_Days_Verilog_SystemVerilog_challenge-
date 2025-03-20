`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 14.03.2025 23:32:14
// Design Name: 
// Module Name: 4_bit_alu_tb
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


module alu_4bit_tb();
    // Testbench signals
    reg clk;
    reg rst_n;
    reg [3:0] a;
    reg [3:0] b;
    reg [2:0] op_code;
    wire [4:0] result;
    wire zero_flag;
    
    // Instantiate the ALU
    alu_4bit DUT (
        .clk(clk),
        .rst_n(rst_n),
        .a(a),
        .b(b),
        .op_code(op_code),
        .result(result),
        .zero_flag(zero_flag)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 100MHz clock
    end
    
    // Stimulus generator
    initial begin
        // Initialize
        rst_n = 0;
        a = 4'b0000;
        b = 4'b0000;
        op_code = 3'b000;
        
        // Release reset
        #20 rst_n = 1;
        
        // Test ADD operation
        #10;
        a = 4'b0011; // 3
        b = 4'b0010; // 2
        op_code = 3'b000; // ADD
        
        // Test SUB operation
        #10;
        a = 4'b0111; // 7
        b = 4'b0010; // 2
        op_code = 3'b001; // SUB
        
        // Test AND operation
        #10;
        a = 4'b1100; // 12
        b = 4'b1010; // 10
        op_code = 3'b010; // AND
        
        // Test OR operation
        #10;
        a = 4'b1100; // 12
        b = 4'b0011; // 3
        op_code = 3'b011; // OR
        
        // Test XOR operation
        #10;
        a = 4'b1010; // 10
        b = 4'b0011; // 3
        op_code = 3'b100; // XOR
        
        // Test SHL operation
        #10;
        a = 4'b0101; // 5
        op_code = 3'b101; // SHL
        
        // Test SHR operation
        #10;
        a = 4'b1000; // 8
        op_code = 3'b110; // SHR
        
        // Run for a bit more time and finish
        #50 $finish;
    end
    
    // Response checker
    always @(posedge clk) begin
        if (rst_n) begin
            case (op_code)
                3'b000: begin // ADD
                    if (result !== a + b)
                        $display("Error: ADD operation failed. a=%d, b=%d, result=%d, expected=%d", 
                                a, b, result, a + b);
                    else
                        $display("ADD operation passed. a=%d, b=%d, result=%d", a, b, result);
                end
                
                3'b001: begin // SUB
                    if (result !== a - b)
                        $display("Error: SUB operation failed. a=%d, b=%d, result=%d, expected=%d", 
                                a, b, result, a - b);
                    else
                        $display("SUB operation passed. a=%d, b=%d, result=%d", a, b, result);
                end
                
                // More checks for other operations...
                
                default: begin
                    // Do nothing
                end
            endcase
            
            // Check zero flag
            if ((result == 5'b0 && zero_flag !== 1'b1) || (result != 5'b0 && zero_flag !== 1'b0))
                $display("Error: Zero flag incorrect. result=%d, zero_flag=%b", result, zero_flag);
        end
    end
    
    // Test sequencer is implicit in the initial block above
    
endmodule
