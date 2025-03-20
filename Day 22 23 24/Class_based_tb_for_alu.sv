`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 14.03.2025 23:40:08
// Design Name: 
// Module Name: Class_based_tb_for_alu
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


`timescale 1ns/1ps

// Transaction class
class AluTransaction;
    rand bit [3:0] a;
    rand bit [3:0] b;
    rand bit [2:0] op_code;
    bit [4:0] expected_result;
    bit expected_zero_flag;
    
    // Compute expected results
    function void compute_expected();
        case (op_code)
            3'b000: expected_result = a + b;                // ADD
            3'b001: expected_result = a - b;                // SUB
            3'b010: expected_result = a & b;                // AND
            3'b011: expected_result = a | b;                // OR
            3'b100: expected_result = a ^ b;                // XOR
            3'b101: expected_result = {1'b0, a} << 1;       // SHL
            3'b110: expected_result = {1'b0, a} >> 1;       // SHR
            default: expected_result = 5'b0;
        endcase
        
        expected_zero_flag = (expected_result == 5'b0) ? 1'b1 : 1'b0;
    endfunction
    
    // Display transaction
    function void display(string prefix = "");
        $display("%sALU Transaction: a=%0d, b=%0d, op_code=%0d", prefix, a, b, op_code);
    endfunction
    
    // Constraint to limit operations to valid ones
    constraint valid_op_code {
        op_code inside {[0:6]};
    }
endclass

// Driver class
class AluDriver;
    virtual alu_4bit_if vif;
    
    function new(virtual alu_4bit_if vif);
        this.vif = vif;
    endfunction
    
    task drive(AluTransaction tx);
        @(posedge vif.clk);
        vif.a <= tx.a;
        vif.b <= tx.b;
        vif.op_code <= tx.op_code;
        tx.display("Driving: ");
    endtask
endclass

// Monitor class
class AluMonitor;
    virtual alu_4bit_if vif;
    mailbox #(AluTransaction) mbx;
    
    function new(virtual alu_4bit_if vif, mailbox #(AluTransaction) mbx);
        this.vif = vif;
        this.mbx = mbx;
    endfunction
    
    task run();
        forever begin
            AluTransaction tx = new();
            @(posedge vif.clk);
            @(posedge vif.clk); // Wait an additional cycle for the result
            
            tx.a = vif.a;
            tx.b = vif.b;
            tx.op_code = vif.op_code;
            tx.compute_expected();
            
            mbx.put(tx);
        end
    endtask
endclass

// Scoreboard class
class AluScoreboard;
    mailbox #(AluTransaction) mbx;
    int passed = 0;
    int failed = 0;
    
    function new(mailbox #(AluTransaction) mbx);
        this.mbx = mbx;
    endfunction
    
    task run();
        forever begin
            AluTransaction tx;
            mbx.get(tx);
            
            // Get the actual result and compare
            if (compare_results(tx)) begin
                passed++;
                $display("TEST PASSED: op_code=%0d, a=%0d, b=%0d, result=%0d", 
                          tx.op_code, tx.a, tx.b, g_actual_result);
            end else begin
                failed++;
                $display("TEST FAILED: op_code=%0d, a=%0d, b=%0d", 
                          tx.op_code, tx.a, tx.b);
                $display("Expected: result=%0d, zero_flag=%0b", 
                          tx.expected_result, tx.expected_zero_flag);
                $display("Actual: result=%0d, zero_flag=%0b", 
                          g_actual_result, g_actual_zero_flag);
            end
        end
    endtask
    
    bit [4:0] g_actual_result;
    bit g_actual_zero_flag;
    
    function bit compare_results(AluTransaction tx);
        // In a real implementation, we would access the DUT outputs
        g_actual_result = vif.result;
        g_actual_zero_flag = vif.zero_flag;
        
        return (tx.expected_result === g_actual_result) && 
               (tx.expected_zero_flag === g_actual_zero_flag);
    endfunction
    
    function void report();
        $display("----------------------------------------------");
        $display("Scoreboard Report");
        $display("Tests Passed: %0d", passed);
        $display("Tests Failed: %0d", failed);
        $display("----------------------------------------------");
    endfunction
endclass

// Interface for the ALU
interface alu_4bit_if(input logic clk, input logic rst_n);
    logic [3:0] a;
    logic [3:0] b;
    logic [2:0] op_code;
    logic [4:0] result;
    logic zero_flag;
endinterface

// Top-level testbench module
module alu_4bit_sv_tb();
    // Clock and reset
    logic clk;
    logic rst_n;
    
    // Generate clock
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // Interface instance
    alu_4bit_if alu_if(clk, rst_n);
    
    // DUT instance
    alu_4bit DUT (
        .clk(clk),
        .rst_n(rst_n),
        .a(alu_if.a),
        .b(alu_if.b),
        .op_code(alu_if.op_code),
        .result(alu_if.result),
        .zero_flag(alu_if.zero_flag)
    );
    
    // Testbench components
    AluDriver driver;
    AluMonitor monitor;
    AluScoreboard scoreboard;
    mailbox #(AluTransaction) mbx;
    
    // Test program
    initial begin
        // Initialize
        rst_n = 0;
        mbx = new();
        driver = new(alu_if);
        monitor = new(alu_if, mbx);
        scoreboard = new(mbx);
        
        // Start monitor and scoreboard
        fork
            monitor.run();
            scoreboard.run();
        join_none
        
        // Release reset
        #20 rst_n = 1;
        
        // Run 20 random tests
        repeat(20) begin
            AluTransaction tx = new();
            assert(tx.randomize());
            tx.compute_expected();
            driver.drive(tx);
            #10; // Wait for processing
        end
        
        // Finish up
        #50;
        scoreboard.report();
        $finish;
    end
endmodule
