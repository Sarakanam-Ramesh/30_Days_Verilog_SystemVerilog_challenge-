`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11.03.2025 12:42:41
// Design Name: 
// Module Name: Cross_coverage
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


module alu_cross_17_tb;
  // Signals
  logic        clk;
  logic        rst_n;
  logic [7:0]  a;
  logic [7:0]  b;
  logic [2:0]  op;
  logic [7:0]  result;
  
  // Instantiate the ALU
  alu_17 dut (
    .clk(clk),
    .rst_n(rst_n),
    .a(a),
    .b(b),
    .op(op),
    .result(result)
  );
  
  // Clock generation
  always #5 clk = ~clk;
  
  // Coverage group with cross coverage
  covergroup alu_cross_cg @(posedge clk);
    option.per_instance = 1;
    
    // Cover the operation types
    operation: coverpoint op {
      bins add_op = {3'b000};
      bins sub_op = {3'b001};
      bins and_op = {3'b010};
      bins or_op  = {3'b011};
      bins xor_op = {3'b100};
      bins shl_op = {3'b101};
      bins shr_op = {3'b110};
    }
    
    // Simplified operand coverpoints for better cross coverage
    operand_a: coverpoint a {
      bins zero     = {0};
      bins non_zero = {[1:$]};
    }
    
    operand_b: coverpoint b {
      bins zero     = {0};
      bins non_zero = {[1:$]};
    }
    
    // Cross coverage between operation and operands
    op_with_a_b: cross operation, operand_a, operand_b {
      // Specifically target division by zero (for validation)
      ignore_bins div_by_zero = binsof(operation) intersect {3'b001} && 
                               binsof(operand_b) intersect {0};
    }
    
    // Special case for shifts - we're interested in shift amounts
    shift_amount: coverpoint b[2:0] iff (op inside {3'b101, 3'b110}) {
      bins small_shift = {[1:3]};
      bins med_shift   = {[4:6]};
      bins large_shift = {7};
    }
    
    // Cross coverage between shift operations and shift amounts
    shift_cross: cross operation, shift_amount {
      // Only interested in SHL and SHR operations for shift amount
      ignore_bins non_shift_ops = binsof(operation) intersect {3'b000, 3'b001, 3'b010, 3'b011, 3'b100};
    }
  endgroup
  
  // Create an instance of the coverage group
  alu_cross_cg cg_inst;
  
  // Stimulus
  initial begin
    // Initialize
    clk = 0;
    rst_n = 0;
    a = 0;
    b = 0;
    op = 0;
    
    // Create coverage group instance
    cg_inst = new();
    
    // Reset
    #10 rst_n = 1;
    
    // Cover all operations
    for (int i = 0; i < 7; i++) begin
      op = i;
      
      if (i inside {5, 6}) begin  // Shift operations
        a = 8'hFF;  // Set all bits
        
        // Test different shift amounts
        for (int shift = 0; shift <= 7; shift++) begin
          b = shift;
          #10;
        end
      end else begin  // Non-shift operations
        // Test different operand combinations
        for (int a_val = 0; a_val < 2; a_val++) begin
          for (int b_val = 0; b_val < 2; b_val++) begin
            a = a_val ? 8'h55 : 8'h00;  // Either 0 or non-zero
            b = b_val ? 8'hAA : 8'h00;  // Either 0 or non-zero
            #10;
          end
        end
        
        // Add a few more interesting combinations
        a = 8'hFF; b = 8'h01; #10;
        a = 8'h01; b = 8'hFF; #10;
      end
    end
    
    // Report coverage
    $display("Cross Coverage: %0.2f%%", $get_coverage());
    
    // End simulation
    #10 $finish;
  end
  
  // Monitor
  initial begin
    $monitor("Time=%0t: op=%b, a=%h, b=%h, result=%h", 
             $time, op, a, b, result);
  end
endmodule