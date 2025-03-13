`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11.03.2025 12:36:48
// Design Name: 
// Module Name: Functional_coverage
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


module alu_17 (
  input        clk,
  input        rst_n,
  input  [7:0] a,
  input  [7:0] b,
  input  [2:0] op,
  output [7:0] result
);

  reg [7:0] result_r;
  
  // ALU operations
  parameter ADD = 3'b000;
  parameter SUB = 3'b001;
  parameter AND = 3'b010;
  parameter OR  = 3'b011;
  parameter XOR = 3'b100;
  parameter SHL = 3'b101;
  parameter SHR = 3'b110;
  
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      result_r <= 8'h00;
    end else begin
      case (op)
        ADD : result_r <= a + b;
        SUB : result_r <= a - b;
        AND : result_r <= a & b;
        OR  : result_r <= a | b;
        XOR : result_r <= a ^ b;
        SHL : result_r <= a << b[2:0];
        SHR : result_r <= a >> b[2:0];
        default : result_r <= 8'h00;
      endcase
    end
  end
  
  assign result = result_r;
  
endmodule

module alu_17_tb;
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
  
  // Coverage group for ALU operations
  covergroup alu_cg @(posedge clk);
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
    
    // Cover interesting input values
    operand_a: coverpoint a {
      bins zeros = {0};
      bins ones  = {8'hFF};
      bins Small = {[1:15]};
      bins med   = {[16:127]};
      bins Large = {[128:254]};
    }
    
    operand_b: coverpoint b {
      bins zeros = {0};
      bins ones  = {8'hFF};
      bins Small = {[1:15]};
      bins med   = {[16:127]};
      bins Large = {[128:254]};
    }
  endgroup
  
  // Create an instance of the coverage group
  alu_cg cg_inst;
  
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
    
    // Test each operation with various operands
    for (int i = 0; i < 7; i++) begin
      op = i;
      
      // Test different operand combinations for each operation
      for (int j = 0; j < 5; j++) begin
        case (j)
          0: begin a = 8'h00; b = 8'h00; end
          1: begin a = 8'hFF; b = 8'hFF; end
          2: begin a = 8'h0A; b = 8'h05; end
          3: begin a = 8'h30; b = 8'h50; end
          4: begin a = 8'hA0; b = 8'h0F; end
        endcase
        
        #10; // Wait for operation to complete
      end
    end
    
    // Report coverage
    $display("Coverage: %0.2f%%", $get_coverage());
    
    // End simulation
    #10 $finish;
  end
  
  // Monitor
  initial begin
    $monitor("Time=%0t: op=%b, a=%h, b=%h, result=%h", 
             $time, op, a, b, result);
  end
endmodule