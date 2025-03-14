`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 13.03.2025 14:46:33
// Design Name: 
// Module Name: Factory_pattern
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


// Synthesizable Factory Pattern
// Creates different hardware modules based on configuration input

module ProductFactory (
  input logic clk,
  input logic rst_n,
  input logic [1:0] product_select,
  input logic [7:0] config_data,
  output logic [7:0] product_output,
  output logic product_valid
);

  // Internal signals
  logic [7:0] product_a_output;
  logic [7:0] product_b_output;
  logic product_a_valid;
  logic product_b_valid;
  
  // Product A implementation
  ProductA product_a_inst (
    .clk(clk),
    .rst_n(rst_n),
    .enable(product_select == 2'b01),
    .config_data(config_data),
    .product_output(product_a_output),
    .product_valid(product_a_valid)
  );
  
  // Product B implementation
  ProductB product_b_inst (
    .clk(clk),
    .rst_n(rst_n),
    .enable(product_select == 2'b10),
    .config_data(config_data),
    .product_output(product_b_output),
    .product_valid(product_b_valid)
  );
  
  // Factory output selection
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      product_output <= 8'h00;
      product_valid <= 1'b0;
    end else begin
      case (product_select)
        2'b01: begin
          product_output <= product_a_output;
          product_valid <= product_a_valid;
        end
        2'b10: begin
          product_output <= product_b_output;
          product_valid <= product_b_valid;
        end
        default: begin
          product_output <= 8'h00;
          product_valid <= 1'b0;
        end
      endcase
    end
  end

endmodule

// Product A implementation
module ProductA (
  input logic clk,
  input logic rst_n,
  input logic enable,
  input logic [7:0] config_data,
  output logic [7:0] product_output,
  output logic product_valid
);

  // Product A specific processing
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      product_output <= 8'h00;
      product_valid <= 1'b0;
    end else if (enable) begin
      // Product A adds offset of 10 to the input
      product_output <= config_data + 8'd10;
      product_valid <= 1'b1;
    end else begin
      product_valid <= 1'b0;
    end
  end

endmodule

// Product B implementation
module ProductB (
  input logic clk,
  input logic rst_n,
  input logic enable,
  input logic [7:0] config_data,
  output logic [7:0] product_output,
  output logic product_valid
);

  // Product B specific processing
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      product_output <= 8'h00;
      product_valid <= 1'b0;
    end else if (enable) begin
      // Product B multiplies input by 2
      product_output <= config_data << 1;
      product_valid <= 1'b1;
    end else begin
      product_valid <= 1'b0;
    end
  end

endmodule

// Testbench
module factory_pattern_tb;
  logic clk;
  logic rst_n;
  logic [1:0] product_select;
  logic [7:0] config_data;
  logic [7:0] product_output;
  logic product_valid;
  
  // Instantiate the factory
  ProductFactory dut (
    .clk(clk),
    .rst_n(rst_n),
    .product_select(product_select),
    .config_data(config_data),
    .product_output(product_output),
    .product_valid(product_valid)
  );
  
  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end
  
  // Test sequence
  initial begin
    rst_n = 0;
    product_select = 2'b00;
    config_data = 8'h05;
    #20;
    
    rst_n = 1;
    #10;
    
    // Select Product A
    product_select = 2'b01;
    #20;
    if (product_valid) 
      $display("Product A output: %d (Expected: %d)", product_output, config_data + 8'd10);
    
    // Select Product B
    product_select = 2'b10;
    #20;
    if (product_valid)
      $display("Product B output: %d (Expected: %d)", product_output, config_data << 1);
    
    // No product selected
    product_select = 2'b00;
    #20;
    
    $finish;
  end
  
endmodule