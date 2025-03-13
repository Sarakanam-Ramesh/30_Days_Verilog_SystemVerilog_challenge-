`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11.03.2025 14:46:02
// Design Name: 
// Module Name: Shared_memory
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


module shared_memory_18 (
  input         clk,
  input         rst_n,
  
  // Writer interface
  input         wr_en,
  input  [3:0]  wr_addr,
  input  [7:0]  wr_data,
  output        wr_ack,
  
  // Reader interface
  input         rd_en,
  input  [3:0]  rd_addr,
  output [7:0]  rd_data,
  output        rd_valid
);

  // Shared memory (16x8 RAM)
  reg [7:0] mem [0:15];
  
  // Writer control
  reg wr_ack_reg;
  
  // Reader control
  reg [7:0] rd_data_reg;
  reg rd_valid_reg;
  
  // Memory write process
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      wr_ack_reg <= 1'b0;
      
      // Initialize memory (for simulation)
      for (integer i = 0; i < 16; i = i + 1) begin
        mem[i] <= 8'h00;
      end
    end
    else begin
      wr_ack_reg <= 1'b0;
      
      if (wr_en) begin
        mem[wr_addr] <= wr_data;
        wr_ack_reg <= 1'b1;
      end
    end
  end
  
  // Memory read process
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      rd_data_reg <= 8'h00;
      rd_valid_reg <= 1'b0;
    end
    else begin
      rd_valid_reg <= 1'b0;
      
      if (rd_en) begin
        rd_data_reg <= mem[rd_addr];
        rd_valid_reg <= 1'b1;
      end
    end
  end
  
  // Output assignments
  assign wr_ack = wr_ack_reg;
  assign rd_data = rd_data_reg;
  assign rd_valid = rd_valid_reg;
  
endmodule

`timescale 1ns/1ps

module shared_memory_18_tb;
  
  // Signals
  reg         clk;
  reg         rst_n;
  
  // Writer signals
  reg         wr_en;
  reg  [3:0]  wr_addr;
  reg  [7:0]  wr_data;
  wire        wr_ack;
  
  // Reader signals
  reg         rd_en;
  reg  [3:0]  rd_addr;
  wire [7:0]  rd_data;
  wire        rd_valid;
  
  // Instantiate DUT
  shared_memory_18 dut (
    .clk(clk),
    .rst_n(rst_n),
    .wr_en(wr_en),
    .wr_addr(wr_addr),
    .wr_data(wr_data),
    .wr_ack(wr_ack),
    .rd_en(rd_en),
    .rd_addr(rd_addr),
    .rd_data(rd_data),
    .rd_valid(rd_valid)
  );
  
  // Clock generation
  always #5 clk = ~clk;
  
  // Writer process
  task write_data(input [3:0] addr, input [7:0] data);
    begin
      @(posedge clk);
      wr_en <= 1'b1;
      wr_addr <= addr;
      wr_data <= data;
      @(posedge clk);
      wr_en <= 1'b0;
      // Wait for ack
      @(posedge wr_ack);
      @(posedge clk);
    end
  endtask
  
  // Reader process
  task read_data(input [3:0] addr);
    begin
      @(posedge clk);
      rd_en <= 1'b1;
      rd_addr <= addr;
      @(posedge clk);
      rd_en <= 1'b0;
      // Wait for valid
      @(posedge rd_valid);
      $display("Read Data: addr=%h, data=%h", addr, rd_data);
      @(posedge clk);
    end
  endtask
  
  // Test sequence
  initial begin
    // Initialize
    clk = 0;
    rst_n = 0;
    wr_en = 0;
    wr_addr = 0;
    wr_data = 0;
    rd_en = 0;
    rd_addr = 0;
    
    // Reset
    #20 rst_n = 1;
    
    // Test Case 1: Write to multiple addresses
    write_data(4'h0, 8'hA1);
    write_data(4'h1, 8'hB2);
    write_data(4'h2, 8'hC3);
    write_data(4'h3, 8'hD4);
    
    // Test Case 2: Read from the same addresses
    read_data(4'h0);
    read_data(4'h1);
    read_data(4'h2);
    read_data(4'h3);
    
    // Test Case 3: Interleaved read and write
    write_data(4'h5, 8'hE5);
    read_data(4'h5);
    write_data(4'h5, 8'hF6);
    read_data(4'h5);
    
    // End simulation
    #20 $finish;
  end
  
  // Monitor
  initial begin
    $monitor("Time=%0t: wr_en=%b, wr_addr=%h, wr_data=%h, wr_ack=%b, rd_en=%b, rd_addr=%h, rd_data=%h, rd_valid=%b", 
             $time, wr_en, wr_addr, wr_data, wr_ack, rd_en, rd_addr, rd_data, rd_valid);
  end
  
endmodule