`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11.03.2025 12:48:10
// Design Name: 
// Module Name: Coverage_driven_test
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


module fifo_17 #(
  parameter WIDTH = 8,
  parameter DEPTH = 16
) (
  input                   clk,
  input                   rst_n,
  input                   wr_en,
  input                   rd_en,
  input      [WIDTH-1:0]  wr_data,
  output reg [WIDTH-1:0]  rd_data,
  output reg              full,
  output reg              empty
);
  
  // Log2 function for address width calculation
  function integer clog2;
    input integer value;
    begin
      value = value - 1;
      for (clog2 = 0; value > 0; clog2 = clog2 + 1)
        value = value >> 1;
    end
  endfunction
  
  // Local parameters
  localparam ADDR_WIDTH = clog2(DEPTH);
  
  // Internal signals
  reg [WIDTH-1:0]      mem [0:DEPTH-1];
  reg [ADDR_WIDTH:0]   wr_ptr;
  reg [ADDR_WIDTH:0]   rd_ptr;
  wire [ADDR_WIDTH:0]  next_wr_ptr;
  wire [ADDR_WIDTH:0]  next_rd_ptr;
  wire                 wr_en_int;
  wire                 rd_en_int;
  
  // FIFO status
  assign next_wr_ptr = wr_ptr + 1'b1;
  assign next_rd_ptr = rd_ptr + 1'b1;
  
  assign full  = (next_wr_ptr[ADDR_WIDTH-1:0] == rd_ptr[ADDR_WIDTH-1:0]) && 
                 (next_wr_ptr[ADDR_WIDTH] != rd_ptr[ADDR_WIDTH]);
  assign empty = (wr_ptr == rd_ptr);
  
  // Internal enable signals
  assign wr_en_int = wr_en & ~full;
  assign rd_en_int = rd_en & ~empty;
  
  // Write pointer
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      wr_ptr <= 0;
    else if (wr_en_int)
      wr_ptr <= next_wr_ptr;
  end
  
  // Read pointer
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      rd_ptr <= 0;
    else if (rd_en_int)
      rd_ptr <= next_rd_ptr;
  end
  
  // Memory write
  always @(posedge clk) begin
    if (wr_en_int)
      mem[wr_ptr[ADDR_WIDTH-1:0]] <= wr_data;
  end
  
  // Memory read
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      rd_data <= 0;
    else if (rd_en_int)
      rd_data <= mem[rd_ptr[ADDR_WIDTH-1:0]];
  end
  
endmodule

module fifo_17_cov_tb;
  // Parameters
  parameter WIDTH = 8;
  parameter DEPTH = 16;
  
  // Signals
  logic                clk;
  logic                rst_n;
  logic                wr_en;
  logic                rd_en;
  logic [WIDTH-1:0]    wr_data;
  logic [WIDTH-1:0]    rd_data;
  logic                full;
  logic                empty;
  
  // FIFO level tracking
  int fifo_level;
  
  // Test phase tracking flags
  bit tested_full = 0;
  bit tested_almost_full_to_empty = 0;
  bit tested_alternating_pattern = 0;
  bit tested_simultaneous_rw = 0;
  
  // Instantiate the FIFO
  fifo_17 #(
    .WIDTH(WIDTH),
    .DEPTH(DEPTH)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .wr_en(wr_en),
    .rd_en(rd_en),
    .wr_data(wr_data),
    .rd_data(rd_data),
    .full(full),
    .empty(empty)
  );
  
  // Clock generation
  always #5 clk = ~clk;
  
  // FIFO level tracking
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      fifo_level <= 0;
    else begin
      if (wr_en && !full && !rd_en)
        fifo_level <= fifo_level + 1;
      else if (rd_en && !empty && !wr_en)
        fifo_level <= fifo_level - 1;
      else if (wr_en && !full && rd_en && !empty)
        fifo_level <= fifo_level; // Simultaneous read and write
    end
  end
  
  // Coverage model
  covergroup fifo_cg @(posedge clk);
    option.per_instance = 1;
    
    // Cover FIFO operations
    fifo_op: coverpoint {wr_en, rd_en} {
      bins no_op       = {2'b00};
      bins write_only  = {2'b10};
      bins read_only   = {2'b01};
      bins read_write  = {2'b11};
    }
    
    // Cover FIFO states
    fifo_state: coverpoint {full, empty} {
      bins empty_fifo     = {2'b01};
      bins full_fifo      = {2'b10};
      bins normal_fifo    = {2'b00};
      illegal_bins illegal = {2'b11}; // Should never happen
    }
    
    // Cover FIFO levels
    fifo_level_cp: coverpoint fifo_level {
      bins empty      = {0};
      bins almost_empty = {[1:2]};
      bins mid_level  = {[3:DEPTH-3]};
      bins almost_full = {[DEPTH-2:DEPTH-1]};
      bins full       = {DEPTH};
    }
    
    // Cover input data patterns
    data_pattern: coverpoint wr_data {
      bins zeros     = {8'h00};
      bins ones      = {8'hFF};
      bins alternating_1 = {8'hAA};
      bins alternating_2 = {8'h55};
      bins random    = default;
    }
    
    // Cross coverage between operations and FIFO state
    op_state_cross: cross fifo_op, fifo_state {
      // Can't write to a full FIFO
      ignore_bins full_write = binsof(fifo_state) intersect {2'b10} && 
                               binsof(fifo_op) intersect {2'b10, 2'b11};
      
      // Can't read from an empty FIFO
      ignore_bins empty_read = binsof(fifo_state) intersect {2'b01} && 
                              binsof(fifo_op) intersect {2'b01, 2'b11};
    }
    
    // Cross coverage between operations and FIFO level
    op_level_cross: cross fifo_op, fifo_level_cp;
  endgroup
  
  // Create an instance of the coverage group
  fifo_cg cg_inst;
  
  // Stimulus generation task
  task automatic apply_random_stimulus(int num_cycles);
    for (int i = 0; i < num_cycles; i++) begin
      // Randomly decide whether to read or write
      wr_en = $urandom_range(0, 1);
      rd_en = $urandom_range(0, 1);
      
      // Don't attempt to write when full or read when empty
      if (full) wr_en = 0;
      if (empty) rd_en = 0;
      
      // Generate random data if writing
      if (wr_en)
        wr_data = $urandom;
      
      @(posedge clk);
    end
  endtask
  
  // Targeted stimulus tasks (separate tasks instead of using $coverage_get)
  
  // Target FIFO full condition
  task automatic target_full_condition();
    if (!tested_full) begin
      $display("Targeting FIFO full condition");
      wr_en = 1;
      rd_en = 0;
      
      // Write until full
      while (!full) begin
        wr_data = $urandom;
        @(posedge clk);
      end
      
      // Try a few more writes when full (should be ignored)
      for (int i = 0; i < 3; i++) begin
        wr_en = 1;
        wr_data = $urandom;
        @(posedge clk);
      end
      
      tested_full = 1;
    end
  endtask
  
  // Target almost full to empty scenario
  task automatic target_almost_full_to_empty();
    if (!tested_almost_full_to_empty) begin
      $display("Targeting almost full to empty transition");
      // Fill to almost full
      wr_en = 1;
      rd_en = 0;
      while (fifo_level < DEPTH-2) begin
        wr_data = $urandom;
        @(posedge clk);
      end
      
      // Then drain
      wr_en = 0;
      rd_en = 1;
      while (!empty) begin
        @(posedge clk);
      end
      
      tested_almost_full_to_empty = 1;
    end
  endtask
  
  // Target specific data patterns
  task automatic target_data_patterns();
    if (!tested_alternating_pattern) begin
      $display("Targeting alternating data pattern");
      wr_en = 1;
      rd_en = 0;
      wr_data = 8'hAA;
      @(posedge clk);
      wr_data = 8'h55;
      @(posedge clk);
      
      tested_alternating_pattern = 1;
    end
  endtask
  
  // Target simultaneous read/write at mid level
  task automatic target_simultaneous_rw_mid_level();
    if (!tested_simultaneous_rw) begin
      $display("Targeting simultaneous read/write at mid level");
      // Fill to mid level
      wr_en = 1;
      rd_en = 0;
      while (fifo_level < DEPTH/2) begin
        wr_data = $urandom;
        @(posedge clk);
      end
      
      // Perform simultaneous reads and writes
      for (int i = 0; i < 5; i++) begin
        wr_en = 1;
        rd_en = 1;
        wr_data = $urandom;
        @(posedge clk);
      end
      
      tested_simultaneous_rw = 1;
    end
  endtask
  
  // Main test flow
  initial begin
    // Initialize
    clk = 0;
    rst_n = 0;
    wr_en = 0;
    rd_en = 0;
    wr_data = 0;
    
    // Create coverage group instance
    cg_inst = new();
    
    // Reset
    #20 rst_n = 1;
    
    // Phase 1: Initial random stimulus
    $display("Phase 1: Random stimulus");
    apply_random_stimulus(100);
    
    // Report initial coverage
    $display("Initial Coverage: %0.2f%%", $get_coverage());
    
    // Phase 2: Targeted stimulus - run all targeted tests
    $display("Phase 2: Targeted stimulus");
    target_full_condition();
    target_almost_full_to_empty();
    target_data_patterns();
    target_simultaneous_rw_mid_level();
    
    // Phase 3: Final random stimulus
    $display("Phase 3: Additional random stimulus");
    apply_random_stimulus(50);
    
    // Final coverage report
    $display("Final Coverage: %0.2f%%", $get_coverage());
    
    // End simulation
    #20 $finish;
  end
  
  // Monitor
  initial begin
    $monitor("Time=%0t: wr_en=%b, rd_en=%b, wr_data=%h, rd_data=%h, full=%b, empty=%b, level=%0d", 
             $time, wr_en, rd_en, wr_data, rd_data, full, empty, fifo_level);
  end
endmodule