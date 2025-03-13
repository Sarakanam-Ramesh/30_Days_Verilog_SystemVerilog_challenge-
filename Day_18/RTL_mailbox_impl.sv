`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11.03.2025 14:57:08
// Design Name: 
// Module Name: RTL_mailbox_impl
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


module mailbox_rtl_18 #(
  parameter DATA_WIDTH = 32,
  parameter DEPTH = 8
) (
  input  logic                   clk,
  input  logic                   rst_n,
  
  // Producer interface
  input  logic                   put_valid,
  input  logic [DATA_WIDTH-1:0]  put_data,
  output logic                   put_ready,
  
  // Consumer interface
  input  logic                   get_valid,
  output logic [DATA_WIDTH-1:0]  get_data,
  output logic                   get_ready
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
  
  // FIFO memory and pointers
  logic [DATA_WIDTH-1:0] mem [DEPTH-1:0];
  logic [ADDR_WIDTH:0]   wr_ptr;
  logic [ADDR_WIDTH:0]   rd_ptr;
  
  // Status flags
  logic                  empty;
  logic                  full;
  logic [ADDR_WIDTH:0]   count;
  
  // Empty and full conditions
  assign empty = (wr_ptr == rd_ptr);
  assign full  = (wr_ptr[ADDR_WIDTH-1:0] == rd_ptr[ADDR_WIDTH-1:0]) && 
                 (wr_ptr[ADDR_WIDTH] != rd_ptr[ADDR_WIDTH]);
  
  // Interface signals
  assign put_ready = !full;
  assign get_ready = !empty;
  assign get_data  = empty ? '0 : mem[rd_ptr[ADDR_WIDTH-1:0]];
  
  // Number of items in the mailbox
  assign count = wr_ptr - rd_ptr;
  
  // Write operation
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      wr_ptr <= '0;
    end else if (put_valid && put_ready) begin
      mem[wr_ptr[ADDR_WIDTH-1:0]] <= put_data;
      wr_ptr <= wr_ptr + 1'b1;
    end
  end
  
  // Read operation
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      rd_ptr <= '0;
    end else if (get_valid && get_ready) begin
      rd_ptr <= rd_ptr + 1'b1;
    end
  end
  
endmodule

`timescale 1ns/1ps

module mailbox_rtl_18_tb;
  // Parameters
  parameter DATA_WIDTH = 32;
  parameter DEPTH = 8;
  parameter CLK_PERIOD = 10; // 10ns clock period (100MHz)
  
  // Clock and reset signals
  logic clk;
  logic rst_n;
  
  // Producer interface
  logic                  put_valid;
  logic [DATA_WIDTH-1:0] put_data;
  logic                  put_ready;
  
  // Consumer interface
  logic                  get_valid;
  logic [DATA_WIDTH-1:0] get_data;
  logic                  get_ready;
  
  // Mailbox to store expected values
  logic [DATA_WIDTH-1:0] expected_data[$];
  
  // Instantiate the DUT (Device Under Test)
  mailbox_rtl_18 #(
    .DATA_WIDTH(DATA_WIDTH),
    .DEPTH(DEPTH)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .put_valid(put_valid),
    .put_data(put_data),
    .put_ready(put_ready),
    .get_valid(get_valid),
    .get_data(get_data),
    .get_ready(get_ready)
  );
  
  // Clock generation
  initial begin
    clk = 0;
    forever #(CLK_PERIOD/2) clk = ~clk;
  end
  
  // Counters and test variables
  int put_count = 0;
  int get_count = 0;
  int error_count = 0;
  bit test_done = 0;
  
  // Task to reset the DUT
  task reset();
    $display("[%0t] Applying reset", $time);
    rst_n = 0;
    put_valid = 0;
    put_data = 0;
    get_valid = 0;
    repeat(3) @(posedge clk);
    rst_n = 1;
    repeat(2) @(posedge clk);
    $display("[%0t] Reset complete", $time);
  endtask
  
  // Task to put data into the mailbox
  task put_item(input logic [DATA_WIDTH-1:0] data);
    @(posedge clk);
    while (!put_ready) @(posedge clk); // Wait until ready
    put_valid = 1;
    put_data = data;
    @(posedge clk);
    put_valid = 0;
    put_count++;
    expected_data.push_back(data);
    $display("[%0t] Put data: 0x%h", $time, data);
  endtask
  
  // Task to get data from the mailbox
  task get_item();
    logic [DATA_WIDTH-1:0] exp_data;
    @(posedge clk);
    while (!get_ready) @(posedge clk); // Wait until ready
    get_valid = 1;
    @(posedge clk);
    if (expected_data.size() > 0) begin
      exp_data = expected_data.pop_front();
      if (get_data !== exp_data) begin
        $display("[%0t] ERROR: Data mismatch! Expected: 0x%h, Got: 0x%h", $time, exp_data, get_data);
        error_count++;
      end else begin
        $display("[%0t] Got data: 0x%h (correct)", $time, get_data);
      end
    end
    get_valid = 0;
    get_count++;
  endtask
  
  // Task to fill the mailbox completely
  task fill_mailbox();
    $display("[%0t] Filling mailbox to capacity", $time);
    for (int i = 0; i < DEPTH; i++) begin
      logic [DATA_WIDTH-1:0] data = $urandom;
      put_item(data);
      // Verify put_ready is deasserted when full
      if (i == DEPTH-1) begin
        if (put_ready) begin
          $display("[%0t] ERROR: put_ready still asserted when mailbox should be full!", $time);
          error_count++;
        end else begin
          $display("[%0t] Correctly detected full mailbox", $time);
        end
      end
    end
  endtask
  
  // Task to empty the mailbox completely
  task empty_mailbox();
    $display("[%0t] Emptying mailbox", $time);
    // Continue until mailbox is empty
    while (expected_data.size() > 0) begin
      get_item();
    end
    // Verify get_ready is deasserted when empty
    if (get_ready) begin
      $display("[%0t] ERROR: get_ready still asserted when mailbox should be empty!", $time);
      error_count++;
    end else begin
      $display("[%0t] Correctly detected empty mailbox", $time);
    end
  endtask
  
  // Test random operations
  task test_random_operations(int num_operations);
    $display("[%0t] Performing %0d random operations", $time, num_operations);
    for (int i = 0; i < num_operations; i++) begin
      bit operation = $urandom % 2; // 0: put, 1: get
      
      if (operation == 0 || expected_data.size() == 0) begin
        // If we chose put or the queue is empty, do a put operation
        if (put_ready) begin
          logic [DATA_WIDTH-1:0] data = $urandom;
          put_item(data);
        end
      end else begin
        // Otherwise do a get operation
        if (get_ready) begin
          get_item();
        end
      end
    end
  endtask
  
  // Main test sequence
  initial begin
    $display("Starting mailbox_rtl testbench");
    
    // Initialize signals
    rst_n = 1;
    put_valid = 0;
    put_data = 0;
    get_valid = 0;
    
    // Apply reset
    reset();
    
    // Test 1: Basic put/get operation
    $display("\n=== Test 1: Basic put/get operation ===");
    put_item(32'hA5A5A5A5);
    get_item();
    
    // Test 2: Fill and empty the mailbox
    $display("\n=== Test 2: Fill and empty the mailbox ===");
    fill_mailbox();
    empty_mailbox();
    
    // Test 3: Alternating put/get
    $display("\n=== Test 3: Alternating put/get ===");
    for (int i = 0; i < 20; i++) begin
      put_item(32'h12345670 + i);
      get_item();
    end
    
    // Test 4: Random operations
    $display("\n=== Test 4: Random operations ===");
    test_random_operations(100);
    
    // Make sure we've emptied the mailbox
    while (expected_data.size() > 0) begin
      get_item();
    end
    
    // Test 5: Underflow test
    $display("\n=== Test 5: Underflow test ===");
    reset();
    if (get_ready) begin
      $display("[%0t] ERROR: get_ready asserted after reset!", $time);
      error_count++;
    end
    
    // Test 6: Overflow test
    $display("\n=== Test 6: Overflow test ===");
    fill_mailbox();
    if (put_ready) begin
      $display("[%0t] ERROR: put_ready asserted when mailbox is full!", $time);
      error_count++;
    end
    
    // Test 7: Mixed depth test (partial fill/empty)
    $display("\n=== Test 7: Mixed depth test ===");
    // Empty half the mailbox
    repeat(DEPTH/2) get_item();
    // Refill
    repeat(DEPTH/2) put_item($urandom);
    // Empty all
    empty_mailbox();
    
    // Test complete
    test_done = 1;
    
    // Report results
    $display("\n=== Test Results ===");
    $display("Put operations: %0d", put_count);
    $display("Get operations: %0d", get_count);
    $display("Errors: %0d", error_count);
    
    if (error_count == 0) begin
      $display("TEST PASSED");
    end else begin
      $display("TEST FAILED with %0d errors", error_count);
    end
    
    $finish;
  end
  
  // Coverage and assertions
  covergroup mailbox_cov @(posedge clk);
    empty_cp: coverpoint get_ready {
      bins empty = {0};
      bins not_empty = {1};
    }
    
    full_cp: coverpoint put_ready {
      bins full = {0};
      bins not_full = {1};
    }
    
    put_op_cp: coverpoint put_valid && put_ready {
      bins put_operation = {1};
    }
    
    get_op_cp: coverpoint get_valid && get_ready {
      bins get_operation = {1};
    }
    
    // Cross coverage
    ops_cross: cross put_op_cp, get_op_cp;
  endgroup
  
  mailbox_cov cov_inst = new();
  
  // Assertions for protocol checking
  property reset_clears_ptrs;
    @(posedge clk) $fell(rst_n) |=> !get_ready;
  endproperty
  
  property full_no_put_ready;
    @(posedge clk) $rose(dut.full) |-> !put_ready;
  endproperty
  
  property empty_no_get_ready;
    @(posedge clk) $rose(dut.empty) |-> !get_ready;
  endproperty
  
  assert property (reset_clears_ptrs)
    else $error("Reset did not clear pointers!");
    
  assert property (full_no_put_ready)
    else $error("put_ready still asserted when full!");
    
  assert property (empty_no_get_ready)
    else $error("get_ready still asserted when empty!");
  
  // Timeout watchdog
  initial begin
    repeat(10000) @(posedge clk);
    if (!test_done) begin
      $display("[%0t] ERROR: Test timed out!", $time);
      $finish;
    end
  end
endmodule