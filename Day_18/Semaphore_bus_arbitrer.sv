`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11.03.2025 18:01:10
// Design Name: 
// Module Name: Semaphore_bus_arbitrer
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


// Synthesizable bus arbiter
module bus_arbiter_18 #(
  parameter NUM_MASTERS = 4
)(
  input  logic                  clk,
  input  logic                  rst_n,
  input  logic [NUM_MASTERS-1:0] request,
  output logic [NUM_MASTERS-1:0] grant
);

  // Priority encoder for arbitration (fixed priority)
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      grant <= '0;
    end else begin
      grant <= '0; // Default - no grants
      
      // Fixed priority arbitration
      for (int i = 0; i < NUM_MASTERS; i++) begin
        if (request[i]) begin
          grant <= '0;
          grant[i] <= 1'b1;
          break; // Grant to the highest priority master
        end
      end
    end
  end

endmodule

// Testbench for bus arbiter using semaphores
`timescale 1ns/1ps

module bus_arbiter_18_tb();
  // Parameters
  parameter NUM_MASTERS = 4;
  
  // DUT signals
  logic                  clk = 0;
  logic                  rst_n;
  logic [NUM_MASTERS-1:0] request;
  logic [NUM_MASTERS-1:0] grant;
  
  // Semaphore to model the shared bus
  semaphore bus_sem = new(1); // Only one master can use the bus at a time
  
  // Instantiate DUT
  bus_arbiter_18 #(
    .NUM_MASTERS(NUM_MASTERS)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .request(request),
    .grant(grant)
  );
  
  // Clock generation
  always #5 clk = ~clk;
  
  // Master model task
  task automatic master(input int id);
    // Local variables
    int num_transactions = $urandom_range(5, 15);
    int idle_cycles;
    
    $display("[%0t] Master %0d: Starting - will perform %0d transactions", 
             $time, id, num_transactions);
    
    repeat (num_transactions) begin
      // Wait some idle time
      idle_cycles = $urandom_range(5, 20);
      repeat (idle_cycles) @(posedge clk);
      
      // Request the bus
      $display("[%0t] Master %0d: Requesting bus", $time, id);
      request[id] = 1'b1;
      
      // Wait for grant
      while (!grant[id]) @(posedge clk);
      
      // Get the bus semaphore
      bus_sem.get(1);
      $display("[%0t] Master %0d: Got bus grant, starting transaction", $time, id);
      
      // Perform the bus transaction
      repeat ($urandom_range(3, 10)) @(posedge clk);
      
      // Release the bus
      request[id] = 1'b0;
      $display("[%0t] Master %0d: Finished transaction, releasing bus", $time, id);
      bus_sem.put(1);
      
      // Wait for grant to be deasserted
      while (grant[id]) @(posedge clk);
    end
    
    $display("[%0t] Master %0d: Completed all transactions", $time, id);
  endtask
  
  // Monitor task
  task bus_monitor();
    forever begin
      @(posedge clk);
      if (|grant) begin
        // Check that only one grant is active at a time
        if ($countones(grant) != 1)
          $error("[%0t] ERROR: Multiple grants active simultaneously: %b", $time, grant);
          
        // Check that the granted master has an active request
        for (int i = 0; i < NUM_MASTERS; i++) begin
          if (grant[i] && !request[i])
            $error("[%0t] ERROR: Master %0d granted without request", $time, i);
        end
      end
    end
  endtask
  
  // Main test sequence
  initial begin
    // Initialize
    request = '0;
    rst_n = 0;
    
    repeat(5) @(posedge clk);
    rst_n = 1;
    
    fork
      master(0);
      master(1);
      master(2);
      master(3);
      bus_monitor();
    join_any
    
    // Let remaining masters finish
    #500;
    $display("[%0t] Test complete", $time);
    $finish;
  end
  
  // Watchdog timer
  initial begin
    #5000;
    $display("[%0t] Watchdog timeout - finishing simulation", $time);
    $finish;
  end
  
  // Coverage
  covergroup arbiter_cov @(posedge clk);
    request_cp: coverpoint request;
    grant_cp: coverpoint grant;
    master_pairs: cross request_cp, grant_cp;
  endgroup
  
  arbiter_cov cov = new();
  
endmodule
