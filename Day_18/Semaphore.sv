`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11.03.2025 17:49:35
// Design Name: 
// Module Name: Semaphore
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

module semaphore_tb;
  
  // Shared resource semaphore
  semaphore shared_resource = new(1); // Only 1 process can access at a time
  
  // Shared memory (simulated)
  int shared_memory[10];
  
  // Process 1 - Writer
  task automatic writer(int id, int start_addr, int num_writes);
    $display("[Writer %0d] Time=%0t: Starting, requesting resource", id, $time);
    
    shared_resource.get(1); // Get one key
    $display("[Writer %0d] Time=%0t: Got access to shared resource", id, $time);
    
    for (int i = 0; i < num_writes; i++) begin
      shared_memory[start_addr + i] = id * 100 + i;
      $display("[Writer %0d] Time=%0t: Writing addr=%0d, data=%0d", 
               id, $time, start_addr + i, shared_memory[start_addr + i]);
      #10; // Simulate processing time
    end
    
    shared_resource.put(1); // Release the key
    $display("[Writer %0d] Time=%0t: Released shared resource", id, $time);
  endtask
  
  // Process 2 - Reader
  task automatic reader(int id, int start_addr, int num_reads);
    $display("[Reader %0d] Time=%0t: Starting, requesting resource", id, $time);
    
    shared_resource.get(1); // Get one key
    $display("[Reader %0d] Time=%0t: Got access to shared resource", id, $time);
    
    for (int i = 0; i < num_reads; i++) begin
      $display("[Reader %0d] Time=%0t: Reading addr=%0d, data=%0d", 
               id, $time, start_addr + i, shared_memory[start_addr + i]);
      #5; // Simulate processing time
    end
    
    shared_resource.put(1); // Release the key
    $display("[Reader %0d] Time=%0t: Released shared resource", id, $time);
  endtask
  
  // Test sequence
  initial begin
    // Initialize memory
    for (int i = 0; i < 10; i++) begin
      shared_memory[i] = 0;
    end
    
    // Create multiple parallel processes to demonstrate semaphore
    fork
      writer(1, 0, 3);  // Writer 1: write to addr 0-2
      #5 reader(1, 0, 5);  // Reader 1: read from addr 0-4
      #10 writer(2, 5, 3);  // Writer 2: write to addr 5-7
      #15 reader(2, 3, 5);  // Reader 2: read from addr 3-7
    join
    
    // Display final memory state
    $display("Final memory state:");
    for (int i = 0; i < 10; i++) begin
      $display("Memory[%0d] = %0d", i, shared_memory[i]);
    end
    
    // End simulation
    $finish;
  end
  
endmodule
