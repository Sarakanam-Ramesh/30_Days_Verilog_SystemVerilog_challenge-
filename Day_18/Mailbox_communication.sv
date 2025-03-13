`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11.03.2025 14:53:58
// Design Name: 
// Module Name: Mailbox_communication
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
class Transaction;
  rand bit [7:0] data;
  rand bit [3:0] addr;
  bit [7:0] response;
  
  function void display(string tag="");
    $display("[%s] Time=%0t: addr=0x%h, data=0x%h, response=0x%h", 
             tag, $time, addr, data, response);
  endfunction
endclass

// Testbench module
module mailbox_tb;
  
  // Mailboxes for communication
  mailbox #(Transaction) gen2drv = new(5);  // Generator to Driver
  mailbox #(Transaction) drv2mon = new(5);  // Driver to Monitor
  
  // Generator process
  task generator(int num_transactions);
    Transaction tx;
    
    for (int i = 0; i < num_transactions; i++) begin
      tx = new();
      assert(tx.randomize());
      
      $display("[GEN] Time=%0t: Generated transaction %0d: addr=0x%h, data=0x%h", 
              $time, i, tx.addr, tx.data);
              
      gen2drv.put(tx);
      #10;
    end
  endtask
  
  // Driver process
  task driver();
    Transaction tx;
    
    forever begin
      gen2drv.get(tx);
      
      // Simulate DUT interaction
      // In a real testbench, this would interface with a DUT
      #20; // Processing time
      
      // Create a response (simple transformation in this example)
      tx.response = tx.data + 8'h11;
      
      $display("[DRV] Time=%0t: Processed transaction: addr=0x%h, data=0x%h, response=0x%h", 
              $time, tx.addr, tx.data, tx.response);
              
      drv2mon.put(tx);
    end
  endtask
  
  // Monitor process
  task monitor();
    Transaction tx;
    
    forever begin
      drv2mon.get(tx);
      
      tx.display("MON");
      
      // Could include checking/scoreboarding here
    end
  endtask
  
  // Test sequence
  initial begin
    // Start the processes
    fork
      generator(10); // Generate 10 transactions
      driver();
      monitor();
    join_any
    
    // Wait for remaining transactions to flush through
    #100;
    
    // End simulation
    $finish;
  end
  
endmodule
