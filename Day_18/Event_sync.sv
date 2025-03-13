`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11.03.2025 17:50:39
// Design Name: 
// Module Name: Event_sync
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

module event_sync_tb;
  
  // Define events
  event data_ready;       // Data is ready for processing
  event processing_done;  // Processing completed
  event verification_done;// Verification completed
  
  // Shared data
  int data_value;
  int processed_value;
  
  // Producer task
  task automatic producer();
    for (int i = 0; i < 5; i++) begin
      #20; // Simulate production time
      
      // Generate data
      data_value = i * 10 + 5;
      $display("[Producer] Time=%0t: Data produced = %0d", $time, data_value);
      
      // Trigger data_ready event
      ->data_ready;
      
      // Wait for processing to complete
      $display("[Producer] Time=%0t: Waiting for processing to complete", $time);
      @processing_done;
      $display("[Producer] Time=%0t: Processing is complete", $time);
    end
  endtask
  
  // Processor task
  task automatic processor();
    forever begin
      // Wait for data_ready event
      $display("[Processor] Time=%0t: Waiting for data", $time);
      @data_ready;
      
      // Process the data
      #15; // Simulate processing time
      processed_value = data_value * 2;
      $display("[Processor] Time=%0t: Processed data %0d -> %0d", 
               $time, data_value, processed_value);
      
      // Signal processing complete
      ->processing_done;
      
      // Wait for verification to complete
      $display("[Processor] Time=%0t: Waiting for verification", $time);
      @verification_done;
      $display("[Processor] Time=%0t: Verification is complete", $time);
    end
  endtask
  
  // Verifier task
  task automatic verifier();
    forever begin
      // Wait for processing_done event
      @processing_done;
      
      // Verify the result
      #10; // Simulate verification time
      
      if (processed_value == data_value * 2) begin
        $display("[Verifier] Time=%0t: Verification PASSED: %0d == %0d * 2", 
                 $time, processed_value, data_value);
      end else begin
        $display("[Verifier] Time=%0t: Verification FAILED: %0d != %0d * 2", 
                 $time, processed_value, data_value);
      end
      
      // Signal verification complete
      ->verification_done;
    end
  endtask
  
  // Test sequence
  initial begin
    // Start the processes
    fork
      producer();
      processor();
      verifier();
    join_any
    
    // Allow some time for operations to complete
    #20;
    
    // End simulation
    $finish;
  end
  
endmodule