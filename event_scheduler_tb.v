`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 08.03.2025 15:48:26
// Design Name: 
// Module Name: event_scheduler_tb
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


module event_scheduler_tb();
    reg clk, rst, event_a, event_b;
    wire task_1_active, task_2_active, task_3_active;
    
    // Instantiate the event scheduler
    event_scheduler uut (
        .clk(clk),
        .rst(rst),
        .event_a(event_a),
        .event_b(event_b),
        .task_1_active(task_1_active),
        .task_2_active(task_2_active),
        .task_3_active(task_3_active)
    );
    
    // Clock generation
    always #5 clk = ~clk;
    
    // Monitor signals
    initial begin
        $monitor("Time=%0dns: Events(A=%b, B=%b) Tasks(T1=%b, T2=%b, T3=%b)", 
                 $time, event_a, event_b, task_1_active, task_2_active, task_3_active);
    end
    
    // Test sequence
    initial begin
        $display("Starting Event Scheduler Test");
        clk = 0;
        rst = 1;
        event_a = 0;
        event_b = 0;
        
        // Release reset
        #10 rst = 0;
        
        // Test event_a positive edge
        #10 event_a = 1;
        #20 event_a = 0;
        
        // Test event_b negative edge
        #10 event_b = 1;
        #20 event_b = 0;
        
        // Test both events high
        #10 event_a = 1;
            event_b = 1;
        #20 event_a = 0;
            event_b = 0;
            
        // Run a bit longer
        #20;
        
        $display("Test Complete");
        $finish;
    end
    
endmodule