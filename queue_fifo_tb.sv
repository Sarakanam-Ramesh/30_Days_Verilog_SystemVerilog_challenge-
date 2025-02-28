`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 27.02.2025 21:44:36
// Design Name: 
// Module Name: queue_fifo_tb
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


module queue_fifo_tb;
    // Parameters
    parameter WIDTH = 8;
    parameter MAX_DEPTH = 32;
    
    // Testbench signals
    logic clk;
    logic reset;
    logic push;
    logic pop;
    logic [WIDTH-1:0] data_in;
    logic [WIDTH-1:0] data_out;
    logic empty;
    logic full;
    logic [$clog2(MAX_DEPTH+1)-1:0] count;
    
    // Instantiate the queue FIFO module
    queue_fifo #(
        .WIDTH(WIDTH),
        .MAX_DEPTH(MAX_DEPTH)
    ) dut (
        .clk(clk),
        .reset(reset),
        .push(push),
        .pop(pop),
        .data_in(data_in),
        .data_out(data_out),
        .empty(empty),
        .full(full),
        .count(count)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 10ns period clock
    end
    
    // Test sequence
    initial begin
        // Initialize signals
        reset = 1;
        push = 0;
        pop = 0;
        data_in = 0;
        
        // Apply reset
        #20;
        reset = 0;
        #10;
        
        // Push data into the queue
        $display("Pushing data into queue...");
        for (int i = 1; i <= 10; i++) begin
            push = 1;
            data_in = i * 10;
            #10;
        end
        push = 0;
        
        $display("Queue count after push: %d", count);
        
        // Pop data from the queue
        $display("Popping data from queue...");
        for (int i = 0; i < 5; i++) begin
            pop = 1;
            #10;
            $display("Popped data: %h", data_out);
        end
        pop = 0;
        
        $display("Queue count after pop: %d", count);
        
        // Push and pop simultaneously
        $display("Pushing and popping simultaneously...");
        for (int i = 11; i <= 15; i++) begin
            push = 1;
            pop = 1;
            data_in = i * 10;
            #10;
            $display("Popped data: %h, Pushed data: %h", data_out, data_in);
        end
        
        push = 0;
        pop = 0;
        
        // Pop remaining data
        $display("Popping remaining data...");
        pop = 1;
        while (!empty) begin
            #10;
            $display("Popped data: %h", data_out);
        end
        pop = 0;
        
        // Push until full
        $display("Pushing until full...");
        push = 1;
        for (int i = 1; i <= MAX_DEPTH + 5; i++) begin
            data_in = i;
            #10;
            if (full) begin
                $display("Queue became full at i = %d", i);
                break;
            end
        end
        
        // End simulation
        #10;
        $finish;
    end
    
    // Monitor changes
    initial begin
        $monitor("Time: %0t, Reset: %b, Push: %b, Pop: %b, DataIn: %h, DataOut: %h, Empty: %b, Full: %b, Count: %d",
                 $time, reset, push, pop, data_in, data_out, empty, full, count);
    end
endmodule