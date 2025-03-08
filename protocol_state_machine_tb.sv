`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 03.03.2025 19:26:22
// Design Name: 
// Module Name: protocol_state_machine_tb
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


module protocol_state_machine_tb;
    // Signals
    logic clk;
    logic rst_n;
    logic req;
    logic [7:0] data_in;
    logic ack;
    logic ready;
    logic [7:0] data_out;
    
    // Instantiate the DUT
    protocol_state_machine dut (
        .clk(clk),
        .rst_n(rst_n),
        .req(req),
        .data_in(data_in),
        .ack(ack),
        .ready(ready),
        .data_out(data_out)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 10ns period
    end
    
    // Task to perform a single transaction
    task perform_transaction(input [7:0] data);
        // Wait until ready
        wait(ready);
        
        // Set data and assert request
        @(posedge clk);
        data_in = data;
        req = 1'b1;
        
        // Wait for acknowledge
        wait(ack);
        
        // Keep request high for a while
        repeat(2) @(posedge clk);
        
        // Deassert request
        req = 1'b0;
        
        // Wait a bit
        repeat(2) @(posedge clk);
    endtask
    
    // Test sequence
    initial begin
        $display("Time\tReset\tReq\tData_in\tAck\tReady\tData_out\tState");
        $monitor("%0t\t%b\t%b\t%h\t%b\t%b\t%h", 
                 $time, rst_n, req, data_in, ack, ready, data_out);
        
        // Initialize inputs
        rst_n = 0;
        req = 0;
        data_in = 8'h00;
        
        // Reset sequence
        repeat(2) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
        
        // Test several transactions
        perform_transaction(8'hA5);
        perform_transaction(8'h3C);
        perform_transaction(8'hFF);
        perform_transaction(8'h00);
        
        // Test back-to-back transactions
        wait(ready);
        
        @(posedge clk);
        data_in = 8'h55;
        req = 1'b1;
        
        wait(ack);
        @(posedge clk);
        data_in = 8'hAA;
        
        repeat(2) @(posedge clk);
        req = 1'b0;
        
        repeat(5) @(posedge clk);
        
        $display("Simulation complete");
        $finish;
    end
endmodule
