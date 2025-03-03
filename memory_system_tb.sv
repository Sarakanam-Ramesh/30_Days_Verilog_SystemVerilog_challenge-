`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 02.03.2025 11:56:25
// Design Name: 
// Module Name: memory_system_tb
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

module memory_system_tb;
    // Clock and reset
    logic clk;
    logic rst_n;
    
    // Host interface signals
    logic        host_req;
    logic        host_wr_en;
    logic [15:0] host_addr;
    logic [31:0] host_wdata;
    logic [31:0] host_rdata;
    logic        host_ack;
    
    // Instantiate DUT
    memory_system dut (
        .clk(clk),
        .rst_n(rst_n),
        .host_req(host_req),
        .host_wr_en(host_wr_en),
        .host_addr(host_addr),
        .host_wdata(host_wdata),
        .host_rdata(host_rdata),
        .host_ack(host_ack)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 100MHz clock
    end
    
    // Transaction tracker
    int num_transactions = 0;
    int num_successful = 0;
    
            // Memory transaction task
        task automatic memory_op(input bit is_write, input [15:0] address, 
                                input [31:0] write_data, output [31:0] read_data);
            num_transactions++;
            
            host_req = 1'b1;
            host_wr_en = is_write;
            host_addr = address;
            host_wdata = write_data;
            
            @(posedge host_ack);
            read_data = host_rdata;
            @(posedge clk);
            host_req = 1'b0;
            @(posedge clk);
        endtask
    
    // Test stimulus
    initial begin
        // Initialize signals
        rst_n = 0;
        host_req = 0;
        host_wr_en = 0;
        host_addr = 0;
        host_wdata = 0;
        
        // Apply reset
        #20 rst_n = 1;
        #10;
        
        
        // Test Case 1: Read Initial Values
        $display("\nTest Case 1: Read Initial Values");
        for (int i = 0; i < 10; i++) begin
            logic [31:0] rd_data;
            memory_op(0, i<<2, 0, rd_data);
            
            if (rd_data === i) begin
                $display("Address 0x%h: Read Success: %h", i<<2, rd_data);
                num_successful++;
            end else begin
                $display("Address 0x%h: Read FAILED. Expected: %h, Got: %h", i<<2, i, rd_data);
            end
        end
        
        // Test Case 2: Write and Read Back
        $display("\nTest Case 2: Write and Read Back");
        for (int i = 0; i < 10; i++) begin
            logic [31:0] wr_data = 32'h55AA0000 | i;
            logic [31:0] rd_data;
            
            // Write operation
            memory_op(1, (i+100)<<2, wr_data, rd_data);
            
            // Read back to verify
            memory_op(0, (i+100)<<2, 0, rd_data);
            
            if (rd_data === wr_data) begin
                $display("Address 0x%h: Write/Read Success: %h", (i+100)<<2, rd_data);
                num_successful++;
            end else begin
                $display("Address 0x%h: Write/Read FAILED. Expected: %h, Got: %h", (i+100)<<2, wr_data, rd_data);
            end
        end
        
        // Test Case 3: Random Access Pattern
        $display("\nTest Case 3: Random Access Pattern");
        for (int i = 0; i < 20; i++) begin
            logic [15:0] addr = $urandom % 1024;
            logic [31:0] wr_data = $urandom;
            logic [31:0] rd_data;
            
            // Write random data
            memory_op(1, addr, wr_data, rd_data);
            
            // Read back
            memory_op(0, addr, 0, rd_data);
            
            if (rd_data === wr_data) begin
                $display("Random Address 0x%h: Write/Read Success: %h", addr, rd_data);
                num_successful++;
            end else begin
                $display("Random Address 0x%h: Write/Read FAILED. Expected: %h, Got: %h", addr, wr_data, rd_data);
            end
        end
        
        // Test summary
        $display("\nTest Summary:");
        $display("Total transactions: %0d", num_transactions);
        $display("Successful transactions: %0d", num_successful);
        $display("Success rate: %0.2f%%", (num_successful * 100.0) / num_transactions);
        
        // End simulation
        #50;
        $display("Simulation complete");
        $finish;
    end
    
endmodule
