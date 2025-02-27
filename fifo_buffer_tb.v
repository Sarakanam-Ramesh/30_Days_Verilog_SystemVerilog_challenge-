`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// Create Date: 27.02.2025 21:12:20
// Design Name: 
// Module Name: fifo_buffer_tb
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// Dependencies: 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
//////////////////////////////////////////////////////////////////////////////////
module fifo_buffer_tb;
    // Parameters
    parameter WIDTH = 8;
    parameter DEPTH = 16;
    
    // Testbench signals
    reg clk;
    reg reset;
    reg write_en;
    reg read_en;
    reg [WIDTH-1:0] data_in;
    wire [WIDTH-1:0] data_out;
    wire empty;
    wire full;
    
    // Instantiate the FIFO buffer module
    fifo_buffer #(
        .WIDTH(WIDTH),
        .DEPTH(DEPTH)
    ) dut (
        .clk(clk),
        .reset(reset),
        .write_en(write_en),
        .read_en(read_en),
        .data_in(data_in),
        .data_out(data_out),
        .empty(empty),
        .full(full)
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
        write_en = 0;
        read_en = 0;
        data_in = 0;
        
        // Apply reset
        #20;
        reset = 0;
        #10;
        
        // Write data to FIFO
        $display("Writing to FIFO...");
        write_en = 1;
        read_en = 0;
        
        // Write 5 data values
        data_in = 8'hA1; #10;
        data_in = 8'hB2; #10;
        data_in = 8'hC3; #10;
        data_in = 8'hD4; #10;
        data_in = 8'hE5; #10;
        
        write_en = 0;
        #10;
        
        // Read data from FIFO
        $display("Reading from FIFO...");
        write_en = 0;
        read_en = 1;
        
        // Read 3 values
        #10; $display("Read data: %h", data_out);
        #10; $display("Read data: %h", data_out);
        #10; $display("Read data: %h", data_out);
        
        // Write and read simultaneously
        $display("Simultaneous write and read...");
        write_en = 1;
        read_en = 1;
        
        data_in = 8'hF6; #10;
        data_in = 8'h78; #10;
        
        // Stop operations
        write_en = 0;
        read_en = 0;
        #10;
        
        // Read remaining data
        $display("Reading remaining data...");
        read_en = 1;
        #10; $display("Read data: %h", data_out);
        #10; $display("Read data: %h", data_out);
        #10; $display("Read data: %h", data_out);
        #10; $display("Read data: %h", data_out);
        
        // Test empty condition
        $display("Testing empty condition...");
        #10; 
        if (empty) $display("FIFO is empty.");
        
        // Test full condition
        $display("Testing full condition...");
        write_en = 1;
        read_en = 0;
        
        // Try to fill the FIFO
        for (integer i = 0; i < DEPTH; i = i + 1) begin
            data_in = i; #10;
        end
        
        if (full) $display("FIFO is full.");
        
        // End simulation
        #10;
        $finish;
    end
    
    // Monitor changes
    initial begin
        $monitor("Time: %0t, Reset: %b, WriteEn: %b, ReadEn: %b, DataIn: %h, DataOut: %h, Empty: %b, Full: %b",
                 $time, reset, write_en, read_en, data_in, data_out, empty, full);
    end
endmodule