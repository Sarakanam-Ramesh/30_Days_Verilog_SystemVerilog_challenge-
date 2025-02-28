`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 28.02.2025 22:20:57
// Design Name: 
// Module Name: void_display_task_tb
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


module void_display_task_tb;
    // Testbench signals
    logic clk;
    logic rst_n;
    logic [31:0] data_in;
    logic [1:0] format_sel;
    logic display_en;
    logic display_busy;
    
    // Instantiate the device under test
    void_display_task dut (
        .clk(clk),
        .rst_n(rst_n),
        .data_in(data_in),
        .format_sel(format_sel),
        .display_en(display_en),
        .display_busy(display_busy)
    );
    
    // Clock generation
    always #5 clk = ~clk;
    
    // Display results - modified to use reg instead of string type
    task display_results;
        input [1:0] op_type;
        begin
            case (op_type)
                2'b00: $display("Operation: Hexadecimal Display");
                2'b01: $display("Operation: Decimal Display");
                2'b10: $display("Operation: Binary Display");
                2'b11: $display("Operation: ASCII Display");
            endcase
            $display("Input: %h", data_in);
            $display("------------------------------");
        end
    endtask
    
    // Test stimulus
    initial begin
        // Initialize signals
        clk = 0;
        rst_n = 0;
        data_in = 32'h0;
        format_sel = 2'b00;
        display_en = 0;
        
        // Release reset
        #20 rst_n = 1;
        
        // Test case 1: Display hexadecimal format
        #10;
        data_in = 32'hABCD1234;
        format_sel = 2'b00; // HEX format
        display_en = 1;
        #10;
        display_en = 0;
        
        // Wait until not busy
        @(negedge display_busy);
        #20;
        display_results(2'b00);
        
        // Test case 2: Display decimal format
        data_in = 32'd987654321;
        format_sel = 2'b01; // DEC format
        display_en = 1;
        #10;
        display_en = 0;
        
        // Wait until not busy
        @(negedge display_busy);
        #20;
        display_results(2'b01);
        
        // Test case 3: Display binary format
        data_in = 32'b10101010_11001100_11110000_10101010;
        format_sel = 2'b10; // BIN format
        display_en = 1;
        #10;
        display_en = 0;
        
        // Wait until not busy
        @(negedge display_busy);
        #20;
        display_results(2'b10);
        
        // Test case 4: Display ASCII format
        data_in = {8'd72, 8'd101, 8'd108, 8'd111}; // "Hello" in ASCII
        format_sel = 2'b11; // ASCII format
        display_en = 1;
        #10;
        display_en = 0;
        
        // Wait until not busy
        @(negedge display_busy);
        #20;
        display_results(2'b11);
        
        $finish;
    end
endmodule
