`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11.03.2025 19:01:05
// Design Name: 
// Module Name: Resuable_counter
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


module reusable_counter_19 #(
    parameter WIDTH = 8,             // Counter width
    parameter INCREMENT = 1,          // Counter increment value
    parameter MAX_VALUE = {WIDTH{1'b1}}, // Maximum counter value
    parameter RESET_VALUE = {WIDTH{1'b0}} // Reset value
)(
    input wire clk,
    input wire rst_n,
    input wire enable,
    input wire clear,
    input wire load_en,
    input wire [WIDTH-1:0] load_val,
    output wire [WIDTH-1:0] count,
    output wire overflow
);
    // Internal registers
    reg [WIDTH-1:0] count_reg;
    
    // Counter logic
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            count_reg <= RESET_VALUE;
        else if (clear)
            count_reg <= RESET_VALUE;
        else if (load_en)
            count_reg <= load_val;
        else if (enable) begin
            if (count_reg + INCREMENT > MAX_VALUE)
                count_reg <= RESET_VALUE;
            else
                count_reg <= count_reg + INCREMENT;
        end
    end
    
    // Assign outputs
    assign count = count_reg;
    assign overflow = enable && (count_reg + INCREMENT > MAX_VALUE);
    
endmodule

`timescale 1ns/1ps

module reusable_counter_19_tb();
    // Define parameters for testing
    localparam WIDTH = 4;
    localparam INCREMENT = 2;
    localparam MAX_VALUE = 4'hA; // Stop at 10
    localparam RESET_VALUE = 4'h2; // Start from 2
    
    // Testbench signals
    reg clk;
    reg rst_n;
    reg enable;
    reg clear;
    reg load_en;
    reg [WIDTH-1:0] load_val;
    wire [WIDTH-1:0] count;
    wire overflow;
    
    // Instantiate the counter with parameters
    reusable_counter_19 #(
        .WIDTH(WIDTH),
        .INCREMENT(INCREMENT),
        .MAX_VALUE(MAX_VALUE),
        .RESET_VALUE(RESET_VALUE)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .enable(enable),
        .clear(clear),
        .load_en(load_en),
        .load_val(load_val),
        .count(count),
        .overflow(overflow)
    );
    
    // Clock generation
    always #5 clk = ~clk;
    
    // Test sequence
    initial begin
        // Initialize signals
        clk = 0;
        rst_n = 0;
        enable = 0;
        clear = 0;
        load_en = 0;
        load_val = 0;
        
        // Apply reset
        #20 rst_n = 1;
        
        // Test counting by 2
        #10 enable = 1;
        #50;
        
        // Test overflow
        #20;
        
        // Test clear
        #10 clear = 1;
        #10 clear = 0;
        #20;
        
        // Test load
        load_val = 4'h8;
        load_en = 1;
        #10 load_en = 0;
        #30;
        
        // End simulation
        $display("Simulation complete");
        $finish;
    end
    
    // Monitor
    always @(posedge clk) begin
        $display("Time=%0t, Count=%h, Enable=%b, Clear=%b, Load_EN=%b, Load_Val=%h, Overflow=%b", 
                 $time, count, enable, clear, load_en, load_val, overflow);
    end
endmodule