`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11.03.2025 18:36:24
// Design Name: 
// Module Name: Basic_module_wrapper
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
// Original module
module counter_4bit (
    input wire clk,
    input wire rst_n,
    input wire enable,
    output reg [3:0] count
);
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            count <= 4'b0000;
        else if (enable)
            count <= count + 1'b1;
    end
endmodule

module counter_4bit_wrapper_19 (
    input wire clk,
    input wire rst_n,
    input wire enable,
    input wire load_en,
    input wire [3:0] load_val,
    output wire [3:0] count
);
    // Internal signals
    reg [3:0] count_reg;
    wire [3:0] counter_out;
    wire counter_enable;
    
    // Logic for enabling counter
    assign counter_enable = enable & ~load_en;
    
    // Original counter instance
    counter_4bit counter_inst (
        .clk(clk),
        .rst_n(rst_n),
        .enable(counter_enable),
        .count(counter_out)
    );
    
    // Additional load functionality
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            count_reg <= 4'b0000;
        else if (load_en)
            count_reg <= load_val;
        else
            count_reg <= counter_out;
    end
    
    // Output assignment
    assign count = count_reg;
endmodule

`timescale 1ns/1ps

module counter_wrapper_19_tb();
    // Testbench signals
    reg clk;
    reg rst_n;
    reg enable;
    reg load_en;
    reg [3:0] load_val;
    wire [3:0] count;
    
    // Instantiate the wrapper
    counter_4bit_wrapper_19 dut (
        .clk(clk),
        .rst_n(rst_n),
        .enable(enable),
        .load_en(load_en),
        .load_val(load_val),
        .count(count)
    );
    
    // Clock generation
    always #5 clk = ~clk;
    
    // Test sequence
    initial begin
        // Initialize signals
        clk = 0;
        rst_n = 0;
        enable = 0;
        load_en = 0;
        load_val = 4'h0;
        
        // Reset
        #20 rst_n = 1;
        
        // Test counting
        #10 enable = 1;
        #40;
        
        // Test loading
        load_val = 4'h7;
        load_en = 1;
        #10;
        load_en = 0;
        #40;
        
        // Test counting from loaded value
        #40;
        
        // End simulation
        $display("Simulation complete");
        $finish;
    end
    
    // Monitor
    always @(posedge clk) begin
        $display("Time=%0t, Count=%h, Enable=%b, Load_EN=%b, Load_Val=%h", 
                 $time, count, enable, load_en, load_val);
    end
endmodule
