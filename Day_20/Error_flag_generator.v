`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 13.03.2025 16:27:27
// Design Name: 
// Module Name: Error_flag_generator
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


module error_flag_generator #(
    parameter NUM_ERRORS = 4
) (
    input wire clk,
    input wire rst_n,
    input wire [NUM_ERRORS-1:0] error_inputs,
    input wire [NUM_ERRORS-1:0] error_mask,
    output reg error_flag,
    output reg [NUM_ERRORS-1:0] error_status
);

    // Internal signals
    wire [NUM_ERRORS-1:0] masked_errors;
    
    // Apply mask to errors
    assign masked_errors = error_inputs & ~error_mask;
    
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            error_flag <= 1'b0;
            error_status <= {NUM_ERRORS{1'b0}};
        end else begin
            // Store current error status
            error_status <= masked_errors;
            
            // Assert error flag if any unmasked error is active
            error_flag <= |masked_errors;
        end
    end

endmodule

`timescale 1ns/1ps

module error_flag_generator_tb();
    // Parameters
    localparam NUM_ERRORS = 4;
    
    // Testbench signals
    reg clk;
    reg rst_n;
    reg [NUM_ERRORS-1:0] error_inputs;
    reg [NUM_ERRORS-1:0] error_mask;
    wire error_flag;
    wire [NUM_ERRORS-1:0] error_status;
    
    // Instantiate the DUT
    error_flag_generator #(
        .NUM_ERRORS(NUM_ERRORS)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .error_inputs(error_inputs),
        .error_mask(error_mask),
        .error_flag(error_flag),
        .error_status(error_status)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 100MHz clock
    end
    
    // Test sequence
    initial begin
        // Initialize
        rst_n = 0;
        error_inputs = 4'b0000;
        error_mask = 4'b0000;
        #20;
        
        // Release reset
        rst_n = 1;
        #10;
        
        // Test case 1: No errors
        error_inputs = 4'b0000;
        error_mask = 4'b0000;
        #20;
        
        // Test case 2: One error, no mask
        error_inputs = 4'b0001;
        error_mask = 4'b0000;
        #20;
        
        // Test case 3: Multiple errors, no mask
        error_inputs = 4'b1011;
        error_mask = 4'b0000;
        #20;
        
        // Test case 4: Multiple errors, some masked
        error_inputs = 4'b1111;
        error_mask = 4'b1010; // Mask bits 1 and 3
        #20;
        
        // Test case 5: All errors masked
        error_inputs = 4'b1111;
        error_mask = 4'b1111;
        #20;
        
        // Complete the simulation
        #20;
        $display("Simulation completed");
        $finish;
    end
    
    // Monitor
    initial begin
        $monitor("Time=%0t, error_inputs=%b, error_mask=%b, error_status=%b, error_flag=%b", 
                 $time, error_inputs, error_mask, error_status, error_flag);
    end
    
endmodule
