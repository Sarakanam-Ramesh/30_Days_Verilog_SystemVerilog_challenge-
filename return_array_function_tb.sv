`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 28.02.2025 22:31:26
// Design Name: 
// Module Name: return_array_function_tb
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

module return_array_function_tb;
    // Testbench signals
    logic clk;
    logic rst_n;
    logic [7:0] data_in;
    logic data_valid;
    logic [1:0] op_select;
    logic [7:0] result_array [0:3];
    logic result_valid;
    
    // Instantiate the DUT (Device Under Test)
    return_array_function DUT (
        .clk(clk),
        .rst_n(rst_n),
        .data_in(data_in),
        .data_valid(data_valid),
        .op_select(op_select),
        .result_array(result_array),
        .result_valid(result_valid)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 10ns period (100MHz)
    end
    
    // Test stimulus
    initial begin
        // Initialize signals
        rst_n = 0;
        data_in = 8'h00;
        data_valid = 0;
        op_select = 2'b00;
        
        // Apply reset
        #20;
        rst_n = 1;
        #10;
        
        // Test case 1: Increment operation (op_select = 2'b00)
        data_in = 8'h0A; // 10 in decimal
        op_select = 2'b00;
        data_valid = 1;
        #10;
        data_valid = 0;
        #20;
        
        // Test case 2: Left shift operation (op_select = 2'b01)
        data_in = 8'h05; // 5 in decimal
        op_select = 2'b01;
        data_valid = 1;
        #10;
        data_valid = 0;
        #20;
        
        // Test case 3: Bitwise operations (op_select = 2'b10)
        data_in = 8'hA5; // 10100101 in binary
        op_select = 2'b10;
        data_valid = 1;
        #10;
        data_valid = 0;
        #20;
        
        // Test case 4: Various operations (op_select = 2'b11)
        data_in = 8'h14; // 20 in decimal
        op_select = 2'b11;
        data_valid = 1;
        #10;
        data_valid = 0;
        #20;
        
        // Test case 5: Test data_valid toggling
        data_in = 8'h32; // 50 in decimal
        op_select = 2'b00;
        data_valid = 1;
        #10;
        data_valid = 0;
        #20;
        
        // Test case 6: Apply reset mid-operation
        data_in = 8'h64; // 100 in decimal
        op_select = 2'b11;
        data_valid = 1;
        #5;
        rst_n = 0;
        #10;
        rst_n = 1;
        data_valid = 0;
        #20;
        
        // End simulation
        $display("Simulation completed successfully");
        $finish;
    end
    
    // Monitor results
    always @(posedge clk) begin
        if (result_valid) begin
            $display("Time: %t, Operation: %b, Input: %h, Results: [%h, %h, %h, %h]", 
                    $time, op_select, data_in, 
                    result_array[0], result_array[1], result_array[2], result_array[3]);
            
            // Verify results
            case (op_select)
                2'b00: begin // Increment by 1, 2, 3, 4
                    if (result_array[0] !== (data_in + 8'd1) ||
                        result_array[1] !== (data_in + 8'd2) ||
                        result_array[2] !== (data_in + 8'd3) ||
                        result_array[3] !== (data_in + 8'd4)) begin
                        $error("Increment operation failed at time %t", $time);
                    end
                end
                
                2'b01: begin // Left shift by 1, 2, 3, 4
                    if (result_array[0] !== (data_in << 1) ||
                        result_array[1] !== (data_in << 2) ||
                        result_array[2] !== (data_in << 3) ||
                        result_array[3] !== (data_in << 4)) begin
                        $error("Left shift operation failed at time %t", $time);
                    end
                end
                
                2'b10: begin // Bit-wise operations
                    if (result_array[0] !== (~data_in) ||
                        result_array[1] !== (data_in & 8'hF0) ||
                        result_array[2] !== (data_in | 8'h0F) ||
                        result_array[3] !== (data_in ^ 8'hFF)) begin
                        $error("Bitwise operation failed at time %t", $time);
                    end
                end
                
                2'b11: begin // Various operations
                    if (result_array[0] !== data_in ||
                        result_array[1] !== (data_in * 2) ||
                        result_array[2] !== (data_in / 2) ||
                        result_array[3] !== (data_in % 10)) begin
                        $error("Various operations failed at time %t", $time);
                    end
                end
            endcase
        end
    end
endmodule
