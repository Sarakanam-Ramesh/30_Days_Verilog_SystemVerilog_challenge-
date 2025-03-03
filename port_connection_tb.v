`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 02.03.2025 11:31:49
// Design Name: 
// Module Name: port_connection_tb
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

module port_connection_tb;
    // Testbench signals
    reg        clk;
    reg        rst_n;
    reg  [7:0] data_a;
    reg  [7:0] data_b;
    wire [8:0] result;
    wire       io_pin;
    
    // Bidirectional pin model
    reg        tb_io_dir;  // Direction from testbench side
    reg        tb_io_out;  // Output from testbench
    integer i;
    // Drive bidirectional pin
    assign io_pin = tb_io_dir ? tb_io_out : 1'bz;
    
    // Instantiate DUT
    port_connection dut (
        .clk(clk),
        .rst_n(rst_n),
        .data_a(data_a),
        .data_b(data_b),
        .result(result),
        .io_pin(io_pin)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 100MHz clock
    end
    
    // Test stimulus
    initial begin
        // Initialize signals
        rst_n = 0;
        data_a = 0;
        data_b = 0;
        tb_io_dir = 0;  // Initially high-Z from testbench side
        tb_io_out = 0;
        
        // Apply reset
        #20 rst_n = 1;
        
        // Test Case 1: Input mode
        $display("\nTest Case 1: Input Mode (even sum)");
        data_a = 8'h44;
        data_b = 8'h22;
        // Result will be 0x66, which is even, so gpio_direction is 0 (input mode)
        
        #10;
        // Drive the pin from testbench
        tb_io_dir = 1;
        tb_io_out = 1;
        
        #20;
        
        // Test Case 2: Output mode
        $display("\nTest Case 2: Output Mode (odd sum)");
        data_a = 8'h45;
        data_b = 8'h22;
        // Result will be 0x67, which is odd, so gpio_direction is 1 (output mode)
        
        #10;
        // Testbench should not drive the pin
        tb_io_dir = 0;
        
        #20;
        
        // Test Case 3: Multiple transitions
        $display("\nTest Case 3: Multiple Transitions");
        for ( i = 0; i < 8; i = i + 1) begin
            data_a = $random;
            data_b = $random;
            
            #15;
            
            $display("data_a=%h, data_b=%h, result=%h, io_pin=%b", data_a, data_b, result, io_pin);
            
            // If the sum is odd, direction is input, so testbench drives the pin
            if (result[0] == 1'b0) begin
                tb_io_dir = 1;
                tb_io_out = $random;
            end else begin
                tb_io_dir = 0;
            end
        end
        
        // End simulation
        #50;
        $display("Simulation complete");
        $finish;
    end
    
endmodule
