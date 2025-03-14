`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 13.03.2025 16:30:34
// Design Name: 
// Module Name: Status_monitor
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


module status_monitor (
    input wire clk,
    input wire rst_n,
    input wire valid,
    input wire ready,
    input wire [7:0] data,
    output reg protocol_error,
    output reg [2:0] error_code
);

    // Error codes
    localparam ERR_NONE       = 3'b000;
    localparam ERR_VALID_DROP = 3'b001; // Valid dropped without ready
    localparam ERR_DATA_ZERO  = 3'b010; // Data is zero when valid
    localparam ERR_READY_WO_VALID = 3'b011; // Ready without valid for too long
    
    // Internal signals
    reg valid_prev;
    reg [3:0] ready_without_valid_count;
    
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            protocol_error <= 1'b0;
            error_code <= ERR_NONE;
            valid_prev <= 1'b0;
            ready_without_valid_count <= 4'b0;
        end else begin
            valid_prev <= valid;
            protocol_error <= 1'b0; // Default to no error
            
            // Check for valid dropping without ready
            if (valid_prev && !valid && !ready) begin
                protocol_error <= 1'b1;
                error_code <= ERR_VALID_DROP;
            end
            
            // Check for zero data when valid
            if (valid && (data == 8'h00)) begin
                protocol_error <= 1'b1;
                error_code <= ERR_DATA_ZERO;
            end
            
            // Check for ready without valid for too long
            if (ready && !valid) begin
                if (ready_without_valid_count < 4'b1111) begin
                    ready_without_valid_count <= ready_without_valid_count + 1'b1;
                end
                
                if (ready_without_valid_count >= 4'd8) begin
                    protocol_error <= 1'b1;
                    error_code <= ERR_READY_WO_VALID;
                end
            end else begin
                ready_without_valid_count <= 4'b0;
            end
        end
    end

endmodule

`timescale 1ns/1ps

module status_monitor_tb();
    // Testbench signals
    reg clk;
    reg rst_n;
    reg valid;
    reg ready;
    reg [7:0] data;
    wire protocol_error;
    wire [2:0] error_code;
    
    // Instantiate the DUT
    status_monitor dut (
        .clk(clk),
        .rst_n(rst_n),
        .valid(valid),
        .ready(ready),
        .data(data),
        .protocol_error(protocol_error),
        .error_code(error_code)
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
        valid = 0;
        ready = 0;
        data = 8'hAA;
        #20;
        
        // Release reset
        rst_n = 1;
        #10;
        
        // Test case 1: Normal operation
        valid = 1;
        ready = 1;
        data = 8'hAA;
        #20;
        valid = 0;
        ready = 0;
        #20;
        
        // Test case 2: Error - Valid dropped without ready
        valid = 1;
        ready = 0;
        data = 8'hBB;
        #20;
        valid = 0; // Drop valid without ready
        #20;
        
        // Test case 3: Error - Data is zero when valid
        valid = 1;
        ready = 1;
        data = 8'h00; // Zero data with valid
        #20;
        valid = 0;
        ready = 0;
        #20;
        
        // Test case 4: Error - Ready without valid for too long
        valid = 0;
        ready = 1;
        data = 8'hCC;
        // Keep ready high without valid for 10 cycles
        repeat (10) #10;
        ready = 0;
        #20;
        
        // Complete the simulation
        #20;
        $display("Simulation completed");
        $finish;
    end
    
    // Monitor
    initial begin
        $monitor("Time=%0t, valid=%b, ready=%b, data=%h, protocol_error=%b, error_code=%b", 
                 $time, valid, ready, data, protocol_error, error_code);
    end
    
endmodule
