`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 13.03.2025 16:41:12
// Design Name: 
// Module Name: Error_injection
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

module error_injection #(
    parameter NUM_CHANNELS = 4,
    parameter ERROR_TYPES = 3  // Number of error types per channel
)(
    input  logic                           clk,
    input  logic                           rst_n,
    input  logic                           enable,        // Enable error injection
    input  logic [NUM_CHANNELS-1:0]        channel_sel,   // Select which channels to affect
    input  logic [ERROR_TYPES-1:0]         error_type,    // Type of error to inject
    input  logic [31:0]                    error_config,  // Configuration for the error
    input  logic                           inject,        // Trigger to inject the error
    input  logic [NUM_CHANNELS-1:0][7:0]   data_in,       // Original data streams
    output logic [NUM_CHANNELS-1:0][7:0]   data_out,      // Modified data streams
    output logic [NUM_CHANNELS-1:0]        error_active   // Indicates error is active on channels
);

    // Error injection state for each channel
    logic [NUM_CHANNELS-1:0] error_state;
    // Error type for each channel
    logic [NUM_CHANNELS-1:0][ERROR_TYPES-1:0] channel_error_type;
    // Error configuration for each channel
    logic [NUM_CHANNELS-1:0][31:0] channel_error_config;
    
    // Store error configuration when inject is triggered
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            error_state <= '0;
            channel_error_type <= '0;
            channel_error_config <= '0;
        end else if (!enable) begin
            error_state <= '0;
        end else if (inject) begin
            for (int i = 0; i < NUM_CHANNELS; i++) begin
                if (channel_sel[i]) begin
                    error_state[i] <= 1'b1;
                    channel_error_type[i] <= error_type;
                    channel_error_config[i] <= error_config;
                end
            end
        end
    end
    
    // Generate modified data based on error type and configuration
    always_comb begin
        data_out = data_in;
        error_active = '0;
        
        for (int i = 0; i < NUM_CHANNELS; i++) begin
            if (enable && error_state[i]) begin
                error_active[i] = 1'b1;
                
                // Apply different error types
                case (channel_error_type[i])
                    3'b001: begin
                        // Bit flip error - flip specific bit
                        data_out[i] = data_in[i] ^ (1 << channel_error_config[i][2:0]);
                    end
                    
                    3'b010: begin
                        // Stuck-at error - force value
                        data_out[i] = channel_error_config[i][7:0];
                    end
                    
                    3'b100: begin
                        // Delay error - previous cycle's value
                        // In RTL this would need a proper delay element
                        // This is simplified for synthesis
                        data_out[i] = data_in[i] ^ 8'hFF; // Invert as a simplified alternative
                    end
                    
                    default: begin
                        // No modification for unknown error types
                        data_out[i] = data_in[i];
                    end
                endcase
            end
        end
    end

endmodule

`timescale 1ns/1ps

module error_injection_tb;
    // Parameters
    localparam NUM_CHANNELS = 4;
    localparam ERROR_TYPES = 3;
    localparam CLK_PERIOD = 10; // 10ns = 100MHz
    
    // Signals
    logic clk;
    logic rst_n;
    logic enable;
    logic [NUM_CHANNELS-1:0] channel_sel;
    logic [ERROR_TYPES-1:0] error_type;
    logic [31:0] error_config;
    logic inject;
    logic [NUM_CHANNELS-1:0][7:0] data_in;
    logic [NUM_CHANNELS-1:0][7:0] data_out;
    logic [NUM_CHANNELS-1:0] error_active;
    
    // Instantiate DUT
    error_injection #(
        .NUM_CHANNELS(NUM_CHANNELS),
        .ERROR_TYPES(ERROR_TYPES)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .enable(enable),
        .channel_sel(channel_sel),
        .error_type(error_type),
        .error_config(error_config),
        .inject(inject),
        .data_in(data_in),
        .data_out(data_out),
        .error_active(error_active)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #(CLK_PERIOD/2) clk = ~clk;
    end
    
    // Data generation - increment data each cycle
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            data_in <= '0;
        end else begin
            for (int i = 0; i < NUM_CHANNELS; i++) begin
                data_in[i] <= data_in[i] + 1;
            end
        end
    end
    
    // Test sequence
    initial begin
        // Initialize signals
        rst_n = 0;
        enable = 0;
        channel_sel = '0;
        error_type = '0;
        error_config = '0;
        inject = 0;
        
        // Apply reset
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
        
        // Start with normal operation
        $display("Normal operation");
        enable = 1;
        repeat(10) @(posedge clk);
        
        // Test case 1: Bit flip error on channel 0
        $display("Test case 1: Bit flip error on channel 0");
        channel_sel = 4'b0001; // Channel 0
        error_type = 3'b001;   // Bit flip
        error_config = 32'h3;  // Flip bit 3
        inject = 1;
        @(posedge clk);
        inject = 0;
        
        // Run for some cycles with error active
        repeat(10) @(posedge clk);
        
        // Test case 2: Stuck-at error on channel 1
        $display("Test case 2: Stuck-at error on channel 1");
        channel_sel = 4'b0010; // Channel 1
        error_type = 3'b010;   // Stuck-at
        error_config = 32'hAA; // Stuck at 0xAA
        inject = 1;
        @(posedge clk);
        inject = 0;
        
        // Run for some cycles with error active
        repeat(10) @(posedge clk);
        
        // Test case 3: Delay/Invert error on channel 2
        $display("Test case 3: Invert error on channel 2");
        channel_sel = 4'b0100; // Channel 2
        error_type = 3'b100;   // Invert (simplified from delay)
        error_config = 32'h0;  // Not used for invert
        inject = 1;
        @(posedge clk);
        inject = 0;
        
        // Run for some cycles with error active
        repeat(10) @(posedge clk);
        
        // Test case 4: Multiple channels
        $display("Test case 4: Multiple channel errors");
        channel_sel = 4'b1001; // Channel 0 and 3
        error_type = 3'b010;   // Stuck-at
        error_config = 32'h55; // Stuck at 0x55
        inject = 1;
        @(posedge clk);
        inject = 0;
        
        // Run for some cycles with errors active
        repeat(10) @(posedge clk);
        
        // Disable error injection
        $display("Disabling error injection");
        enable = 0;
        repeat(10) @(posedge clk);
        
        // End simulation
        $display("Simulation complete");
        $finish;
    end
    
    // Monitor results
    always @(posedge clk) begin
        for (int i = 0; i < NUM_CHANNELS; i++) begin
            if (error_active[i]) begin
                $display("Time %0t: Channel %0d - Input: %h, Output: %h (ERROR)", 
                         $time, i, data_in[i], data_out[i]);
            end
        end
    end
    
endmodule