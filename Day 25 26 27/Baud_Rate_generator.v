`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 23.03.2025 11:00:51
// Design Name: 
// Module Name: Baud_Rate_generator
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


module baud_generator #(
    parameter CLOCK_FREQ = 50000000,  // Default 50MHz system clock
    parameter DEFAULT_BAUD = 9600,    // Default baud rate
    parameter OVERSAMPLING = 16       // Default oversampling rate
) (
    input wire clk,               // System clock
    input wire rst_n,             // Active low reset
    input wire [15:0] baud_cfg,   // Baud rate configuration (0 = use DEFAULT_BAUD)
    output reg baud_tick          // Baud rate tick output (at OVERSAMPLING times baud rate)
);

    // Calculate the default divider
    localparam DEFAULT_DIVIDER = CLOCK_FREQ / (DEFAULT_BAUD * OVERSAMPLING);
    
    // Internal signals
    reg [15:0] baud_divider;      // Divider value based on configuration
    reg [15:0] counter;           // Counter for division
    
    // Set baud rate divider based on configuration
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            baud_divider <= DEFAULT_DIVIDER;
        end else begin
            if (baud_cfg == 16'd0) begin
                baud_divider <= DEFAULT_DIVIDER;
            end else begin
                baud_divider <= CLOCK_FREQ / (baud_cfg * OVERSAMPLING);
            end
        end
    end
    
    // Generate baud rate ticks
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            counter <= 16'd0;
            baud_tick <= 1'b0;
        end else begin
            baud_tick <= 1'b0;  // Default state
            
            if (counter >= baud_divider - 1) begin
                counter <= 16'd0;
                baud_tick <= 1'b1;  // Generate tick pulse
            end else begin
                counter <= counter + 16'd1;
            end
        end
    end
    
endmodule

`timescale 1ns / 1ps

module baud_generator_tb();
    // Parameters
    parameter CLK_PERIOD = 20;  // 50 MHz clock
    parameter CLOCK_FREQ = 50000000;
    parameter DEFAULT_BAUD = 9600;
    parameter OVERSAMPLING = 16;
    
    // Calculated divider
    parameter DEFAULT_DIVIDER = CLOCK_FREQ / (DEFAULT_BAUD * OVERSAMPLING);
    
    // Test baud rates
    parameter [15:0] TEST_BAUD1 = 9600;    // Default
    parameter [15:0] TEST_BAUD2 = 115200;  // Common high speed
    parameter [15:0] TEST_BAUD3 = 1200;    // Low speed
    parameter [15:0] TEST_BAUD4 = 38400;   // Medium speed
    
    // Signals
    reg clk;
    reg rst_n;
    reg [15:0] baud_cfg;
    wire baud_tick;
    
    // Time tracking
    time last_tick;
    time current_tick;
    time tick_interval;
    real expected_interval;
    real error_percent;
    
    // Instantiate DUT
    baud_generator #(
        .CLOCK_FREQ(CLOCK_FREQ),
        .DEFAULT_BAUD(DEFAULT_BAUD),
        .OVERSAMPLING(OVERSAMPLING)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .baud_cfg(baud_cfg),
        .baud_tick(baud_tick)
    );
    
    // Clock generation
    always begin
        #(CLK_PERIOD/2) clk = ~clk;
    end
    
    // Task to verify baud rate
    task verify_baud_rate;
        input [15:0] baud_rate;
        integer tick_count;
        real measured_baud;
        begin
            // Calculate expected interval
            expected_interval = 1000000000.0 / (baud_rate * OVERSAMPLING);
            $display("Testing baud rate: %d", baud_rate);
            $display("Expected tick interval: %.2f ns", expected_interval);
            
            // Reset measurement variables
            last_tick = 0;
            tick_count = 0;
            
            // Apply baud configuration
            baud_cfg = baud_rate;
            #(CLK_PERIOD * 10);
            
            // Measure 100 ticks
            while (tick_count < 100) begin
                @(posedge baud_tick);
                current_tick = $time;
                
                if (last_tick != 0) begin
                    tick_interval = current_tick - last_tick;
                    error_percent = ((tick_interval - expected_interval) / expected_interval) * 100.0;
                    
                    if (tick_count > 5) begin  // Skip first few for stabilization
                        $display("Tick %0d: Interval = %0t ns, Error = %.2f%%", 
                                 tick_count, tick_interval, error_percent);
                        
                        // Check if within 5% of expected
                        if (error_percent > 5.0 || error_percent < -5.0) begin
                            $display("ERROR: Baud rate accuracy outside acceptable range!");
                        end
                    end
                end
                
                last_tick = current_tick;
                tick_count = tick_count + 1;
            end
            
            // Calculate actual baud rate
            measured_baud = 1000000000.0 / (tick_interval * OVERSAMPLING);
            $display("Measured baud rate: %.2f", measured_baud);
            $display("Baud rate test complete\n");
        end
    endtask
    
    // Test sequence
    initial begin
        // Initialize
        clk = 0;
        rst_n = 0;
        baud_cfg = 0;
        
        // Apply reset
        #(CLK_PERIOD * 10);
        rst_n = 1;
        #(CLK_PERIOD * 10);
        
        // Test 1: Default baud rate (using baud_cfg = 0)
        verify_baud_rate(0);  // Should use DEFAULT_BAUD
        
        // Test 2: 115200 baud
        verify_baud_rate(TEST_BAUD2);
        
        // Test 3: 1200 baud
        verify_baud_rate(TEST_BAUD3);
        
        // Test 4: 38400 baud
        verify_baud_rate(TEST_BAUD4);
        
        // Test completion
        #(CLK_PERIOD * 100);
        $display("All tests completed");
        $finish;
    end
    
    // Optional waveform dumping for simulation
    initial begin
        $dumpfile("baud_generator_tb.vcd");
        $dumpvars(0, baud_generator_tb);
    end
    
endmodule
