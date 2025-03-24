`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 23.03.2025 11:05:44
// Design Name: 
// Module Name: UART_top
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


module uart_top #(
    parameter CLOCK_FREQ = 50000000,  // Default 50MHz system clock
    parameter DEFAULT_BAUD = 9600,    // Default baud rate
    parameter DATA_WIDTH = 8,         // Data width (typically 8)
    parameter STOP_BITS = 1,          // Stop bits (1 or 2)
    parameter PARITY_EN = 0,          // Parity: 0=None, 1=Even, 2=Odd
    parameter OVERSAMPLING = 16       // Oversampling rate for receiver
) (
    input wire clk,                     // System clock
    input wire rst_n,                   // Active low reset
    
    // UART External Interface
    input wire rx,                      // UART RX pin
    output wire tx,                     // UART TX pin
    
    // Transmitter Interface
    input wire tx_start,                // Start transmission
    input wire [DATA_WIDTH-1:0] tx_data,// Data to transmit
    output wire tx_busy,                // Transmitter busy
    output wire tx_done,                // Transmission complete
    
    // Receiver Interface
    output wire [DATA_WIDTH-1:0] rx_data,// Received data
    output wire rx_valid,               // Received data valid
    
    // Configuration
    input wire [15:0] baud_cfg,         // Baud rate config (0 = use default)
    
    // Error signals
    output wire frame_error,            // Frame error
    output wire parity_error,           // Parity error
    output wire overrun_error,          // Overrun error
    output wire break_detected,         // Break condition detected
    
    // Statistics
    output wire [7:0] frame_error_count,  // Count of frame errors
    output wire [7:0] parity_error_count, // Count of parity errors
    output wire [7:0] overrun_error_count,// Count of overrun errors
    output wire [7:0] break_count,        // Count of break conditions
    output wire [15:0] bytes_received,    // Total bytes received
    output wire [15:0] packets_received,  // Packets received
    
    // Control
    input wire clear_stats               // Clear statistics counters
);

    // Baud tick signal
    wire baud_tick;

    // Generate baud rate
    baud_generator #(
        .CLOCK_FREQ(CLOCK_FREQ),
        .DEFAULT_BAUD(DEFAULT_BAUD),
        .OVERSAMPLING(OVERSAMPLING)
    ) baud_gen (
        .clk(clk),
        .rst_n(rst_n),
        .baud_cfg(baud_cfg),
        .baud_tick(baud_tick)
    );
    
    // UART Transmitter
    uart_tx #(
        .DATA_WIDTH(DATA_WIDTH),
        .STOP_BITS(STOP_BITS),
        .PARITY_EN(PARITY_EN),
        .BAUD_DIV(0)  // Use external baud generator
    ) uart_transmitter (
        .clk(clk),
        .rst_n(rst_n),
        .tx_start(tx_start),
        .tx_data(tx_data),
        .baud_tick(baud_tick),
        .tx(tx),
        .tx_busy(tx_busy),
        .tx_done(tx_done)
    );
    
    // UART Receiver
    uart_rx #(
        .DATA_WIDTH(DATA_WIDTH),
        .STOP_BITS(STOP_BITS),
        .PARITY_EN(PARITY_EN),
        .BAUD_DIV(0),  // Use external baud generator
        .SAMPLE_RATE(OVERSAMPLING)
    ) uart_receiver (
        .clk(clk),
        .rst_n(rst_n),
        .rx(rx),
        .baud_tick(baud_tick),
        .rx_data(rx_data),
        .rx_valid(rx_valid),
        .frame_error(frame_error),
        .parity_error(parity_error),
        .overrun_error(overrun_error)
    );
    
    // Protocol Checker
    uart_protocol_checker #(
        .DATA_WIDTH(DATA_WIDTH)
    ) protocol_checker (
        .clk(clk),
        .rst_n(rst_n),
        .rx_valid(rx_valid),
        .rx_data(rx_data),
        .frame_error(frame_error),
        .parity_error(parity_error),
        .overrun_error(overrun_error),
        .frame_error_count(frame_error_count),
        .parity_error_count(parity_error_count),
        .overrun_error_count(overrun_error_count),
        .break_count(break_count),
        .error_detected(),  // Not connected at top level
        .error_type(),      // Not connected at top level
        .break_detected(break_detected),
        .bytes_received(bytes_received),
        .packets_received(packets_received),
        .clear_stats(clear_stats)
    );
    
endmodule

`timescale 1ns/1ps

module uart_top_tb();
    // Parameters
    parameter CLOCK_FREQ = 50000000;  // 50MHz system clock
    parameter DEFAULT_BAUD = 9600;     // Default baud rate
    parameter DATA_WIDTH = 8;          // Data width
    parameter STOP_BITS = 1;           // Stop bits
    parameter PARITY_EN = 0;           // No parity
    parameter OVERSAMPLING = 16;       // Oversampling rate
    
    parameter CLK_PERIOD = 20;         // 20ns = 50MHz
    
    // Test bench signals
    reg clk;
    reg rst_n;
    
    // UART signals
    wire rx;
    wire tx;
    
    // Loopback connection (tx -> rx)
    assign rx = tx;
    
    // Transmitter interface
    reg tx_start;
    reg [DATA_WIDTH-1:0] tx_data;
    wire tx_busy;
    wire tx_done;
    
    // Receiver interface
    wire [DATA_WIDTH-1:0] rx_data;
    wire rx_valid;
    
    // Configuration
    reg [15:0] baud_cfg;
    
    // Error signals
    wire frame_error;
    wire parity_error;
    wire overrun_error;
    wire break_detected;
    
    // Statistics
    wire [7:0] frame_error_count;
    wire [7:0] parity_error_count;
    wire [7:0] overrun_error_count;
    wire [7:0] break_count;
    wire [15:0] bytes_received;
    wire [15:0] packets_received;
    
    // Control
    reg clear_stats;
    
    // Expected values for checking
    reg [7:0] expected_bytes;
    reg [7:0] expected_errors;
    
    // Test sequence counter
    reg [7:0] test_seq;
    
    // Instantiate the module under test
    uart_top #(
        .CLOCK_FREQ(CLOCK_FREQ),
        .DEFAULT_BAUD(DEFAULT_BAUD),
        .DATA_WIDTH(DATA_WIDTH),
        .STOP_BITS(STOP_BITS),
        .PARITY_EN(PARITY_EN),
        .OVERSAMPLING(OVERSAMPLING)
    ) uut (
        .clk(clk),
        .rst_n(rst_n),
        .rx(rx),
        .tx(tx),
        .tx_start(tx_start),
        .tx_data(tx_data),
        .tx_busy(tx_busy),
        .tx_done(tx_done),
        .rx_data(rx_data),
        .rx_valid(rx_valid),
        .baud_cfg(baud_cfg),
        .frame_error(frame_error),
        .parity_error(parity_error),
        .overrun_error(overrun_error),
        .break_detected(break_detected),
        .frame_error_count(frame_error_count),
        .parity_error_count(parity_error_count),
        .overrun_error_count(overrun_error_count),
        .break_count(break_count),
        .bytes_received(bytes_received),
        .packets_received(packets_received),
        .clear_stats(clear_stats)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #(CLK_PERIOD/2) clk = ~clk;
    end
    
    // Task to wait for transmitter to complete
    task wait_for_tx_done;
        begin
            wait(tx_done);
            @(posedge clk);
            // Add extra wait time for receiver to process
            repeat(OVERSAMPLING*12) @(posedge clk);
        end
    endtask
    
    // Task to send a byte
    task send_byte;
        input [DATA_WIDTH-1:0] data;
        begin
            // Wait until transmitter is not busy
            wait (!tx_busy);
            @(posedge clk);
            
            // Start transmission
            tx_data = data;
            tx_start = 1'b1;
            @(posedge clk);
            tx_start = 1'b0;
            
            // Wait for completion
            wait_for_tx_done();
        end
    endtask
    
    // Task to check received data
    task check_received_data;
        input [DATA_WIDTH-1:0] expected_data;
        begin
            // Wait for rx_valid to assert
            wait(rx_valid);
            @(posedge clk);
            
            // Check data
            if (rx_data !== expected_data) begin
                $display("Error: rx_data = %h, expected %h", rx_data, expected_data);
            end
            
            // Wait for rx_valid to deassert
            wait(!rx_valid);
            @(posedge clk);
        end
    endtask
    
    // Task to check statistics
    task check_stats;
        input [15:0] exp_bytes;
        input [7:0] exp_frame_errs;
        input [7:0] exp_parity_errs;
        input [7:0] exp_overrun_errs;
        input [7:0] exp_breaks;
        begin
            if (bytes_received !== exp_bytes)
                $display("Error: bytes_received = %d, expected %d", bytes_received, exp_bytes);
                
            if (frame_error_count !== exp_frame_errs)
                $display("Error: frame_error_count = %d, expected %d", frame_error_count, exp_frame_errs);
                
            if (parity_error_count !== exp_parity_errs)
                $display("Error: parity_error_count = %d, expected %d", parity_error_count, exp_parity_errs);
                
            if (overrun_error_count !== exp_overrun_errs)
                $display("Error: overrun_error_count = %d, expected %d", overrun_error_count, exp_overrun_errs);
                
            if (break_count !== exp_breaks)
                $display("Error: break_count = %d, expected %d", break_count, exp_breaks);
        end
    endtask
    
    // Task to clear statistics
    task clear_statistics;
        begin
            clear_stats = 1'b1;
            @(posedge clk);
            clear_stats = 1'b0;
            @(posedge clk);
        end
    endtask
    
    // Baud rate calculation for the testbench
    function [31:0] calculate_baud_div;
        input [31:0] target_baud;
        begin
            calculate_baud_div = ((CLOCK_FREQ / (OVERSAMPLING * target_baud)) - 1);
        end
    endfunction
    
    // Task to configure baud rate
    task set_baud_rate;
        input [31:0] new_baud;
            reg [31:0] temp_baud_div;
        begin
        temp_baud_div = calculate_baud_div(new_baud);
        baud_cfg = temp_baud_div[15:0];
            // Wait for configuration to take effect
            repeat (10) @(posedge clk);
        end
    endtask
    
    // Task to send multiple bytes in sequence
    task send_multiple_bytes;
        input [7:0] start_value;
        input [7:0] count;
        integer i;
        begin
            for (i = 0; i < count; i = i + 1) begin
                send_byte(start_value + i);
            end
        end
    endtask
    
    // Main test sequence
    initial begin
        // Initialize
        rst_n = 0;
        tx_start = 0;
        tx_data = 0;
        baud_cfg = 0;  // Use default
        clear_stats = 0;
        expected_bytes = 0;
        expected_errors = 0;
        
        // Reset sequence
        repeat (10) @(posedge clk);
        rst_n = 1;
        repeat (10) @(posedge clk);
        
        // Test 1: Basic loopback at default baud rate
        $display("Test 1: Basic loopback test at default baud rate");
        for (test_seq = 0; test_seq < 10; test_seq = test_seq + 1) begin
            send_byte(test_seq);
            expected_bytes = expected_bytes + 1;
        end
        
        // Check statistics
        check_stats(10, 0, 0, 0, 0);
        
        // Test 2: Change baud rate
        $display("Test 2: Change baud rate to 115200");
        set_baud_rate(115200);
        
        for (test_seq = 0; test_seq < 5; test_seq = test_seq + 1) begin
            send_byte(8'hA0 + test_seq);
            expected_bytes = expected_bytes + 1;
        end
        
        // Check statistics
        check_stats(15, 0, 0, 0, 0);
        
        // Test 3: Send various data patterns
        $display("Test 3: Send various data patterns");
        send_byte(8'h00);  // All zeros
        send_byte(8'hFF);  // All ones
        send_byte(8'hA5);  // Alternating
        send_byte(8'h5A);  // Alternating
        expected_bytes = expected_bytes + 4;
        
        // Check statistics
        check_stats(19, 0, 0, 0, 0);
        
        // Test 4: Clear statistics
        $display("Test 4: Clear statistics");
        clear_statistics();
        expected_bytes = 0;
        
        // Check that stats are cleared
        check_stats(0, 0, 0, 0, 0);
        
        // Test 5: Higher volume data transfer
        $display("Test 5: Higher volume data transfer");
        send_multiple_bytes(8'h20, 32);  // Send 32 bytes
        expected_bytes = expected_bytes + 32;
        
        // Check statistics
        check_stats(32, 0, 0, 0, 0);
        
        // Test 6: Send idle characters to form packet boundaries
        $display("Test 6: Packet boundary test");
        // Send first data burst
        send_multiple_bytes(8'h50, 5);
        expected_bytes = expected_bytes + 5;
        
        // Send idle characters (0xFF) to mark packet boundary
        repeat (5) send_byte(8'hFF);
        expected_bytes = expected_bytes + 5;
        
        // Send second data burst
        send_multiple_bytes(8'h60, 5);
        expected_bytes = expected_bytes + 5;
        
        // Check statistics - should have detected at least one packet
        // Note: The exact packet count may vary based on the protocol_checker implementation
        $display("Bytes received: %d, Packets detected: %d", 
                 bytes_received, packets_received);
        
        // Test complete
        repeat (100) @(posedge clk);
        $display("All tests completed");
        $finish;
    end
    
    // Optional: Monitor important signals
    initial begin
        $monitor("Time=%0t: tx_busy=%b, tx_done=%b, rx_valid=%b, rx_data=%h",
                 $time, tx_busy, tx_done, rx_valid, rx_data);
    end
    
endmodule
