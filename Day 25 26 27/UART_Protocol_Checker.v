`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 23.03.2025 11:02:34
// Design Name: 
// Module Name: UART_Protocol_Checker
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


module uart_protocol_checker #(
    parameter DATA_WIDTH = 8
) (
    input wire clk,                      // System clock
    input wire rst_n,                    // Active low reset
    
    // UART receiver interface
    input wire rx_valid,                 // Data valid signal from receiver
    input wire [DATA_WIDTH-1:0] rx_data, // Received data
    input wire frame_error,              // Frame error from receiver
    input wire parity_error,             // Parity error from receiver
    input wire overrun_error,            // Overrun error from receiver
    
    // Error statistics and reporting
    output reg [7:0] frame_error_count,  // Count of frame errors
    output reg [7:0] parity_error_count, // Count of parity errors
    output reg [7:0] overrun_error_count,// Count of overrun errors
    output reg [7:0] break_count,        // Count of break conditions
    output reg error_detected,           // Indicates an error was detected
    output reg [1:0] error_type,         // 0=frame, 1=parity, 2=overrun, 3=break
    
    // Break detection
    output reg break_detected,           // Break condition detected
    
    // Protocol statistics
    output reg [15:0] bytes_received,    // Total bytes received
    output reg [15:0] packets_received,  // Packets received (assuming idle delimiter)
    
    // Control
    input wire clear_stats               // Clear all statistics counters
);

    // Break detection logic (all zeros for extended period)
    localparam BREAK_THRESHOLD = 10;     // Number of consecutive zeros to detect break
    reg [7:0] zero_counter;              // Count consecutive zeros
    reg break_active;                    // Currently in break condition
    
    // Packet detection (simple idle delimiter-based)
    reg [3:0] idle_counter;              // Count idle characters
    localparam PACKET_DELIMITER = 3;     // Idle characters to mark packet boundary
    
    // Previous state for edge detection
    reg prev_rx_valid;
    reg prev_frame_error;
    reg prev_parity_error;
    reg prev_overrun_error;
    
    // Handle break detection
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            zero_counter <= 0;
            break_detected <= 1'b0;
            break_active <= 1'b0;
        end else begin
            // Reset break detected flag
            break_detected <= 1'b0;
            
            // Check for all zeros in received data (potential break)
            if (rx_valid && (rx_data == 0) && frame_error) begin
                zero_counter <= zero_counter + 1'b1;
                if (zero_counter >= BREAK_THRESHOLD - 1 && !break_active) begin
                    break_detected <= 1'b1;  // Rising edge of break condition
                    break_active <= 1'b1;
                end
            end else if (rx_valid && ((rx_data != 0) || !frame_error)) begin
                zero_counter <= 0;
                break_active <= 1'b0;  // End of break condition
            end
        end
    end
    
    // Track packet boundaries
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            idle_counter <= 0;
            packets_received <= 0;
        end else if (clear_stats) begin
            packets_received <= 0;
        end else begin
            if (rx_valid) begin
                // Check for idle character (usually 0xFF)
                if (rx_data == {DATA_WIDTH{1'b1}}) begin
                    if (idle_counter < PACKET_DELIMITER) begin
                        idle_counter <= idle_counter + 1'b1;
                    end
                end else begin
                    // If we were in idle state and now received non-idle,
                    // increment packet count
                    if (idle_counter >= PACKET_DELIMITER) begin
                        packets_received <= packets_received + 1'b1;
                    end
                    idle_counter <= 0;
                end
            end
        end
    end
    
    // Error detection and statistics tracking
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            frame_error_count <= 0;
            parity_error_count <= 0;
            overrun_error_count <= 0;
            break_count <= 0;
            bytes_received <= 0;
            error_detected <= 1'b0;
            error_type <= 2'b00;
            prev_rx_valid <= 1'b0;
            prev_frame_error <= 1'b0;
            prev_parity_error <= 1'b0;
            prev_overrun_error <= 1'b0;
        end else if (clear_stats) begin
            frame_error_count <= 0;
            parity_error_count <= 0;
            overrun_error_count <= 0;
            break_count <= 0;
            bytes_received <= 0;
        end else begin
            // Default state for error detected flag (pulse for one cycle)
            error_detected <= 1'b0;
            
            // Count received bytes
            if (rx_valid && !prev_rx_valid) begin
                bytes_received <= bytes_received + 1'b1;
            end
            
            // Detect and count errors (on rising edge)
            if (frame_error && !prev_frame_error) begin
                frame_error_count <= frame_error_count + 1'b1;
                error_detected <= 1'b1;
                error_type <= 2'b00;
            end
            
            if (parity_error && !prev_parity_error) begin
                parity_error_count <= parity_error_count + 1'b1;
                error_detected <= 1'b1;
                error_type <= 2'b01;
            end
            
            if (overrun_error && !prev_overrun_error) begin
                overrun_error_count <= overrun_error_count + 1'b1;
                error_detected <= 1'b1;
                error_type <= 2'b10;
            end
            
            if (break_detected) begin
                break_count <= break_count + 1'b1;
                error_detected <= 1'b1;
                error_type <= 2'b11;
            end
            
            // Update previous states for edge detection
            prev_rx_valid <= rx_valid;
            prev_frame_error <= frame_error;
            prev_parity_error <= parity_error;
            prev_overrun_error <= overrun_error;
        end
    end
    
endmodule

`timescale 1ns/1ps

module uart_protocol_checker_tb();
    // Parameters
    parameter DATA_WIDTH = 8;
    parameter CLK_PERIOD = 10; // 10ns = 100MHz clock
    
    // Testbench signals
    reg clk;
    reg rst_n;
    reg rx_valid;
    reg [DATA_WIDTH-1:0] rx_data;
    reg frame_error;
    reg parity_error;
    reg overrun_error;
    reg clear_stats;
    
    // Output signals to monitor
    wire [7:0] frame_error_count;
    wire [7:0] parity_error_count;
    wire [7:0] overrun_error_count;
    wire [7:0] break_count;
    wire error_detected;
    wire [1:0] error_type;
    wire break_detected;
    wire [15:0] bytes_received;
    wire [15:0] packets_received;
    
    // Instantiate the module under test
    uart_protocol_checker #(
        .DATA_WIDTH(DATA_WIDTH)
    ) uut (
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
        .error_detected(error_detected),
        .error_type(error_type),
        .break_detected(break_detected),
        .bytes_received(bytes_received),
        .packets_received(packets_received),
        .clear_stats(clear_stats)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #(CLK_PERIOD/2) clk = ~clk;
    end
    
    // Test sequence counter and expected values for checking
    reg [7:0] test_seq;
    reg [7:0] expected_frame_errors;
    reg [7:0] expected_parity_errors;
    reg [7:0] expected_overrun_errors;
    reg [7:0] expected_breaks;
    reg [15:0] expected_bytes;
    reg [15:0] expected_packets;
    
    // Task for checking outputs
    task check_outputs;
        input [7:0] exp_frame_errs;
        input [7:0] exp_parity_errs;
        input [7:0] exp_overrun_errs;
        input [7:0] exp_breaks;
        input [15:0] exp_bytes;
        input [15:0] exp_packets;
        begin
            if (frame_error_count !== exp_frame_errs)
                $display("Error: frame_error_count = %d, expected %d", frame_error_count, exp_frame_errs);
            
            if (parity_error_count !== exp_parity_errs)
                $display("Error: parity_error_count = %d, expected %d", parity_error_count, exp_parity_errs);
                
            if (overrun_error_count !== exp_overrun_errs)
                $display("Error: overrun_error_count = %d, expected %d", overrun_error_count, exp_overrun_errs);
                
            if (break_count !== exp_breaks)
                $display("Error: break_count = %d, expected %d", break_count, exp_breaks);
                
            if (bytes_received !== exp_bytes)
                $display("Error: bytes_received = %d, expected %d", bytes_received, exp_bytes);
                
            if (packets_received !== exp_packets)
                $display("Error: packets_received = %d, expected %d", packets_received, exp_packets);
        end
    endtask
    
    // Task to send a byte with optional errors
    task send_byte;
        input [DATA_WIDTH-1:0] data;
        input has_frame_error;
        input has_parity_error;
        input has_overrun_error;
        begin
            rx_valid = 1'b1;
            rx_data = data;
            frame_error = has_frame_error;
            parity_error = has_parity_error;
            overrun_error = has_overrun_error;
            @(posedge clk);
            rx_valid = 1'b0;
            frame_error = 1'b0;
            parity_error = 1'b0;
            overrun_error = 1'b0;
            @(posedge clk);
        end
    endtask
    
    // Task to generate a break condition
    task generate_break;
        integer i;
        begin
            for (i = 0; i < 12; i = i + 1) begin
                rx_valid = 1'b1;
                rx_data = 8'h00;
                frame_error = 1'b1;
                @(posedge clk);
            end
            rx_valid = 1'b0;
            frame_error = 1'b0;
            @(posedge clk);
        end
    endtask
    
    // Task to generate packet delimiter
    task generate_packet_delimiter;
        integer i;
        begin
            for (i = 0; i < 4; i = i + 1) begin
                rx_valid = 1'b1;
                rx_data = 8'hFF;  // Idle character
                @(posedge clk);
            end
            rx_valid = 1'b0;
            @(posedge clk);
        end
    endtask
    
    // Testbench stimulus
    initial begin
        // Initialize
        rst_n = 0;
        rx_valid = 0;
        rx_data = 0;
        frame_error = 0;
        parity_error = 0;
        overrun_error = 0;
        clear_stats = 0;
        test_seq = 0;
        
        expected_frame_errors = 0;
        expected_parity_errors = 0;
        expected_overrun_errors = 0;
        expected_breaks = 0;
        expected_bytes = 0;
        expected_packets = 0;
        
        // Reset sequence
        repeat (5) @(posedge clk);
        rst_n = 1;
        repeat (5) @(posedge clk);
        
        // Test 1: Normal data reception
        $display("Test 1: Normal data reception");
        for (test_seq = 0; test_seq < 10; test_seq = test_seq + 1) begin
            send_byte(test_seq, 0, 0, 0);
            expected_bytes = expected_bytes + 1;
            repeat (2) @(posedge clk);
        end
        check_outputs(0, 0, 0, 0, 10, 0);
        
        // Test 2: Frame errors
        $display("Test 2: Frame errors");
        for (test_seq = 0; test_seq < 5; test_seq = test_seq + 1) begin
            send_byte(test_seq, 1, 0, 0);
            expected_bytes = expected_bytes + 1;
            expected_frame_errors = expected_frame_errors + 1;
            repeat (2) @(posedge clk);
        end
        check_outputs(5, 0, 0, 0, 15, 0);
        
        // Test 3: Parity errors
        $display("Test 3: Parity errors");
        for (test_seq = 0; test_seq < 3; test_seq = test_seq + 1) begin
            send_byte(test_seq, 0, 1, 0);
            expected_bytes = expected_bytes + 1;
            expected_parity_errors = expected_parity_errors + 1;
            repeat (2) @(posedge clk);
        end
        check_outputs(5, 3, 0, 0, 18, 0);
        
        // Test 4: Overrun errors
        $display("Test 4: Overrun errors");
        for (test_seq = 0; test_seq < 2; test_seq = test_seq + 1) begin
            send_byte(test_seq, 0, 0, 1);
            expected_bytes = expected_bytes + 1;
            expected_overrun_errors = expected_overrun_errors + 1;
            repeat (2) @(posedge clk);
        end
        check_outputs(5, 3, 2, 0, 20, 0);
        
        // Test 5: Break condition
        $display("Test 5: Break condition");
        generate_break();
        expected_breaks = expected_breaks + 1;
        repeat (5) @(posedge clk);
        check_outputs(5, 3, 2, 1, 20, 0);
        
        // Test 6: Packet detection
        $display("Test 6: Packet detection");
        // First packet
        generate_packet_delimiter();
        repeat (5) @(posedge clk);
        for (test_seq = 0; test_seq < 5; test_seq = test_seq + 1) begin
            send_byte(test_seq, 0, 0, 0);
            expected_bytes = expected_bytes + 1;
        end
        repeat (5) @(posedge clk);
        expected_packets = expected_packets + 1;
        
        // Second packet
        generate_packet_delimiter();
        repeat (5) @(posedge clk);
        for (test_seq = 0; test_seq < 5; test_seq = test_seq + 1) begin
            send_byte(test_seq, 0, 0, 0);
            expected_bytes = expected_bytes + 1;
        end
        repeat (5) @(posedge clk);
        expected_packets = expected_packets + 1;
        
        check_outputs(5, 3, 2, 1, 30, 2);
        
        // Test 7: Clear statistics
        $display("Test 7: Clear statistics");
        clear_stats = 1;
        @(posedge clk);
        clear_stats = 0;
        @(posedge clk);
        
        // Reset expected values
        expected_frame_errors = 0;
        expected_parity_errors = 0;
        expected_overrun_errors = 0;
        expected_breaks = 0;
        expected_bytes = 0;
        expected_packets = 0;
        
        check_outputs(0, 0, 0, 0, 0, 0);
        
        // Test 8: Mixed errors
        $display("Test 8: Mixed errors");
        send_byte(8'hA5, 1, 1, 0);  // Frame + parity error
        expected_bytes = expected_bytes + 1;
        expected_frame_errors = expected_frame_errors + 1;
        expected_parity_errors = expected_parity_errors + 1;
        repeat (2) @(posedge clk);
        
        send_byte(8'h5A, 1, 0, 1);  // Frame + overrun error
        expected_bytes = expected_bytes + 1;
        expected_frame_errors = expected_frame_errors + 1;
        expected_overrun_errors = expected_overrun_errors + 1;
        repeat (2) @(posedge clk);
        
        check_outputs(2, 1, 1, 0, 2, 0);
        
        // End of test
        repeat (10) @(posedge clk);
        $display("All tests completed successfully");
        $finish;
    end
    
    // Optional: Monitor important signals
    initial begin
        $monitor("Time=%0t: rx_valid=%b, rx_data=%h, errors=%b %b %b, counts=%d %d %d %d",
                 $time, rx_valid, rx_data, frame_error, parity_error, overrun_error,
                 frame_error_count, parity_error_count, overrun_error_count, break_count);
    end
    
endmodule
