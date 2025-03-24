`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 23.03.2025 10:59:02
// Design Name: 
// Module Name: UART_Reciever
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


module uart_rx #(
    parameter DATA_WIDTH = 8,
    parameter STOP_BITS = 1,
    parameter PARITY_EN = 0,   // 0 = No parity, 1 = Even parity, 2 = Odd parity
    parameter BAUD_DIV = 0,    // 0 = External baud rate, other values = clock divider
    parameter SAMPLE_RATE = 16 // Oversampling rate
) (
    input wire clk,                     // System clock
    input wire rst_n,                   // Active low reset
    input wire rx,                      // Serial input
    input wire baud_tick,               // Tick from baud rate generator (ignored if BAUD_DIV > 0)
    output reg [DATA_WIDTH-1:0] rx_data,// Received data
    output reg rx_valid,                // Pulses high when new data is available
    output reg frame_error,             // High on frame error (invalid stop bit)
    output reg parity_error,            // High on parity error (if parity enabled)
    output reg overrun_error            // High if new data received before previous read
);

    // State definitions
    localparam IDLE = 3'b000;
    localparam START = 3'b001;
    localparam DATA = 3'b010;
    localparam PARITY = 3'b011;
    localparam STOP = 3'b100;
    
    // Internal registers
    reg [2:0] state, next_state;
    reg [DATA_WIDTH-1:0] rx_shift_reg;
    reg [3:0] bit_count;
    reg [3:0] stop_bit_count;
    reg [4:0] sample_count;  // For oversampling
    reg calculated_parity;
    reg rx_data_ready;
    
    // Synchronize the rx input to prevent metastability
    reg rx_sync1, rx_sync2;
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rx_sync1 <= 1'b1;
            rx_sync2 <= 1'b1;
        end else begin
            rx_sync1 <= rx;
            rx_sync2 <= rx_sync1;
        end
    end
    
    // Baud rate generation (if internal) and oversampling
    reg [15:0] baud_counter;
    wire baud_pulse;
    wire sample_pulse;
    
    generate
        if (BAUD_DIV > 0) begin
            // Internal baud rate generator with oversampling
            always @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    baud_counter <= 0;
                end else begin
                    if (baud_counter >= (BAUD_DIV / SAMPLE_RATE) - 1) begin
                        baud_counter <= 0;
                    end else begin
                        baud_counter <= baud_counter + 1'b1;
                    end
                end
            end
            assign sample_pulse = (baud_counter == 0);
            
            // Divide sample pulse to get baud pulse (for bit timing)
            reg [7:0] sample_counter;
            always @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    sample_counter <= 0;
                end else if (sample_pulse) begin
                    if (sample_counter >= SAMPLE_RATE - 1) begin
                        sample_counter <= 0;
                    end else begin
                        sample_counter <= sample_counter + 1'b1;
                    end
                end
            end
            assign baud_pulse = sample_pulse && (sample_counter == 0);
        end else begin
            // External baud rate generator
            assign sample_pulse = baud_tick;
            
            // Create baud pulse from external sample_pulse
            reg [7:0] sample_counter;
            always @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    sample_counter <= 0;
                end else if (sample_pulse) begin
                    if (sample_counter >= SAMPLE_RATE - 1) begin
                        sample_counter <= 0;
                    end else begin
                        sample_counter <= sample_counter + 1'b1;
                    end
                end
            end
            assign baud_pulse = sample_pulse && (sample_counter == 0);
        end
    endgenerate
    
    // Noise filter for rx (majority vote)
    reg [2:0] rx_filter;
    reg rx_filtered;
    
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rx_filter <= 3'b111;
            rx_filtered <= 1'b1;
        end else if (sample_pulse) begin
            rx_filter <= {rx_filter[1:0], rx_sync2};
            rx_filtered <= (rx_filter[2] & rx_filter[1]) | 
                           (rx_filter[2] & rx_filter[0]) | 
                           (rx_filter[1] & rx_filter[0]);
        end
    end
    
    // State machine - Next state logic
    always @(*) begin
        next_state = state;
        
        case (state)
            IDLE: begin
                // Detect start bit (falling edge)
                if (sample_pulse && !rx_filtered)
                    next_state = START;
            end
            
            START: begin
                // Confirm it's a valid start bit (sample in the middle)
                if (sample_pulse && sample_count == (SAMPLE_RATE/2) - 1) begin
                    if (rx_filtered)  // Not a valid start bit
                        next_state = IDLE;
                    else              // Valid start bit, get ready for data
                        next_state = DATA;
                end
            end
            
            DATA: begin
                // Capture data bits
                if (baud_pulse && bit_count == DATA_WIDTH - 1)
                    next_state = (PARITY_EN > 0) ? PARITY : STOP;
            end
            
            PARITY: begin
                // Check parity bit
                if (baud_pulse)
                    next_state = STOP;
            end
            
            STOP: begin
                // Verify stop bits
                if (baud_pulse && stop_bit_count == STOP_BITS - 1)
                    next_state = IDLE;
            end
            
            default: next_state = IDLE;
        endcase
    end
    
    // State machine - State register
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
        end else begin
            state <= next_state;
        end
    end
    
    // Data path logic
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            rx_shift_reg <= 0;
            rx_data <= 0;
            rx_valid <= 0;
            frame_error <= 0;
            parity_error <= 0;
            overrun_error <= 0;
            bit_count <= 0;
            stop_bit_count <= 0;
            sample_count <= 0;
            calculated_parity <= 0;
            rx_data_ready <= 0;
        end else begin
            rx_valid <= 0;  // Default, pulse only for one cycle
            
            // Handle sample counting for oversampling
            if (sample_pulse) begin
                if (state == IDLE) begin
                    sample_count <= 0;
                end else begin
                    sample_count <= sample_count + 1'b1;
                    if (sample_count >= SAMPLE_RATE - 1)
                        sample_count <= 0;
                end
            end
            
            case (state)
                IDLE: begin
                    frame_error <= 0;
                    parity_error <= 0;
                    
                    // If we have received new data and it hasn't been read
                    if (rx_data_ready && rx_valid) begin
                        overrun_error <= 1'b1;
                    end
                    
                    // When transition to START is detected
                    if (next_state == START) begin
                        bit_count <= 0;
                        stop_bit_count <= 0;
                        calculated_parity <= 0;
                    end
                end
                
                START: begin
                    // Wait for middle of start bit to confirm
                end
                
                DATA: begin
                    // Sample in the middle of each bit
                    if (sample_pulse && sample_count == (SAMPLE_RATE/2) - 1) begin
                        rx_shift_reg <= {rx_filtered, rx_shift_reg[DATA_WIDTH-1:1]};
                        
                        // Calculate parity as we go
                        if (PARITY_EN == 1) begin
                            // Even parity
                            calculated_parity <= calculated_parity ^ rx_filtered;
                        end else if (PARITY_EN == 2) begin
                            // Odd parity
                            calculated_parity <= calculated_parity ^ rx_filtered;
                        end
                    end
                    
                    // Count bits at the baud rate
                    if (baud_pulse) begin
                        if (bit_count < DATA_WIDTH - 1) begin
                            bit_count <= bit_count + 1'b1;
                        end
                    end
                end
                
                PARITY: begin
                    // Check parity in middle of bit
                    if (sample_pulse && sample_count == (SAMPLE_RATE/2) - 1) begin
                        if (PARITY_EN == 1) begin
                            // Even parity (should result in even number of 1s)
                            parity_error <= calculated_parity != rx_filtered;
                        end else if (PARITY_EN == 2) begin
                            // Odd parity (should result in odd number of 1s)
                            parity_error <= calculated_parity == rx_filtered;
                        end
                    end
                end
                
                STOP: begin
                    // Check for valid stop bit
                    if (sample_pulse && sample_count == (SAMPLE_RATE/2) - 1) begin
                        if (!rx_filtered) begin
                            frame_error <= 1'b1;  // Stop bit should be high
                        end
                    end
                    
                    // Process stop bits
                    if (baud_pulse) begin
                        if (stop_bit_count < STOP_BITS - 1) begin
                            stop_bit_count <= stop_bit_count + 1'b1;
                        end else begin
                            // Data reception complete
                            rx_data <= rx_shift_reg;
                            rx_valid <= 1'b1;
                            rx_data_ready <= 1'b1;
                            overrun_error <= 0;  // Clear for new reception
                        end
                    end
                end
                
                default: begin
                    // Nothing to do
                end
            endcase
        end
    end
    
endmodule

`timescale 1ns / 1ps

module uart_rx_tb();
    // Parameters
    parameter CLK_PERIOD = 20;  // 50 MHz clock
    parameter DATA_WIDTH = 8;
    parameter STOP_BITS = 1;
    parameter PARITY_EN = 0;
    parameter BAUD_RATE = 9600;
    parameter BIT_PERIOD = 1000000000 / BAUD_RATE;  // ns
    parameter SAMPLE_RATE = 16;
    
    // Test data
    parameter [DATA_WIDTH-1:0] TEST_DATA1 = 8'h55;  // Alternating 0101...
    parameter [DATA_WIDTH-1:0] TEST_DATA2 = 8'hAA;  // Alternating 1010...
    parameter [DATA_WIDTH-1:0] TEST_DATA3 = 8'hFF;  // All ones
    parameter [DATA_WIDTH-1:0] TEST_DATA4 = 8'h00;  // All zeros
    
    // Calculated baud divider
    parameter BAUD_DIV = 50000000 / (BAUD_RATE * SAMPLE_RATE);
    
    // Signals
    reg clk;
    reg rst_n;
    reg rx;
    reg baud_tick;
    wire [DATA_WIDTH-1:0] rx_data;
    wire rx_valid;
    wire frame_error;
    wire parity_error;
    wire overrun_error;
    
    // Baud counter for external baud generation
    reg [15:0] baud_counter;
        integer i;
    
    // Instantiate DUT
    uart_rx #(
        .DATA_WIDTH(DATA_WIDTH),
        .STOP_BITS(STOP_BITS),
        .PARITY_EN(PARITY_EN),
        .BAUD_DIV(0),  // External baud rate
        .SAMPLE_RATE(SAMPLE_RATE)
    ) dut (
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
    
    // Clock generation
    always begin
        #(CLK_PERIOD/2) clk = ~clk;
    end
    
    // Baud tick generation (oversample)
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            baud_counter <= 0;
            baud_tick <= 0;
        end else begin
            if (baud_counter >= (BAUD_DIV / SAMPLE_RATE) - 1) begin
                baud_counter <= 0;
                baud_tick <= 1;
            end else begin
                baud_counter <= baud_counter + 1;
                baud_tick <= 0;
            end
        end
    end
    
    // Task to send data serially
    task send_uart;
        input [DATA_WIDTH-1:0] data;
        reg parity;
        begin
            // Calculate parity if enabled
            parity = 0;
            if (PARITY_EN == 1) begin
                // Even parity
                parity = ^data;
            end else if (PARITY_EN == 2) begin
                // Odd parity
                parity = ~(^data);
            end
            
            // Start bit (low)
            rx = 1'b0;
            #BIT_PERIOD;
            
            // Data bits (LSB first)
            for (i = 0; i < DATA_WIDTH; i = i + 1) begin
                rx = data[i];
                #BIT_PERIOD;
            end
            
            // Parity bit if enabled
            if (PARITY_EN > 0) begin
                rx = parity;
                #BIT_PERIOD;
            end
            
            // Stop bit(s) (high)
            for (i = 0; i < STOP_BITS; i = i + 1) begin
                rx = 1'b1;
                #BIT_PERIOD;
            end
            
            $display("Sent data: 0x%h", data);
        end
    endtask
    
    // Task to verify received data
    task verify_reception;
        input [DATA_WIDTH-1:0] expected_data;
        begin
            // Wait for data valid
            @(posedge rx_valid);
            
            // Verify data
            if (rx_data !== expected_data) begin
                $display("ERROR: Data mismatch! Expected 0x%h, Got 0x%h", expected_data, rx_data);
            end else begin
                $display("PASS: Data correctly received");
            end
            
            // Check for errors
            if (frame_error) $display("ERROR: Frame error detected!");
            if (parity_error) $display("ERROR: Parity error detected!");
            if (overrun_error) $display("ERROR: Overrun error detected!");
            
            // Wait a bit before next test
            #(BIT_PERIOD * 2);
        end
    endtask
    
    // Test sequence
    initial begin
        // Initialize
        clk = 0;
        rst_n = 0;
        rx = 1;  // Idle state is high
        
        // Apply reset
        #(CLK_PERIOD * 10);
        rst_n = 1;
        #(CLK_PERIOD * 10);
        
        // Test 1: Send first test data
        $display("Test 1: Sending data 0x%h", TEST_DATA1);
        fork
            send_uart(TEST_DATA1);
            verify_reception(TEST_DATA1);
        join
        
        // Test 2: Send second test data
        $display("Test 2: Sending data 0x%h", TEST_DATA2);
        fork
            send_uart(TEST_DATA2);
            verify_reception(TEST_DATA2);
        join
        
        // Test 3: Send third test data
        $display("Test 3: Sending data 0x%h", TEST_DATA3);
        fork
            send_uart(TEST_DATA3);
            verify_reception(TEST_DATA3);
        join
        
        // Test 4: Send fourth test data
        $display("Test 4: Sending data 0x%h", TEST_DATA4);
        fork
            send_uart(TEST_DATA4);
            verify_reception(TEST_DATA4);
        join
        
        // Test 5: Frame error test (missing stop bit)
        $display("Test 5: Frame error test");
        rx = 1'b0;  // Start bit
        #BIT_PERIOD;
        
        // Data bits (all ones)
        for (i = 0; i < DATA_WIDTH; i = i + 1) begin
            rx = 1'b1;
            #BIT_PERIOD;
        end
        
        // Missing stop bit (set to 0 instead of 1)
        rx = 1'b0;
        #BIT_PERIOD;
        
        // Return to idle
        rx = 1'b1;
        #(BIT_PERIOD * 2);
        
        if (!frame_error) begin
            $display("ERROR: Frame error not detected!");
        end else begin
            $display("PASS: Frame error correctly detected");
        end
        
        // Test completion
        #(BIT_PERIOD * 10);
        $display("All tests completed");
        $finish;
    end
    
    // Optional waveform dumping for simulation
    initial begin
        $dumpfile("uart_rx_tb.vcd");
        $dumpvars(0, uart_rx_tb);
    end
    
endmodule
