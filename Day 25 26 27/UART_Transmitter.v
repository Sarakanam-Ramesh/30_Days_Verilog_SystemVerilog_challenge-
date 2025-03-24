`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 23.03.2025 10:56:41
// Design Name: 
// Module Name: UART_Transmitter
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


module uart_tx #(
    parameter DATA_WIDTH = 8,
    parameter STOP_BITS = 1,
    parameter PARITY_EN = 0,   // 0 = No parity, 1 = Even parity, 2 = Odd parity
    parameter BAUD_DIV = 0     // 0 = External baud rate, other values = clock divider
) (
    input wire clk,                     // System clock
    input wire rst_n,                   // Active low reset
    input wire tx_start,                // Start transmission signal
    input wire [DATA_WIDTH-1:0] tx_data,// Data to transmit
    input wire baud_tick,               // Tick from baud rate generator (ignored if BAUD_DIV > 0)
    output reg tx,                      // Serial output
    output reg tx_busy,                 // High when transmitting
    output reg tx_done                  // Pulses high when transmission completes
);

    // State definitions
    localparam IDLE = 2'b00;
    localparam START = 2'b01;
    localparam DATA = 2'b10;
    localparam PARITY = 2'b11;
    localparam STOP = 3'b100;
    
    // Internal registers
    reg [1:0] state, next_state;
    reg [DATA_WIDTH-1:0] tx_shift_reg;
    reg [3:0] bit_count;
    reg [3:0] stop_bit_count;
    reg parity_bit;
    
    // Baud rate generation (if internal)
    reg [15:0] baud_counter;
    wire baud_pulse;
    
    generate
        if (BAUD_DIV > 0) begin
            // Internal baud rate generator
            always @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    baud_counter <= 0;
                end else begin
                    if (baud_counter >= BAUD_DIV - 1) begin
                        baud_counter <= 0;
                    end else begin
                        baud_counter <= baud_counter + 1'b1;
                    end
                end
            end
            assign baud_pulse = (baud_counter == 0);
        end else begin
            // External baud rate generator
            assign baud_pulse = baud_tick;
        end
    endgenerate
    
    // State machine - Next state logic
    always @(*) begin
        next_state = state;
        
        case (state)
            IDLE: begin
                if (tx_start)
                    next_state = START;
            end
            
            START: begin
                if (baud_pulse)
                    next_state = DATA;
            end
            
            DATA: begin
                if (baud_pulse && bit_count == DATA_WIDTH - 1)
                    next_state = (PARITY_EN > 0) ? PARITY : STOP;
            end
            
            PARITY: begin
                if (baud_pulse)
                    next_state = STOP;
            end
            
            STOP: begin
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
            tx <= 1'b1;              // Idle state is high
            tx_shift_reg <= 0;
            bit_count <= 0;
            stop_bit_count <= 0;
            parity_bit <= 0;
            tx_busy <= 0;
            tx_done <= 0;
        end else begin
            tx_done <= 0;  // Default, pulse only for one cycle
            
            case (state)
                IDLE: begin
                    tx <= 1'b1;  // Idle state is high
                    tx_busy <= 0;
                    
                    if (tx_start) begin
                        tx_shift_reg <= tx_data;
                        tx_busy <= 1'b1;
                        // Calculate parity if needed
                        if (PARITY_EN == 1) begin
                            // Even parity
                            parity_bit <= ^tx_data;
                        end else if (PARITY_EN == 2) begin
                            // Odd parity
                            parity_bit <= ~(^tx_data);
                        end
                    end
                end
                
                START: begin
                    tx <= 1'b0;  // Start bit is low
                    tx_busy <= 1'b1;
                    bit_count <= 0;
                    stop_bit_count <= 0;
                    
                    if (baud_pulse) begin
                        // Prepare for data transmission
                    end
                end
                
                DATA: begin
                    tx <= tx_shift_reg[0];  // LSB first
                    tx_busy <= 1'b1;
                    
                    if (baud_pulse) begin
                        tx_shift_reg <= {1'b0, tx_shift_reg[DATA_WIDTH-1:1]};
                        if (bit_count < DATA_WIDTH - 1) begin
                            bit_count <= bit_count + 1'b1;
                        end
                    end
                end
                
                PARITY: begin
                    tx <= parity_bit;
                    tx_busy <= 1'b1;
                end
                
                STOP: begin
                    tx <= 1'b1;  // Stop bit is high
                    tx_busy <= 1'b1;
                    
                    if (baud_pulse) begin
                        if (stop_bit_count < STOP_BITS - 1) begin
                            stop_bit_count <= stop_bit_count + 1'b1;
                        end else begin
                            tx_done <= 1'b1;  // Transmission complete
                        end
                    end
                end
                
                default: tx <= 1'b1;
            endcase
        end
    end
    
endmodule

`timescale 1ns / 1ps

module uart_tx_tb();
    // Parameters
    parameter CLK_PERIOD = 20;  // 50 MHz clock
    parameter DATA_WIDTH = 8;
    parameter STOP_BITS = 1;
    parameter PARITY_EN = 0;
    parameter BAUD_RATE = 9600;
    parameter BIT_PERIOD = 1000000000 / BAUD_RATE;  // ns
    
    // Test data
    parameter [DATA_WIDTH-1:0] TEST_DATA1 = 8'h55;  // Alternating 0101...
    parameter [DATA_WIDTH-1:0] TEST_DATA2 = 8'hAA;  // Alternating 1010...
    parameter [DATA_WIDTH-1:0] TEST_DATA3 = 8'hFF;  // All ones
    parameter [DATA_WIDTH-1:0] TEST_DATA4 = 8'h00;  // All zeros
    
    // Calculated baud divider (assuming 16x oversample)
    parameter BAUD_DIV = 50000000 / (BAUD_RATE * 16);
    
    // Signals
    reg clk;
    reg rst_n;
    reg tx_start;
    reg [DATA_WIDTH-1:0] tx_data;
    reg baud_tick;
    wire tx;
    wire tx_busy;
    wire tx_done;
    
    // Baud counter for external baud generation
    reg [15:0] baud_counter;
    
    // Instantiate DUT
    uart_tx #(
        .DATA_WIDTH(DATA_WIDTH),
        .STOP_BITS(STOP_BITS),
        .PARITY_EN(PARITY_EN),
        .BAUD_DIV(0)  // External baud rate
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .tx_start(tx_start),
        .tx_data(tx_data),
        .baud_tick(baud_tick),
        .tx(tx),
        .tx_busy(tx_busy),
        .tx_done(tx_done)
    );
    
    // Clock generation
    always begin
        #(CLK_PERIOD/2) clk = ~clk;
    end
    
    // Baud tick generation (16x oversample)
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            baud_counter <= 0;
            baud_tick <= 0;
        end else begin
            if (baud_counter >= BAUD_DIV - 1) begin
                baud_counter <= 0;
                baud_tick <= 1;
            end else begin
                baud_counter <= baud_counter + 1;
                baud_tick <= 0;
            end
        end
    end
    
    // Monitor TX output
    reg [DATA_WIDTH-1:0] received_data;
    reg receiving;
    integer bit_position;
    integer sample_point;
    
    // Task to receive data serially
    task receive_uart;
        begin
            receiving = 1;
            
            // Wait for start bit (falling edge)
            @(negedge tx);
            
            // Delay to middle of start bit
            #(BIT_PERIOD/2);
            
            // Verify start bit is low
            if (tx != 0) begin
                $display("ERROR: Invalid start bit detected!");
            end
            
            // Initialize data
            received_data = 0;
            
            // Sample each data bit
            for (bit_position = 0; bit_position < DATA_WIDTH; bit_position = bit_position + 1) begin
                // Delay to middle of bit
                #BIT_PERIOD;
                
                // Sample bit
                received_data[bit_position] = tx;
            end
            
            // Check parity bit if enabled
            if (PARITY_EN > 0) begin
                #BIT_PERIOD;
                // Could verify parity here
            end
            
            // Verify stop bit(s)
            for (bit_position = 0; bit_position < STOP_BITS; bit_position = bit_position + 1) begin
                #BIT_PERIOD;
                if (tx != 1) begin
                    $display("ERROR: Invalid stop bit detected!");
                end
            end
            
            receiving = 0;
            $display("Received data: 0x%h", received_data);
        end
    endtask
    
    // Test sequence
    initial begin
        // Initialize
        clk = 0;
        rst_n = 0;
        tx_start = 0;
        tx_data = 0;
        receiving = 0;
        
        // Apply reset
        #(CLK_PERIOD * 10);
        rst_n = 1;
        #(CLK_PERIOD * 10);
        
        // Test 1: Send first test data
        $display("Test 1: Sending data 0x%h", TEST_DATA1);
        tx_data = TEST_DATA1;
        tx_start = 1;
        #(CLK_PERIOD);
        tx_start = 0;
        
        // Monitor the transmission
        receive_uart();
        
        // Verify received data
        if (received_data !== TEST_DATA1) begin
            $display("ERROR: Data mismatch! Expected 0x%h, Got 0x%h", TEST_DATA1, received_data);
        end else begin
            $display("PASS: Data correctly transmitted");
        end
        
        // Wait for transmitter to become idle
        wait(!tx_busy);
        #(BIT_PERIOD * 2);
        
        // Test 2: Send second test data
        $display("Test 2: Sending data 0x%h", TEST_DATA2);
        tx_data = TEST_DATA2;
        tx_start = 1;
        #(CLK_PERIOD);
        tx_start = 0;
        
        // Monitor the transmission
        receive_uart();
        
        // Verify received data
        if (received_data !== TEST_DATA2) begin
            $display("ERROR: Data mismatch! Expected 0x%h, Got 0x%h", TEST_DATA2, received_data);
        end else begin
            $display("PASS: Data correctly transmitted");
        end
        
        // Wait for transmitter to become idle
        wait(!tx_busy);
        #(BIT_PERIOD * 2);
        
        // Test 3: Send third test data
        $display("Test 3: Sending data 0x%h", TEST_DATA3);
        tx_data = TEST_DATA3;
        tx_start = 1;
        #(CLK_PERIOD);
        tx_start = 0;
        
        // Monitor the transmission
        receive_uart();
        
        // Verify received data
        if (received_data !== TEST_DATA3) begin
            $display("ERROR: Data mismatch! Expected 0x%h, Got 0x%h", TEST_DATA3, received_data);
        end else begin
            $display("PASS: Data correctly transmitted");
        end
        
        // Wait for transmitter to become idle
        wait(!tx_busy);
        #(BIT_PERIOD * 2);
        
        // Test 4: Send fourth test data
        $display("Test 4: Sending data 0x%h", TEST_DATA4);
        tx_data = TEST_DATA4;
        tx_start = 1;
        #(CLK_PERIOD);
        tx_start = 0;
        
        // Monitor the transmission
        receive_uart();
        
        // Verify received data
        if (received_data !== TEST_DATA4) begin
            $display("ERROR: Data mismatch! Expected 0x%h, Got 0x%h", TEST_DATA4, received_data);
        end else begin
            $display("PASS: Data correctly transmitted");
        end
        
        // Test completion
        #(BIT_PERIOD * 10);
        $display("All tests completed");
        $finish;
    end
    
    // Optional waveform dumping for simulation
    initial begin
        $dumpfile("uart_tx_tb.vcd");
        $dumpvars(0, uart_tx_tb);
    end
    
endmodule
