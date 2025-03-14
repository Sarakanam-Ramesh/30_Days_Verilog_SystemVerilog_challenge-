`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 13.03.2025 22:25:03
// Design Name: 
// Module Name: Recovery_mechanism
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


module recovery_mechanism #(
    parameter DATA_WIDTH = 32,
    parameter NUM_RETRIES = 3,
    parameter BACKOFF_CYCLES = 10
)(
    input  logic                    clk,
    input  logic                    rst_n,
    // Transaction interface
    input  logic                    tx_valid,
    output logic                    tx_ready,
    input  logic [DATA_WIDTH-1:0]   tx_data,
    // Response interface
    output logic                    rx_valid,
    input  logic                    rx_ready,
    output logic [DATA_WIDTH-1:0]   rx_data,
    // Error interface
    input  logic                    error_detected,
    input  logic                    critical_error,
    // Status output
    output logic [1:0]              recovery_state,  // 0=normal, 1=retrying, 2=backoff, 3=failed
    output logic [2:0]              retry_count
);

    // State machine states
    typedef enum logic [2:0] {
        NORMAL,
        ERROR_DETECTED,
        RETRY,
        BACKOFF,
        FAILED
    } state_t;
    
    state_t state, next_state;
    
    // Registers for retry and backoff
    logic [$clog2(NUM_RETRIES)-1:0] retry_counter;
    logic [$clog2(BACKOFF_CYCLES)-1:0] backoff_counter;
    logic [DATA_WIDTH-1:0] saved_tx_data;
    
    // State machine
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= NORMAL;
            retry_counter <= '0;
            backoff_counter <= '0;
            saved_tx_data <= '0;
        end else begin
            state <= next_state;
            
            // Handle retry counter
            if (state == NORMAL) begin
                retry_counter <= '0;
            end else if (state == ERROR_DETECTED && next_state == RETRY) begin
                retry_counter <= retry_counter + 1'b1;
            end
            
            // Handle backoff counter
            if (state != BACKOFF) begin
                backoff_counter <= BACKOFF_CYCLES - 1;
            end else if (backoff_counter > 0) begin
                backoff_counter <= backoff_counter - 1'b1;
            end
            
            // Save transaction data when valid
            if (state == NORMAL && tx_valid && tx_ready) begin
                saved_tx_data <= tx_data;
            end
        end
    end
    
    // Next state logic
    always_comb begin
        next_state = state;
        
        case (state)
            NORMAL: begin
                if (error_detected) begin
                    next_state = ERROR_DETECTED;
                end
            end
            
            ERROR_DETECTED: begin
                if (critical_error) begin
                    next_state = FAILED;
                end else if (retry_counter < NUM_RETRIES - 1) begin
                    next_state = RETRY;
                end else begin
                    next_state = FAILED;
                end
            end
            
            RETRY: begin
                next_state = BACKOFF;
            end
            
            BACKOFF: begin
                if (backoff_counter == 0) begin
                    next_state = NORMAL;
                end
            end
            
            FAILED: begin
                // Stay in FAILED state until reset
                next_state = FAILED;
            end
            
            default: next_state = NORMAL;
        endcase
    end
    
    // Output logic
    always_comb begin
        // Default values
        tx_ready = 1'b0;
        rx_valid = 1'b0;
        rx_data = saved_tx_data;
        
        // Output recovery state
        recovery_state = 2'd0;  // normal
        retry_count = retry_counter;
        
        case (state)
            NORMAL: begin
                tx_ready = 1'b1;  // Ready to accept new transactions
                recovery_state = 2'd0;  // normal
            end
            
            RETRY, ERROR_DETECTED: begin
                recovery_state = 2'd1;  // retrying
            end
            
            BACKOFF: begin
                recovery_state = 2'd2;  // backoff
            end
            
            FAILED: begin
                recovery_state = 2'd3;  // failed
                rx_valid = 1'b1;        // Signal completion (with error)
            end
            
            default: begin
                tx_ready = 1'b1;
                recovery_state = 2'd0;
            end
        endcase
    end

endmodule

`timescale 1ns/1ps

module recovery_mechanism_tb;
    // Parameters
    localparam DATA_WIDTH = 32;
    localparam NUM_RETRIES = 3;
    localparam BACKOFF_CYCLES = 10;
    localparam CLK_PERIOD = 10; // 10ns = 100MHz
    
    // Signals
    logic clk;
    logic rst_n;
    logic tx_valid;
    logic tx_ready;
    logic [DATA_WIDTH-1:0] tx_data;
    logic rx_valid;
    logic rx_ready;
    logic [DATA_WIDTH-1:0] rx_data;
    logic error_detected;
    logic critical_error;
    logic [1:0] recovery_state;
    logic [2:0] retry_count;
    
    // Test transaction counter
    int transaction_count;
    
    // Instantiate DUT
    recovery_mechanism #(
        .DATA_WIDTH(DATA_WIDTH),
        .NUM_RETRIES(NUM_RETRIES),
        .BACKOFF_CYCLES(BACKOFF_CYCLES)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .tx_valid(tx_valid),
        .tx_ready(tx_ready),
        .tx_data(tx_data),
        .rx_valid(rx_valid),
        .rx_ready(rx_ready),
        .rx_data(rx_data),
        .error_detected(error_detected),
        .critical_error(critical_error),
        .recovery_state(recovery_state),
        .retry_count(retry_count)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #(CLK_PERIOD/2) clk = ~clk;
    end
    
    // Translate recovery state to string for readability
    function automatic string state_to_string(logic [1:0] state);
        case (state)
            2'd0: return "NORMAL";
            2'd1: return "RETRYING";
            2'd2: return "BACKOFF";
            2'd3: return "FAILED";
            default: return "UNKNOWN";
        endcase
    endfunction
    
    // Test sequence
    initial begin
        // Initialize signals
        rst_n = 0;
        tx_valid = 0;
        tx_data = '0;
        rx_ready = 1; // Always ready to receive
        error_detected = 0;
        critical_error = 0;
        transaction_count = 0;
        
        // Apply reset
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
        
        // Test case 1: Successful transaction
        $display("Test case 1: Successful transaction");
        tx_data = 32'hABCD1234;
        tx_valid = 1;
        wait(tx_ready);
        @(posedge clk);
        tx_valid = 0;
        
        // Wait for completion
        repeat(5) @(posedge clk);
        
        // Test case 2: Recoverable error with retries
        $display("Test case 2: Recoverable error with retries");
        tx_data = 32'h55AA55AA;
        tx_valid = 1;
        wait(tx_ready);
        @(posedge clk);
        tx_valid = 0;
        
        // Inject error after a few cycles
        repeat(3) @(posedge clk);
        error_detected = 1;
        @(posedge clk);
        error_detected = 0;
        
        // Let it go through retry and backoff cycles
        repeat(BACKOFF_CYCLES * 2) @(posedge clk);
        
        // Test case 3: Multiple errors with recovery
        $display("Test case 3: Multiple errors with eventual recovery");
        tx_data = 32'hDEADBEEF;
        tx_valid = 1;
        wait(tx_ready);
        @(posedge clk);
        tx_valid = 0;
        
        // Inject error multiple times
        for (int i = 0; i < NUM_RETRIES-1; i++) begin
            // Wait a bit then inject error
            repeat(5) @(posedge clk);
            error_detected = 1;
            @(posedge clk);
            error_detected = 0;
            
            // Let it go through retry and some backoff
            repeat(BACKOFF_CYCLES) @(posedge clk);
        end
        
        // Wait for system to return to normal
        wait(recovery_state == 2'd0);
        repeat(5) @(posedge clk);
        
        // Test case 4: Critical error (unrecoverable)
        $display("Test case 4: Critical error (unrecoverable)");
        tx_data = 32'h12345678;
        tx_valid = 1;
        wait(tx_ready);
        @(posedge clk);
        tx_valid = 0;
        
        // Inject critical error
        repeat(3) @(posedge clk);
        error_detected = 1;
        critical_error = 1;
        @(posedge clk);
        error_detected = 0;
        critical_error = 0;
        
        // Wait for failure state
        wait(recovery_state == 2'd3);
        repeat(5) @(posedge clk);
        
        // Reset to recover from critical error
        rst_n = 0;
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(5) @(posedge clk);
        
        // End simulation
        $display("Simulation complete");
        $finish;
    end
    
    // Monitor recovery process
    always @(posedge clk) begin
        if (recovery_state != 2'd0) begin
            $display("Time %0t: Recovery state = %s, Retry count = %0d", 
                     $time, state_to_string(recovery_state), retry_count);
        end
        
        if (tx_valid && tx_ready) begin
            transaction_count++;
            $display("Time %0t: Transaction %0d started, Data = %h", 
                     $time, transaction_count, tx_data);
        end
        
        if (rx_valid && rx_ready) begin
            $display("Time %0t: Transaction completed, Data = %h", 
                     $time, rx_data);
        end
    end
    
endmodule