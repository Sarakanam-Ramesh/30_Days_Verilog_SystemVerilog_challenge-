`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 13.03.2025 14:56:03
// Design Name: 
// Module Name: Singleton_logger
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


// Synthesizable Singleton Logger
// Implements a centralized logging module that can be accessed from multiple places

module LoggerModule (
  input logic clk,
  input logic rst_n,
  
  // Configuration interface
  input logic config_valid,
  input logic [1:0] config_log_level,  // 0=OFF, 1=ERROR, 2=WARNING, 3=INFO
  
  // Logger client interface 1
  input logic client1_log_valid,
  input logic [1:0] client1_log_type,  // 0=INFO, 1=WARNING, 2=ERROR
  input logic [7:0] client1_log_data,
  output logic client1_log_ack,
  
  // Logger client interface 2
  input logic client2_log_valid,
  input logic [1:0] client2_log_type,
  input logic [7:0] client2_log_data,
  output logic client2_log_ack,
  
  // Logger output interface (could connect to UART, memory, etc.)
  output logic log_entry_valid,
  output logic [1:0] log_entry_type,
  output logic [7:0] log_entry_data,
  output logic [15:0] log_count
);

  // Logger state and configuration
  typedef enum logic [1:0] {
    LOG_LEVEL_OFF     = 2'b00,
    LOG_LEVEL_ERROR   = 2'b01,
    LOG_LEVEL_WARNING = 2'b10,
    LOG_LEVEL_INFO    = 2'b11
  } log_level_t;
  
  // Singleton instance state
  log_level_t current_log_level;
  logic [15:0] log_counter;
  
  // Client arbiter state
  typedef enum logic [1:0] {
    IDLE = 2'b00,
    CLIENT1_ACTIVE = 2'b01,
    CLIENT2_ACTIVE = 2'b10
  } arbiter_state_t;
  
  arbiter_state_t arbiter_state;
  
  // Configuration logic
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_log_level <= LOG_LEVEL_OFF;
    end else if (config_valid) begin
      current_log_level <= log_level_t'(config_log_level);
    end
  end
  
  // Log counter
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      log_counter <= 16'h0000;
    end else if (log_entry_valid) begin
      log_counter <= log_counter + 16'h0001;
    end
  end
  
  // Client arbitration and logging logic
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      arbiter_state <= IDLE;
      client1_log_ack <= 1'b0;
      client2_log_ack <= 1'b0;
      log_entry_valid <= 1'b0;
      log_entry_type <= 2'b00;
      log_entry_data <= 8'h00;
    end else begin
      // Default values
      client1_log_ack <= 1'b0;
      client2_log_ack <= 1'b0;
      log_entry_valid <= 1'b0;
      
      case (arbiter_state)
        IDLE: begin
          // Priority to client 1
          if (client1_log_valid) begin
            // Check if log type passes the current log level filter
            if ((current_log_level == LOG_LEVEL_ERROR && client1_log_type == 2'b10) ||
                (current_log_level == LOG_LEVEL_WARNING && client1_log_type >= 2'b01) ||
                (current_log_level == LOG_LEVEL_INFO)) begin
              
              arbiter_state <= CLIENT1_ACTIVE;
              log_entry_valid <= 1'b1;
              log_entry_type <= client1_log_type;
              log_entry_data <= client1_log_data;
              client1_log_ack <= 1'b1;
            end else begin
              // Log level filtered, just acknowledge
              client1_log_ack <= 1'b1;
            end
          end else if (client2_log_valid) begin
            // Check if log type passes the current log level filter
            if ((current_log_level == LOG_LEVEL_ERROR && client2_log_type == 2'b10) ||
                (current_log_level == LOG_LEVEL_WARNING && client2_log_type >= 2'b01) ||
                (current_log_level == LOG_LEVEL_INFO)) begin
              
              arbiter_state <= CLIENT2_ACTIVE;
              log_entry_valid <= 1'b1;
              log_entry_type <= client2_log_type;
              log_entry_data <= client2_log_data;
              client2_log_ack <= 1'b1;
            end else begin
              // Log level filtered, just acknowledge
              client2_log_ack <= 1'b1;
            end
          end
        end
        
        CLIENT1_ACTIVE: begin
          // Return to idle after one cycle
          arbiter_state <= IDLE;
        end
        
        CLIENT2_ACTIVE: begin
          // Return to idle after one cycle
          arbiter_state <= IDLE;
        end
        
        default: begin
          arbiter_state <= IDLE;
        end
      endcase
    end
  end
  
  // Output the current log count
  assign log_count = log_counter;

endmodule

// Example client module that uses the logger
module LoggerClient (
  input logic clk,
  input logic rst_n,
  input logic [7:0] event_data,
  input logic event_trigger,
  input logic [1:0] event_severity,  // 0=INFO, 1=WARNING, 2=ERROR
  
  // Logger interface
  output logic log_valid,
  output logic [1:0] log_type,
  output logic [7:0] log_data,
  input logic log_ack
);

  // Client state
  typedef enum logic [1:0] {
    IDLE,
    LOG_REQUESTED,
    WAIT_ACK
  } client_state_t;
  
  client_state_t state;
  
  // Client logic
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state <= IDLE;
      log_valid <= 1'b0;
      log_type <= 2'b00;
      log_data <= 8'h00;
    end else begin
      case (state)
        IDLE: begin
          if (event_trigger) begin
            state <= LOG_REQUESTED;
            log_valid <= 1'b1;
            log_type <= event_severity;
            log_data <= event_data;
          end
        end
        
        LOG_REQUESTED: begin
          state <= WAIT_ACK;
        end
        
        WAIT_ACK: begin
          if (log_ack) begin
            state <= IDLE;
            log_valid <= 1'b0;
          end
        end
        
        default: begin
          state <= IDLE;
        end
      endcase
    end
  end

endmodule


// Testbench
module singleton_logger();
  logic clk;
  logic rst_n;
  
  // Logger configuration
  logic config_valid;
  logic [1:0] config_log_level;
  
  // Client 1 signals
  logic client1_event_trigger;
  logic [7:0] client1_event_data;
  logic [1:0] client1_event_severity;
  logic client1_log_valid;
  logic [1:0] client1_log_type;
  logic [7:0] client1_log_data;
  logic client1_log_ack;
  
  // Client 2 signals
  logic client2_event_trigger;
  logic [7:0] client2_event_data;
  logic [1:0] client2_event_severity;
  logic client2_log_valid;
  logic [1:0] client2_log_type;
  logic [7:0] client2_log_data;
  logic client2_log_ack;
  
  // Logger output
  logic log_entry_valid;
  logic [1:0] log_entry_type;
  logic [7:0] log_entry_data;
  logic [15:0] log_count;
  
  // Instantiate the logger
  LoggerModule logger (
    .clk(clk),
    .rst_n(rst_n),
    .config_valid(config_valid),
    .config_log_level(config_log_level),
    .client1_log_valid(client1_log_valid),
    .client1_log_type(client1_log_type),
    .client1_log_data(client1_log_data),
    .client1_log_ack(client1_log_ack),
    .client2_log_valid(client2_log_valid),
    .client2_log_type(client2_log_type),
    .client2_log_data(client2_log_data),
    .client2_log_ack(client2_log_ack),
    .log_entry_valid(log_entry_valid),
    .log_entry_type(log_entry_type),
    .log_entry_data(log_entry_data),
    .log_count(log_count)
  );
  
  // Instantiate client 1
  LoggerClient client1 (
    .clk(clk),
    .rst_n(rst_n),
    .event_data(client1_event_data),
    .event_trigger(client1_event_trigger),
    .event_severity(client1_event_severity),
    .log_valid(client1_log_valid),
    .log_type(client1_log_type),
    .log_data(client1_log_data),
    .log_ack(client1_log_ack)
  );
  
  // Instantiate client 2
  LoggerClient client2 (
    .clk(clk),
    .rst_n(rst_n),
    .event_data(client2_event_data),
    .event_trigger(client2_event_trigger),
    .event_severity(client2_event_severity),
    .log_valid(client2_log_valid),
    .log_type(client2_log_type),
    .log_data(client2_log_data),
    .log_ack(client2_log_ack)
  );
  
  endmodule
// Testbench
module singleton_logger_tb;
  logic clk;
  logic rst_n;
  
  // Logger configuration
  logic config_valid;
  logic [1:0] config_log_level;
  
  // Client 1 signals
  logic client1_event_trigger;
  logic [7:0] client1_event_data;
  logic [1:0] client1_event_severity;
  logic client1_log_valid;
  logic [1:0] client1_log_type;
  logic [7:0] client1_log_data;
  logic client1_log_ack;
  
  // Client 2 signals
  logic client2_event_trigger;
  logic [7:0] client2_event_data;
  logic [1:0] client2_event_severity;
  logic client2_log_valid;
  logic [1:0] client2_log_type;
  logic [7:0] client2_log_data;
  logic client2_log_ack;
  
  // Logger output
  logic log_entry_valid;
  logic [1:0] log_entry_type;
  logic [7:0] log_entry_data;
  logic [15:0] log_count;
  
  // Instantiate the logger
  LoggerModule logger (
    .clk(clk),
    .rst_n(rst_n),
    .config_valid(config_valid),
    .config_log_level(config_log_level),
    .client1_log_valid(client1_log_valid),
    .client1_log_type(client1_log_type),
    .client1_log_data(client1_log_data),
    .client1_log_ack(client1_log_ack),
    .client2_log_valid(client2_log_valid),
    .client2_log_type(client2_log_type),
    .client2_log_data(client2_log_data),
    .client2_log_ack(client2_log_ack),
    .log_entry_valid(log_entry_valid),
    .log_entry_type(log_entry_type),
    .log_entry_data(log_entry_data),
    .log_count(log_count)
  );
  
  // Instantiate client 1
  LoggerClient client1 (
    .clk(clk),
    .rst_n(rst_n),
    .event_data(client1_event_data),
    .event_trigger(client1_event_trigger),
    .event_severity(client1_event_severity),
    .log_valid(client1_log_valid),
    .log_type(client1_log_type),
    .log_data(client1_log_data),
    .log_ack(client1_log_ack)
  );
  
  // Instantiate client 2
  LoggerClient client2 (
    .clk(clk),
    .rst_n(rst_n),
    .event_data(client2_event_data),
    .event_trigger(client2_event_trigger),
    .event_severity(client2_event_severity),
    .log_valid(client2_log_valid),
    .log_type(client2_log_type),
    .log_data(client2_log_data),
    .log_ack(client2_log_ack)
  );
  
  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end
  
  // Monitor logs
  always @(posedge clk) begin
    if (log_entry_valid) begin
      case (log_entry_type)
        2'b00: $display("INFO: Data=%h, Count=%d", log_entry_data, log_count);
        2'b01: $display("WARNING: Data=%h, Count=%d", log_entry_data, log_count);
        2'b10: $display("ERROR: Data=%h, Count=%d", log_entry_data, log_count);
        default: $display("UNKNOWN: Data=%h, Count=%d", log_entry_data, log_count);
      endcase
    end
  end
  
  // Test sequence
  initial begin
    // Initialize
    rst_n = 0;
    config_valid = 0;
    config_log_level = 2'b00;
    client1_event_trigger = 0;
    client1_event_data = 8'h00;
    client1_event_severity = 2'b00;
    client2_event_trigger = 0;
    client2_event_data = 8'h00;
    client2_event_severity = 2'b00;
    #20;
    
    rst_n = 1;
    #10;
    
    // Configure logger to INFO level
    config_log_level = 2'b11; // INFO level
    config_valid = 1;
    #10;
    config_valid = 0;
    #10;
    
    // Client 1 logs an INFO message
    client1_event_data = 8'hA1;
    client1_event_severity = 2'b00; // INFO
    client1_event_trigger = 1;
    #10;
    client1_event_trigger = 0;
    #20;
    
    // Client 2 logs a WARNING message
    client2_event_data = 8'hB2;
    client2_event_severity = 2'b01; // WARNING
    client2_event_trigger = 1;
    #10;
    client2_event_trigger = 0;
    #20;
    
    // Client 1 logs an ERROR message
    client1_event_data = 8'hC3;
    client1_event_severity = 2'b10; // ERROR
    client1_event_trigger = 1;
    #10;
    client1_event_trigger = 0;
    #20;
    
    // Change logger level to ERROR only
    config_log_level = 2'b01; // ERROR level
    config_valid = 1;
    #10;
    config_valid = 0;
    #10;
    
    // Client 2 logs an INFO message (should be filtered)
    client2_event_data = 8'hD4;
    client2_event_severity = 2'b00; // INFO
    client2_event_trigger = 1;
    #10;
    client2_event_trigger = 0;
    #20;
    
    // Client 1 logs an ERROR message (should pass through)
    client1_event_data = 8'hE5;
    client1_event_severity = 2'b10; // ERROR
    client1_event_trigger = 1;
    #10;
    client1_event_trigger = 0;
    #20;
    
    $finish;
  end
  
endmodule