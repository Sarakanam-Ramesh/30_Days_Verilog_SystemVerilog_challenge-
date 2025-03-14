`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 13.03.2025 15:07:57
// Design Name: 
// Module Name: Observer_pattern
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


// Synthesizable Observer Pattern
// Implements a subject (temperature sensor) with multiple observers (alarm modules)

// Subject module - Temperature Sensor
module TemperatureSensor (
  input logic clk,
  input logic rst_n,
  input logic [7:0] sensor_input,
  input logic sensor_valid,
  
  // Observer notification interfaces
  output logic [7:0] current_temperature,
  output logic temperature_update_valid,
  output logic threshold_exceeded
);

  // Internal state
  logic [7:0] temperature;
  logic [7:0] threshold;
  
  // Initialize threshold
  initial begin
    threshold = 8'd75; // 75 degrees threshold
  end
  
  // Update temperature and notify observers
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      temperature <= 8'd0;
      temperature_update_valid <= 1'b0;
      threshold_exceeded <= 1'b0;
    end else begin
      temperature_update_valid <= 1'b0;
      
      if (sensor_valid) begin
        temperature <= sensor_input;
        temperature_update_valid <= 1'b1;
        
        // Check if temperature exceeds threshold
        threshold_exceeded <= (sensor_input > threshold);
      end
    end
  end
  
  // Output current temperature to observers
  assign current_temperature = temperature;

endmodule

// Observer 1 - Temperature Display
module TemperatureDisplay (
  input logic clk,
  input logic rst_n,
  input logic [7:0] temperature_input,
  input logic temperature_valid,
  
  // Display output (could connect to LED digits, LCD, etc.)
  output logic [7:0] display_value,
  output logic display_updated
);

  // Internal state
  logic [7:0] displayed_temp;
  
  // Update display when notified by subject
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      displayed_temp <= 8'd0;
      display_updated <= 1'b0;
    end else begin
      display_updated <= 1'b0;
      
      if (temperature_valid) begin
        displayed_temp <= temperature_input;
        display_updated <= 1'b1;
      end
    end
  end
  
  // Output to display
  assign display_value = displayed_temp;

endmodule

// Observer 2 - Temperature Alarm
module TemperatureAlarm (
  input logic clk,
  input logic rst_n,
  input logic threshold_exceeded,
  input logic temperature_valid,
  
  // Alarm output
  output logic alarm_active
);

  // Internal state
  logic alarm_state;
  
  // Update alarm when notified by subject
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      alarm_state <= 1'b0;
    end else if (temperature_valid) begin
      alarm_state <= threshold_exceeded;
    end
  end
  
  // Output alarm state
  assign alarm_active = alarm_state;

endmodule

// Observer 3 - Temperature Logger
module TemperatureLogger (
  input logic clk,
  input logic rst_n,
  input logic [7:0] temperature_input,
  input logic temperature_valid,
  
  // Logger output
  output logic [7:0] logged_temperature,
  output logic [15:0] log_count,
  output logic log_event
);

  // Internal state
  logic [15:0] entry_count;
  
  // Update log when notified by subject
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      logged_temperature <= 8'd0;
      entry_count <= 16'd0;
      log_event <= 1'b0;
    end else begin
      log_event <= 1'b0;
      
      if (temperature_valid) begin
        logged_temperature <= temperature_input;
        entry_count <= entry_count + 16'd1;
        log_event <= 1'b1;
      end
    end
  end
  
  // Output log count
  assign log_count = entry_count;

endmodule

// Top-level module that connects the subject with multiple observers
module TemperatureMonitorSystem (
  input logic clk,
  input logic rst_n,
  input logic [7:0] raw_temperature,
  input logic temperature_sample_valid,
  
  // Observer outputs
  output logic [7:0] display_temperature,
  output logic display_updated,
  output logic alarm_active,
  output logic [7:0] logged_temperature,
  output logic [15:0] log_entry_count,
  output logic log_updated
);

  // Internal signals
  logic [7:0] current_temperature;
  logic temperature_update;
  logic temp_threshold_exceeded;
  
  // Instantiate the subject (temperature sensor)
  TemperatureSensor sensor (
    .clk(clk),
    .rst_n(rst_n),
    .sensor_input(raw_temperature),
    .sensor_valid(temperature_sample_valid),
    .current_temperature(current_temperature),
    .temperature_update_valid(temperature_update),
    .threshold_exceeded(temp_threshold_exceeded)
  );
  
  // Instantiate Observer 1 (display)
  TemperatureDisplay display (
    .clk(clk),
    .rst_n(rst_n),
    .temperature_input(current_temperature),
    .temperature_valid(temperature_update),
    .display_value(display_temperature),
    .display_updated(display_updated)
  );
  
  // Instantiate Observer 2 (alarm)
  TemperatureAlarm alarm (
    .clk(clk),
    .rst_n(rst_n),
    .threshold_exceeded(temp_threshold_exceeded),
    .temperature_valid(temperature_update),
    .alarm_active(alarm_active)
  );
  
  // Instantiate Observer 3 (logger)
  TemperatureLogger logger (
    .clk(clk),
    .rst_n(rst_n),
    .temperature_input(current_temperature),
    .temperature_valid(temperature_update),
    .logged_temperature(logged_temperature),
    .log_count(log_entry_count),
    .log_event(log_updated)
  );

endmodule

// Testbench
module observer_pattern_tb;
  logic clk;
  logic rst_n;
  logic [7:0] raw_temperature;
  logic temperature_sample_valid;
  
  logic [7:0] display_temperature;
  logic display_updated;
  logic alarm_active;
  logic [7:0] logged_temperature;
  logic [15:0] log_entry_count;
  logic log_updated;
  
  // Instantiate the top module
  TemperatureMonitorSystem dut (
    .clk(clk),
    .rst_n(rst_n),
    .raw_temperature(raw_temperature),
    .temperature_sample_valid(temperature_sample_valid),
    .display_temperature(display_temperature),
    .display_updated(display_updated),
    .alarm_active(alarm_active),
    .logged_temperature(logged_temperature),
    .log_entry_count(log_entry_count),
    .log_updated(log_updated)
  );
  
  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end
  
  // Monitor observer updates
  always @(posedge clk) begin
    if (display_updated) begin
      $display("Display updated: %d degrees", display_temperature);
    end
    
    if (alarm_active) begin
      $display("ALARM: Temperature threshold exceeded!");
    end
    
    if (log_updated) begin
      $display("Temperature logged: %d degrees (Log entry #%d)", 
                logged_temperature, log_entry_count);
    end
  end
  
  // Test sequence
  initial begin
    // Initialize
    rst_n = 0;
    raw_temperature = 8'd0;
    temperature_sample_valid = 0;
    #20;
    
    rst_n = 1;
    #10;
    
    // Normal temperature reading
    raw_temperature = 8'd65;
    temperature_sample_valid = 1;
    #10;
    temperature_sample_valid = 0;
    #20;
    
    // High temperature reading (should trigger alarm)
    raw_temperature = 8'd80;
    temperature_sample_valid = 1;
    #10;
    temperature_sample_valid = 0;
    #20;
    
    // Temperature back to normal
    raw_temperature = 8'd70;
    temperature_sample_valid = 1;
    #10;
    temperature_sample_valid = 0;
    #20;
    
    $finish;
  end
  
endmodule
