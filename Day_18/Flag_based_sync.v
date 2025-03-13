`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11.03.2025 14:40:40
// Design Name: 
// Module Name: Flag_based_sync
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


module flag_sync_18 (
  input        clk,
  input        rst_n,
  input        process_a_trigger,
  input  [7:0] process_a_data,
  output [7:0] process_b_result,
  output       process_b_done
);

  // State definitions
  localparam IDLE        = 2'b00;
  localparam PROCESSING  = 2'b01;
  localparam DONE        = 2'b10;
  
  reg [1:0]  state_a;
  reg [1:0]  state_b;
  reg [7:0]  shared_data;
  reg [7:0]  result;
  reg        a_done_flag;
  reg        b_done_flag;
  
  // Process A - Data Producer
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state_a <= IDLE;
      shared_data <= 8'h00;
      a_done_flag <= 1'b0;
    end
    else begin
      case (state_a)
        IDLE: begin
          if (process_a_trigger) begin
            shared_data <= process_a_data;
            a_done_flag <= 1'b1;
            state_a <= PROCESSING;
          end
        end
        
        PROCESSING: begin
          if (b_done_flag) begin
            a_done_flag <= 1'b0;
            state_a <= DONE;
          end
        end
        
        DONE: begin
          state_a <= IDLE;
        end
        
        default: state_a <= IDLE;
      endcase
    end
  end
  
  // Process B - Data Consumer
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state_b <= IDLE;
      result <= 8'h00;
      b_done_flag <= 1'b0;
    end
    else begin
      case (state_b)
        IDLE: begin
          if (a_done_flag) begin
            state_b <= PROCESSING;
          end
        end
        
        PROCESSING: begin
          // Process the data (multiply by 2 in this example)
          result <= shared_data << 1;
          b_done_flag <= 1'b1;
          state_b <= DONE;
        end
        
        DONE: begin
          if (!a_done_flag) begin
            b_done_flag <= 1'b0;
            state_b <= IDLE;
          end
        end
        
        default: state_b <= IDLE;
      endcase
    end
  end
  
  assign process_b_result = result;
  assign process_b_done = b_done_flag;
  
endmodule

`timescale 1ns/1ps

module flag_sync_18_tb;
  
  // Signals
  reg         clk;
  reg         rst_n;
  reg         process_a_trigger;
  reg  [7:0]  process_a_data;
  wire [7:0]  process_b_result;
  wire        process_b_done;
  
  // Instantiate DUT
  flag_sync_18 dut (
    .clk(clk),
    .rst_n(rst_n),
    .process_a_trigger(process_a_trigger),
    .process_a_data(process_a_data),
    .process_b_result(process_b_result),
    .process_b_done(process_b_done)
  );
  
  // Clock generation
  always #5 clk = ~clk;
  
  // Test sequence
  initial begin
    // Initialize
    clk = 0;
    rst_n = 0;
    process_a_trigger = 0;
    process_a_data = 0;
    
    // Reset
    #20 rst_n = 1;
    
    // Test Case 1: Send data 0x10
    #10;
    process_a_data = 8'h10;
    process_a_trigger = 1;
    #10 process_a_trigger = 0;
    
    // Wait for processing
    @(posedge process_b_done);
    #20;
    
    // Test Case 2: Send data 0xA5
    process_a_data = 8'hA5;
    process_a_trigger = 1;
    #10 process_a_trigger = 0;
    
    // Wait for processing
    @(posedge process_b_done);
    #20;
    
    // Test Case 3: Send data 0xFF
    process_a_data = 8'hFF;
    process_a_trigger = 1;
    #10 process_a_trigger = 0;
    
    // Wait for processing
    @(posedge process_b_done);
    #20;
    
    // End simulation
    $finish;
  end
  
  // Monitor
  initial begin
    $monitor("Time=%0t: trigger=%b, data_in=%h, result=%h, done=%b", 
             $time, process_a_trigger, process_a_data, process_b_result, process_b_done);
  end
  
endmodule
