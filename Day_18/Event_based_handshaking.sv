`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11.03.2025 18:07:34
// Design Name: 
// Module Name: Event_based_handshaking
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


// Synthesizable event-based handshaking protocol
module handshake_protocol_18(
  input  logic       clk,
  input  logic       rst_n,
  // Sender interface
  input  logic       send_valid,
  input  logic [7:0] send_data,
  output logic       send_ready,
  // Receiver interface
  output logic       recv_valid,
  output logic [7:0] recv_data,
  input  logic       recv_ready
);

  typedef enum logic [1:0] {
    IDLE,
    SENDING,
    WAIT_ACK
  } state_t;
  
  state_t state;
  
  // State machine
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state <= IDLE;
      recv_valid <= 1'b0;
      recv_data <= 8'h00;
      send_ready <= 1'b1;
    end else begin
      case (state)
        IDLE: begin
          if (send_valid && send_ready) begin
            // Latch the data
            recv_data <= send_data;
            recv_valid <= 1'b1;
            send_ready <= 1'b0;
            state <= SENDING;
          end
        end
        
        SENDING: begin
          if (recv_ready) begin
            // Receiver acknowledged the data
            recv_valid <= 1'b0;
            state <= WAIT_ACK;
          end
        end
        
        WAIT_ACK: begin
          // Wait cycle to allow sender to deassert valid if needed
          send_ready <= 1'b1;
          state <= IDLE;
        end
        
        default: state <= IDLE;
      endcase
    end
  end

endmodule

// Testbench for handshake protocol using events
`timescale 1ns/1ps

module handshake_protocol_18_tb();
  // DUT signals
  logic       clk = 0;
  logic       rst_n;
  logic       send_valid;
  logic [7:0] send_data;
  logic       send_ready;
  logic       recv_valid;
  logic [7:0] recv_data;
  logic       recv_ready;
  
  // Events for synchronization
  event data_sent;
  event data_received;
  
  // Instantiate DUT
  handshake_protocol_18 dut (
    .clk(clk),
    .rst_n(rst_n),
    .send_valid(send_valid),
    .send_data(send_data),
    .send_ready(send_ready),
    .recv_valid(recv_valid),
    .recv_data(recv_data),
    .recv_ready(recv_ready)
  );
  
  // Clock generation
  always #5 clk = ~clk;
  
  // Sender task
  task sender();
    int delay;
    
    send_valid = 0;
    for (int i = 0; i < 20; i++) begin
      // Wait for ready signal
      while (!send_ready) @(posedge clk);
      
      // Random delay before sending
      delay = $urandom_range(1, 5);
      repeat (delay) @(posedge clk);
      
      // Send data
      send_data = $urandom;
      send_valid = 1;
      $display("[%0t] Sender: Sending data 0x%h", $time, send_data);
      
      @(posedge clk);
      while (send_ready) @(posedge clk); // Wait until accepted
      send_valid = 0;
      
      // Trigger event and wait for completion
      ->data_sent;
      @(data_received);
    end
  endtask
  
  // Receiver task
  task receiver();
    int delay;
    
    recv_ready = 0;
    forever begin
      // Wait for valid data
      while (!recv_valid) @(posedge clk);
      
      // Display received data
      $display("[%0t] Receiver: Got data 0x%h", $time, recv_data);
      
      // Random delay before acknowledging
      delay = $urandom_range(1, 5);
      repeat (delay) @(posedge clk);
      
      // Acknowledge receipt
      recv_ready = 1;
      @(posedge clk);
      recv_ready = 0;
      
      // Trigger event
      ->data_received;
      @(data_sent);
    end
  endtask
  
  // Main test sequence
  initial begin
    // Reset
    rst_n = 0;
    send_valid = 0;
    recv_ready = 0;
    
    repeat(5) @(posedge clk);
    rst_n = 1;
    
    fork
      sender();
      receiver();
    join_any
    
    repeat(10) @(posedge clk);
    $display("[%0t] Test complete", $time);
    $finish;
  end
  
  // Watchdog timer
  initial begin
    #5000;
    $display("[%0t] Watchdog timeout - finishing simulation", $time);
    $finish;
  end
  
  // Protocol checking
  property valid_ready_handshake;
    @(posedge clk) disable iff (!rst_n)
    (send_valid && send_ready) |-> ##[1:$] (recv_valid && recv_ready);
  endproperty
  
  assert property (valid_ready_handshake)
    else $error("Handshake protocol violation");
  
endmodule
