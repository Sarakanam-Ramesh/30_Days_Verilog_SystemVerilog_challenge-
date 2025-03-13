`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11.03.2025 14:28:46
// Design Name: 
// Module Name: Basic_handshaking
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


module producer (
  input        clk,
  input        rst_n,
  input        ready,     // Consumer is ready to receive
  output reg   valid,     // Producer has valid data
  output [7:0] data       // Data from producer to consumer
);

  reg [7:0] data_reg;
  reg [3:0] count;
  
  assign data = data_reg;
  
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      valid <= 1'b0;
      data_reg <= 8'h00;
      count <= 4'h0;
    end
    else begin
      if (ready && valid) begin
        // Consumer accepted the data, prepare next data
        valid <= 1'b0;
      end
      else if (!valid) begin
        // Produce new data
        data_reg <= data_reg + 8'h1;
        valid <= 1'b1;
        count <= count + 4'h1;
      end
    end
  end
  
endmodule

module consumer (
  input        clk,
  input        rst_n,
  input        valid,     // Producer has valid data
  input  [7:0] data,      // Data from producer
  output reg   ready      // Consumer is ready to receive
);

  reg [7:0] last_received;
  
  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      ready <= 1'b1;      // Ready to receive initially
      last_received <= 8'h00;
    end
    else begin
      if (valid && ready) begin
        // Received valid data
        last_received <= data;
        ready <= 1'b0;    // Not ready for next cycle
      end
      else if (!ready) begin
        // Process the data (simulated by waiting)
        ready <= 1'b1;    // Ready for next data
      end
    end
  end
  
endmodule

module handshaking_system_18 (
  input        clk,
  input        rst_n,
  output [7:0] last_data
);

  wire        valid;
  wire        ready;
  wire [7:0]  data;
  
  producer producer_inst (
    .clk(clk),
    .rst_n(rst_n),
    .ready(ready),
    .valid(valid),
    .data(data)
  );
  
  consumer consumer_inst (
    .clk(clk),
    .rst_n(rst_n),
    .valid(valid),
    .data(data),
    .ready(ready),
    .last_received(last_data)
  );
  
endmodule

`timescale 1ns/1ps

module handshaking_18_tb;
  
  // Signals
  reg         clk;
  reg         rst_n;
  wire [7:0]  data;
  wire        valid;
  wire        ready;
  
  // Instantiate modules
  producer producer_inst (
    .clk(clk),
    .rst_n(rst_n),
    .ready(ready),
    .valid(valid),
    .data(data)
  );
  
  consumer consumer_inst (
    .clk(clk),
    .rst_n(rst_n),
    .valid(valid),
    .data(data),
    .ready(ready)
  );
  
  // Clock generation
  always #5 clk = ~clk;
  
  // Test sequence
  initial begin
    // Initialize
    clk = 0;
    rst_n = 0;
    
    // Reset
    #20 rst_n = 1;
    
    // Run simulation
    #500;
    
    // End simulation
    $finish;
  end
  
  // Monitor handshaking
  initial begin
    $monitor("Time=%0t: valid=%b, ready=%b, data=%h", 
             $time, valid, ready, data);
  end
  
endmodule