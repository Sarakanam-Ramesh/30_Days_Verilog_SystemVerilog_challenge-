`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 13.03.2025 22:52:13
// Design Name: 
// Module Name: Multi_channel_interfacce
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


// Multi-Channel Interface (RTL)
// This module implements an 8-channel data interface with individual
// enable signals and a shared clock domain

module multi_channel_interface #(
    parameter CHANNELS = 8,
    parameter DATA_WIDTH = 32
)(
    input  wire                        clk,
    input  wire                        rst_n,
    
    // Input channels
    input  wire [CHANNELS-1:0]         channel_valid_i,
    input  wire [CHANNELS*DATA_WIDTH-1:0] channel_data_i,
    output wire [CHANNELS-1:0]         channel_ready_o,
    
    // Output interface
    output wire                        data_valid_o,
    output wire [DATA_WIDTH-1:0]       data_o,
    output wire [$clog2(CHANNELS)-1:0] channel_id_o,
    input  wire                        data_ready_i
);

    // Channel selection logic using priority encoder
    reg [$clog2(CHANNELS)-1:0] selected_channel;
    reg [CHANNELS-1:0] channel_valid_masked;
    reg channel_selected;
    integer i;
    
    // Ready signals - a channel is ready when it's selected or when no valid data
    assign channel_ready_o = (channel_selected) ? (1 << selected_channel) & {CHANNELS{data_ready_i}} : {CHANNELS{1'b0}};
    
    // Output signals
    assign data_valid_o = channel_selected;
    assign data_o = channel_selected ? channel_data_i[selected_channel*DATA_WIDTH +: DATA_WIDTH] : {DATA_WIDTH{1'b0}};
    assign channel_id_o = selected_channel;
    
    // Priority encoder for channel selection
    always @(*) begin
        channel_valid_masked = channel_valid_i;
        channel_selected = |channel_valid_masked;
        selected_channel = 0;
        
        for (i = 0; i < CHANNELS; i=i+1) begin
            if (channel_valid_masked[i]) begin
                selected_channel = i[$clog2(CHANNELS)-1:0];
                //break;
            end
        end
    end

endmodule

// Multi-Channel Interface Testbench
`timescale 1ns/1ps

module multi_channel_interface_tb;
    // Parameters
    localparam CHANNELS = 8;
    localparam DATA_WIDTH = 32;
    
    // Clock and reset
    reg clk = 0;
    reg rst_n = 0;
    
    // Input channels
    reg [CHANNELS-1:0] channel_valid_i;
    reg [CHANNELS*DATA_WIDTH-1:0] channel_data_i;
    wire [CHANNELS-1:0] channel_ready_o;
    
    // Output interface
    wire data_valid_o;
    wire [DATA_WIDTH-1:0] data_o;
    wire [$clog2(CHANNELS)-1:0] channel_id_o;
    reg data_ready_i;
    integer i;
    
    // DUT instantiation
    multi_channel_interface #(
        .CHANNELS(CHANNELS),
        .DATA_WIDTH(DATA_WIDTH)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .channel_valid_i(channel_valid_i),
        .channel_data_i(channel_data_i),
        .channel_ready_o(channel_ready_o),
        .data_valid_o(data_valid_o),
        .data_o(data_o),
        .channel_id_o(channel_id_o),
        .data_ready_i(data_ready_i)
    );
    
    // Clock generation
    always #5 clk = ~clk;
    
    // Test sequence
    initial begin
        // Initialize signals
        channel_valid_i = 0;
        channel_data_i = 0;
        data_ready_i = 0;
        
        // Apply reset
        #10 rst_n = 0;
        #20 rst_n = 1;
        
        // Apply test stimuli
        #10;
        
        // Test 1: Single channel active
        channel_data_i[0 +: DATA_WIDTH] = 32'hA1A1A1A1;
        channel_valid_i = 8'b00000001;
        data_ready_i = 1;
        #10;
        
        // Test 2: Multiple channels active (priority should select lowest index)
        channel_data_i[0 +: DATA_WIDTH] = 32'hB1B1B1B1;
        channel_data_i[2*DATA_WIDTH +: DATA_WIDTH] = 32'hB3B3B3B3;
        channel_data_i[5*DATA_WIDTH +: DATA_WIDTH] = 32'hB6B6B6B6;
        channel_valid_i = 8'b00100101;
        #10;
        
        // Test 3: Backpressure test
        data_ready_i = 0;  // Assert backpressure
        #20;
        data_ready_i = 1;  // Release backpressure
        #10;
        
        // Test 4: All channels active
        for (i = 0; i < CHANNELS; i=i+1) begin
            channel_data_i[i*DATA_WIDTH +: DATA_WIDTH] = 32'hC0C0C0C0 + i;
        end
        channel_valid_i = 8'b11111111;
        #40;
        
        // Test 5: No channels active
        channel_valid_i = 8'b00000000;
        #20;
        
        // End simulation
        $display("Simulation completed successfully");
        $finish;
    end
    
    // Monitor
    always @(posedge clk) begin
        if (data_valid_o && data_ready_i) begin
            $display("Time: %0t, Channel: %0d, Data: 0x%h", $time, channel_id_o, data_o);
        end
    end
    
endmodule