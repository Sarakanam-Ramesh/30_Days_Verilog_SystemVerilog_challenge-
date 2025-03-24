`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 24.03.2025 23:08:49
// Design Name: 
// Module Name: DMA_Controller
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


`timescale 1ns/1ps

module dma_controller_structural #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32,
    parameter NUM_CHANNELS = 4
)(
    input wire clk,
    input wire rst_n,
    input wire [NUM_CHANNELS-1:0] channel_req,
    input wire [NUM_CHANNELS-1:0] peripheral_req,
    output wire [NUM_CHANNELS-1:0] peripheral_ack,
    output wire [ADDR_WIDTH-1:0] mem_addr,
    output wire [DATA_WIDTH-1:0] mem_data_out,
    input wire [DATA_WIDTH-1:0] mem_data_in,
    output wire mem_read_en,
    output wire mem_write_en,
    output wire dma_interrupt,
    output wire [NUM_CHANNELS-1:0] channel_active,
    output wire [NUM_CHANNELS-1:0] channel_complete
);

    // State Parameters (replacing typedef)
    parameter [1:0] 
        TRANSFER_IDLE = 2'b00,
        TRANSFER_READ = 2'b01,
        TRANSFER_WRITE = 2'b10,
        TRANSFER_COMPLETE = 2'b11;

    // Internal Wires
    wire [2:0] selected_channel;
    wire [ADDR_WIDTH-1:0] channel_src_addr;
    wire [ADDR_WIDTH-1:0] channel_dest_addr;
    wire transfer_valid;
    wire transfer_ready;
    reg [ADDR_WIDTH-1:0] src_addr;
    reg [ADDR_WIDTH-1:0] dest_addr;

    // Priority Encoder Module
    priority_encoder #(
        .NUM_CHANNELS(NUM_CHANNELS)
    ) priority_selector (
        .requests(channel_req),
        .selected_channel(selected_channel)
    );

    // Address Generator Module
    address_generator #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .NUM_CHANNELS(NUM_CHANNELS)
    ) addr_gen (
        .clk(clk),
        .rst_n(rst_n),
        .selected_channel(selected_channel),
        .channel_req(channel_req),
        .src_addr(channel_src_addr),
        .dest_addr(channel_dest_addr)
    );

    // Transfer Controller Module
    transfer_controller #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .src_addr(channel_src_addr),  // CHANGED: Use channel_src_addr directly
        .dest_addr(channel_dest_addr),  // CHANGED: Use channel_dest_addr directly
        .mem_addr(mem_addr),
        .mem_data_out(mem_data_out),
        .mem_data_in(mem_data_in),
        .mem_read_en(mem_read_en),
        .mem_write_en(mem_write_en),
        .transfer_valid(transfer_valid),
        .transfer_ready(transfer_ready)
    );

    // Interrupt Controller Module
    interrupt_controller #(
        .NUM_CHANNELS(NUM_CHANNELS)
    ) int_ctrl (
        .clk(clk),
        .rst_n(rst_n),
        .channel_complete(channel_complete),
        .peripheral_req(peripheral_req),
        .peripheral_ack(peripheral_ack),
        .dma_interrupt(dma_interrupt)
    );

    // Channel Status Controller Module
    channel_status_controller #(
        .NUM_CHANNELS(NUM_CHANNELS)
    ) channel_status (
        .clk(clk),
        .rst_n(rst_n),
        .channel_req(channel_req),
        .transfer_complete(transfer_ready),  // CHANGED: Use transfer_ready directly
        .channel_active(channel_active),
        .channel_complete(channel_complete)
    );

endmodule

// Priority Encoder Module
module priority_encoder #(
    parameter NUM_CHANNELS = 4
)(
    input wire [NUM_CHANNELS-1:0] requests,
    output reg [2:0] selected_channel
);
        integer i;
    always @(*) begin
        selected_channel = 3'b000;
        for (i = 0; i < NUM_CHANNELS; i = i + 1) begin
            if (requests[i]) begin
                selected_channel = i;
                //disable block;
            end
        end
    end
endmodule

// Address Generator Module
module address_generator #(
    parameter ADDR_WIDTH = 32,
    parameter NUM_CHANNELS = 4
)(
    input wire clk,
    input wire rst_n,
    input wire [2:0] selected_channel,
    input wire [NUM_CHANNELS-1:0] channel_req,
    output reg [ADDR_WIDTH-1:0] src_addr,
    output reg [ADDR_WIDTH-1:0] dest_addr
);
    // Base addresses for each channel
    reg [ADDR_WIDTH-1:0] channel_base_src [NUM_CHANNELS-1:0];
    reg [ADDR_WIDTH-1:0] channel_base_dest [NUM_CHANNELS-1:0];
    integer i;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Initialize base addresses
            for (i = 0; i < NUM_CHANNELS; i = i + 1) begin
                channel_base_src[i] = 32'h1000_0000 + (i * 32'h1000);
                channel_base_dest[i] = 32'h2000_0000 + (i * 32'h1000);
            end
        end else begin
            // Generate addresses based on selected channel
            if (channel_req[selected_channel]) begin
                src_addr = channel_base_src[selected_channel];
                dest_addr = channel_base_dest[selected_channel];
                
                // Increment base addresses for next transfer
                channel_base_src[selected_channel] = 
                    channel_base_src[selected_channel] + 32'h4;
                channel_base_dest[selected_channel] = 
                    channel_base_dest[selected_channel] + 32'h4;
            end
        end
    end
endmodule

// transfer controller
module transfer_controller #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32
)(
    input wire clk,
    input wire rst_n,
    input wire [ADDR_WIDTH-1:0] src_addr,
    input wire [ADDR_WIDTH-1:0] dest_addr,
    output reg [ADDR_WIDTH-1:0] mem_addr,
    output reg [DATA_WIDTH-1:0] mem_data_out,
    input wire [DATA_WIDTH-1:0] mem_data_in,
    output reg mem_read_en,
    output reg mem_write_en,
    output reg transfer_valid,
    output reg transfer_ready
);
    // State Parameters
    parameter [2:0] 
        IDLE = 3'b000,
        READ_ADDR = 3'b001,
        READ_DATA = 3'b010,
        WRITE_ADDR = 3'b011,
        WRITE_DATA = 3'b100,
        COMPLETE = 3'b101;

    reg [2:0] current_state, next_state;
    reg [7:0] transfer_count;
    reg [ADDR_WIDTH-1:0] current_src_addr;
    reg [ADDR_WIDTH-1:0] current_dest_addr;

    // State Transition Logic
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_state <= IDLE;
            current_src_addr <= 'b0;
            current_dest_addr <= 'b0;
            transfer_count <= 8'd0;  // CHANGED: Initialize transfer_count to 0
        end else begin
            current_state <= next_state;
            
            // CHANGED: Simplified address and transfer count management
            if (current_state == IDLE && src_addr != 0) begin
                current_src_addr <= src_addr;
                current_dest_addr <= dest_addr;
                transfer_count <= 8'd4; // Fixed transfer size
            end
        end
    end

    // Next State and Output Logic
    always @(*) begin
        // Default values
        next_state = current_state;
        mem_read_en = 1'b0;
        mem_write_en = 1'b0;
        transfer_valid = 1'b0;
        transfer_ready = 1'b0;
        mem_addr = 'b0;
        mem_data_out = 'b0;

        case (current_state)
            IDLE: begin
                if (src_addr != 0) begin
                    next_state = READ_ADDR;
                    mem_addr = current_src_addr;
                    mem_read_en = 1'b1;
                end
            end

            READ_ADDR: begin
                mem_addr = current_src_addr;
                mem_read_en = 1'b1;
                next_state = READ_DATA;
            end

            READ_DATA: begin
                mem_data_out = mem_data_in;
                mem_read_en = 1'b0;
                next_state = WRITE_ADDR;
                mem_addr = current_dest_addr;
            end

            WRITE_ADDR: begin
                mem_addr = current_dest_addr;
                mem_write_en = 1'b1;
                next_state = WRITE_DATA;
            end

            WRITE_DATA: begin
                mem_write_en = 1'b1;
                mem_addr = current_dest_addr;
                
                transfer_count = transfer_count - 1;
                
                if (transfer_count == 0) begin
                    next_state = COMPLETE;
                    transfer_ready = 1'b1;
                end else begin
                    // Increment addresses for next transfer
                    current_src_addr = current_src_addr + 4;  // CHANGED: Use 4-byte increment
                    current_dest_addr = current_dest_addr + 4;
                    next_state = READ_ADDR;
                end
            end

            COMPLETE: begin
                transfer_ready = 1'b1;
                transfer_valid = 1'b1;
                next_state = IDLE;
            end

            default: next_state = IDLE;
        endcase
    end
endmodule

// Interrupt Controller Module
module interrupt_controller #(
    parameter NUM_CHANNELS = 4
)(
    input wire clk,
    input wire rst_n,
    input wire [NUM_CHANNELS-1:0] channel_complete,
    input wire [NUM_CHANNELS-1:0] peripheral_req,
    output reg [NUM_CHANNELS-1:0] peripheral_ack,
    output reg dma_interrupt
);
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            dma_interrupt <= 1'b0;
            peripheral_ack <= 'b0;
        end else begin
            // Generate interrupt when any channel completes
            dma_interrupt <= |channel_complete;
            
            // Acknowledge peripheral requests for completed channels
            peripheral_ack <= channel_complete;
        end
    end
endmodule

// Channel Status Controller Module
module channel_status_controller #(
    parameter NUM_CHANNELS = 4
)(
    input wire clk,
    input wire rst_n,
    input wire [NUM_CHANNELS-1:0] channel_req,
    input wire transfer_complete,
    output reg [NUM_CHANNELS-1:0] channel_active,
    output reg [NUM_CHANNELS-1:0] channel_complete
);
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            channel_active <= 'b0;
            channel_complete <= 'b0;
        end else begin
            // Set active channels based on requests
            channel_active <= channel_req;
            
            // Set complete flag when transfer is done
            if (transfer_complete) begin
                channel_complete <= channel_req;
            end else begin
                channel_complete <= 'b0;
            end
        end
    end
endmodule

`timescale 1ns/1ps

module dma_controller_structural_tb;
    // Parameters
    parameter ADDR_WIDTH = 32;
    parameter DATA_WIDTH = 32;
    parameter NUM_CHANNELS = 4;

    // Testbench Signals
    reg clk, rst_n;
    reg [NUM_CHANNELS-1:0] channel_req;
    reg [NUM_CHANNELS-1:0] peripheral_req;
    wire [NUM_CHANNELS-1:0] peripheral_ack;

    wire [ADDR_WIDTH-1:0] mem_addr;
    wire [DATA_WIDTH-1:0] mem_data_out;
    reg [DATA_WIDTH-1:0] mem_data_in;
    wire mem_read_en, mem_write_en;
    wire dma_interrupt;
    wire [NUM_CHANNELS-1:0] channel_active, channel_complete;

    // Memory Simulation
    reg [DATA_WIDTH-1:0] memory [0:1024];

    // Instantiate DMA Controller
    dma_controller_structural #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH),
        .NUM_CHANNELS(NUM_CHANNELS)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .channel_req(channel_req),
        .peripheral_req(peripheral_req),
        .peripheral_ack(peripheral_ack),
        .mem_addr(mem_addr),
        .mem_data_out(mem_data_out),
        .mem_data_in(mem_data_in),
        .mem_read_en(mem_read_en),
        .mem_write_en(mem_write_en),
        .dma_interrupt(dma_interrupt),
        .channel_active(channel_active),
        .channel_complete(channel_complete)
    );

    // Clock Generation
    always #5 clk = ~clk;

    // Memory Simulation Logic
    always @(posedge clk) begin
        if (mem_read_en) begin
            // Simulate memory read
            mem_data_in <= memory[mem_addr[9:2]];
        end
        
        if (mem_write_en) begin
            // Simulate memory write
            memory[mem_addr[9:2]] <= mem_data_out;
        end
    end

    // Testbench Stimulus
    initial begin
        // Initialize Signals
        clk = 0;
        rst_n = 0;
        channel_req = 'b0;
        peripheral_req = 'b0;
        mem_data_in = 'b0;

        // Populate Memory with Test Data
        for (integer i = 0; i < 16; i = i + 1) begin
            memory[i] = i * 10;
        end

        // Reset Sequence
        #10 rst_n = 1;

        // Test Scenario 1: Single Channel DMA Transfer
        #20 channel_req = 4'b0001;  // Request Channel 0
        peripheral_req = 4'b0001;   // Peripheral request for Channel 0


        // Test Scenario 2: Multiple Channel Requests
        #100 
        channel_req = 4'b1010;  // Request Channels 1 and 3
        peripheral_req = 4'b1010;  // Peripheral requests for Channels 1 and 3

        // Wait and Observe Transfers
        #500 $finish;
    end

    // Monitor and Display Results
    initial begin
        $monitor("Time=%0t: Channel Req=%b, Active=%b, Complete=%b, Interrupt=%b, Mem Addr=%h, Mem Data Out=%h", 
                 $time, channel_req, channel_active, channel_complete, 
                 dma_interrupt, mem_addr, mem_data_out);
    end

    // VCD Dump for Waveform Analysis
    initial begin
        $dumpfile("dma_controller_structural_tb.vcd");
        $dumpvars(0, dma_controller_structural_tb);
    end

    // Timeout to prevent infinite simulation
    initial begin
        #1000 $display("Testbench timed out");
        $finish;
    end
endmodule


`timescale 1ns/1ps

module priority_encoder_tb;
    parameter NUM_CHANNELS = 4;

    // Inputs
    reg [NUM_CHANNELS-1:0] requests;

    // Outputs
    wire [2:0] selected_channel;

    // Instantiate the Unit Under Test (UUT)
    priority_encoder #(
        .NUM_CHANNELS(NUM_CHANNELS)
    ) uut (
        .requests(requests),
        .selected_channel(selected_channel)
    );

    // Stimulus
    initial begin
        // Test Case 1: No requests
        requests = 4'b0000;
        #10;
        $display("Test Case 1 - No Requests: Selected Channel = %0d", selected_channel);

        // Test Case 2: Single Channel Request
        requests = 4'b0010;  // Channel 1
        #10;
        $display("Test Case 2 - Channel 1 Request: Selected Channel = %0d", selected_channel);

        // Test Case 3: Multiple Channel Requests
        requests = 4'b1010;  // Channels 1 and 3
        #10;
        $display("Test Case 3 - Multiple Requests: Selected Channel = %0d", selected_channel);

        // Test Case 4: Highest Priority Channel
        requests = 4'b1001;  // Channels 0 and 3
        #10;
        $display("Test Case 4 - Highest Priority: Selected Channel = %0d", selected_channel);

        // Finish simulation
        #10 $finish;
    end

    // VCD Dump
    initial begin
        $dumpfile("priority_encoder_tb.vcd");
        $dumpvars(0, priority_encoder_tb);
    end
endmodule

`timescale 1ns/1ps

module address_generator_tb;
    parameter ADDR_WIDTH = 32;
    parameter NUM_CHANNELS = 4;

    // Inputs
    reg clk, rst_n;
    reg [2:0] selected_channel;
    reg [NUM_CHANNELS-1:0] channel_req;

    // Outputs
    wire [ADDR_WIDTH-1:0] src_addr;
    wire [ADDR_WIDTH-1:0] dest_addr;

    // Instantiate the Unit Under Test (UUT)
    address_generator #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .NUM_CHANNELS(NUM_CHANNELS)
    ) uut (
        .clk(clk),
        .rst_n(rst_n),
        .selected_channel(selected_channel),
        .channel_req(channel_req),
        .src_addr(src_addr),
        .dest_addr(dest_addr)
    );

    // Clock Generation
    always #5 clk = ~clk;

    // Stimulus
    initial begin
        // Initialize Signals
        clk = 0;
        rst_n = 0;
        selected_channel = 0;
        channel_req = 0;

        // Reset Sequence
        #10 rst_n = 1;

        // Test Case 1: Channel 0 Transfer
        selected_channel = 0;
        channel_req = 4'b0001;
        #10;
        $display("Channel 0 - Src Addr: %h, Dest Addr: %h", src_addr, dest_addr);

        // Test Case 2: Multiple Transfers on Channel 0
        repeat(3) begin
            #10;
            $display("Channel 0 - Src Addr: %h, Dest Addr: %h", src_addr, dest_addr);
        end

        // Test Case 3: Channel 1 Transfer
        selected_channel = 1;
        channel_req = 4'b0010;
        #10;
        $display("Channel 1 - Src Addr: %h, Dest Addr: %h", src_addr, dest_addr);

        // Finish simulation
        #10 $finish;
    end

    // VCD Dump
    initial begin
        $dumpfile("address_generator_tb.vcd");
        $dumpvars(0, address_generator_tb);
    end
endmodule

`timescale 1ns/1ps

module transfer_controller_tb();
    // Parameters
    parameter ADDR_WIDTH = 32;
    parameter DATA_WIDTH = 32;
    parameter CLK_PERIOD = 10; // 10ns clock period

    // Testbench signals
    reg clk;
    reg rst_n;
    reg [ADDR_WIDTH-1:0] src_addr;
    reg [ADDR_WIDTH-1:0] dest_addr;
    wire [ADDR_WIDTH-1:0] mem_addr;
    wire [DATA_WIDTH-1:0] mem_data_out;
    reg [DATA_WIDTH-1:0] mem_data_in;
    wire mem_read_en;
    wire mem_write_en;
    wire transfer_valid;
    wire transfer_ready;

    // Memory simulation
    reg [DATA_WIDTH-1:0] memory [0:255];

    // Instantiate the DUT (Device Under Test)
    transfer_controller #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .src_addr(src_addr),
        .dest_addr(dest_addr),
        .mem_addr(mem_addr),
        .mem_data_out(mem_data_out),
        .mem_data_in(mem_data_in),
        .mem_read_en(mem_read_en),
        .mem_write_en(mem_write_en),
        .transfer_valid(transfer_valid),
        .transfer_ready(transfer_ready)
    );

    // Clock generation
    always begin
        #(CLK_PERIOD/2) clk = ~clk;
    end

    // Memory read/write simulation
    always @(posedge clk) begin
        if (mem_read_en) begin
            // Simulate memory read
            mem_data_in <= memory[mem_addr[9:2]];
        end
        
        if (mem_write_en) begin
            // Simulate memory write
            memory[mem_addr[9:2]] <= mem_data_out;
        end
    end

    // Testbench stimulus
    initial begin
        // Initialize signals
        clk = 0;
        rst_n = 0;
        src_addr = 0;
        dest_addr = 0;
        mem_data_in = 0;

        // Initialize memory with test data
        for (integer i = 0; i < 256; i = i + 1) begin
            memory[i] = i * 16;  // Some pattern for testing
        end

        // Reset sequence
        #(CLK_PERIOD * 2);
        rst_n = 1;

        // Test Case 1: Basic Transfer
        @(posedge clk);
        src_addr = 32'h00000010;  // Source start address
        dest_addr = 32'h00000050;  // Destination start address
        
        // Wait for transfer to complete
        @(posedge transfer_ready);
        
        // Verify transfer
        #(CLK_PERIOD * 2);
        
        // Test Case 2: Another Transfer
        src_addr = 32'h00000020;
        dest_addr = 32'h00000060;
        
        // Wait for transfer to complete
        @(posedge transfer_ready);
        
        // Final verification and end simulation
        #(CLK_PERIOD * 5);
        $display("Testbench completed");
        $finish;
    end

    // Optional: Waveform dumping for simulation
    initial begin
        $dumpfile("transfer_controller_tb.vcd");
        $dumpvars(0, transfer_controller_tb);
    end

    // Optional: Verification of transfers
    always @(posedge transfer_ready) begin
        $display("Transfer Complete:");
        $display("Source Address: %h", src_addr);
        $display("Destination Address: %h", dest_addr);
        
        // Quick verification of transfer
        for (integer i = 0; i < 4; i = i + 1) begin
            $display("Memory[%0d]: %h -> %h", 
                     (dest_addr[9:2] + i), 
                     memory[src_addr[9:2] + i], 
                     memory[dest_addr[9:2] + i]);
        end
    end

    // Timeout to prevent infinite simulation
    initial begin
        #(CLK_PERIOD * 100);
        $display("Testbench timed out");
        $finish;
    end
endmodule

`timescale 1ns/1ps

module interrupt_controller_tb;
    parameter NUM_CHANNELS = 4;

    // Inputs
    reg clk, rst_n;
    reg [NUM_CHANNELS-1:0] channel_complete;
    reg [NUM_CHANNELS-1:0] peripheral_req;

    // Outputs
    wire [NUM_CHANNELS-1:0] peripheral_ack;
    wire dma_interrupt;

    // Instantiate the Unit Under Test (UUT)
    interrupt_controller #(
        .NUM_CHANNELS(NUM_CHANNELS)
    ) uut (
        .clk(clk),
        .rst_n(rst_n),
        .channel_complete(channel_complete),
        .peripheral_req(peripheral_req),
        .peripheral_ack(peripheral_ack),
        .dma_interrupt(dma_interrupt)
    );

    // Clock Generation
    always #5 clk = ~clk;

    // Stimulus
    initial begin
        // Initialize Signals
        clk = 0;
        rst_n = 0;
        channel_complete = 'b0;
        peripheral_req = 'b0;

        // Reset Sequence
        #10 rst_n = 1;

        // Test Case 1: No Channels Completed
        #10;
        $display("No Channels Completed - Interrupt: %b, Peripheral Ack: %b", 
                 dma_interrupt, peripheral_ack);

        // Test Case 2: Single Channel Completion
        channel_complete = 4'b0010;  // Channel 1 completed
        #10;
        $display("Channel 1 Completed - Interrupt: %b, Peripheral Ack: %b", 
                 dma_interrupt, peripheral_ack);

        // Test Case 3: Multiple Channels Completed
        channel_complete = 4'b1010;  // Channels 1 and 3 completed
        #10;
        $display("Channels 1 & 3 Completed - Interrupt: %b, Peripheral Ack: %b", 
                 dma_interrupt, peripheral_ack);

        // Test Case 4: Peripheral Request with Channel Completion
        peripheral_req = 4'b1100;  // Channels 2 and 3 requested
        #10;
        $display("Peripheral Req & Channel Completion - Interrupt: %b, Peripheral Ack: %b", 
                 dma_interrupt, peripheral_ack);

        // Finish simulation
        #10 $finish;
    end

    // VCD Dump
    initial begin
        $dumpfile("interrupt_controller_tb.vcd");
        $dumpvars(0, interrupt_controller_tb);
    end
endmodule

`timescale 1ns/1ps

module channel_status_controller_tb;
    parameter NUM_CHANNELS = 4;

    // Inputs
    reg clk, rst_n;
    reg [NUM_CHANNELS-1:0] channel_req;
    reg transfer_complete;

    // Outputs
    wire [NUM_CHANNELS-1:0] channel_active;
    wire [NUM_CHANNELS-1:0] channel_complete;

    // Instantiate the Unit Under Test (UUT)
    channel_status_controller #(
        .NUM_CHANNELS(NUM_CHANNELS)
    ) uut (
        .clk(clk),
        .rst_n(rst_n),
        .channel_req(channel_req),
        .transfer_complete(transfer_complete),
        .channel_active(channel_active),
        .channel_complete(channel_complete)
    );

    // Clock Generation
    always #5 clk = ~clk;

    // Stimulus
    initial begin
        // Initialize Signals
        clk = 0;
        rst_n = 0;
        channel_req = 'b0;
        transfer_complete = 0;

        // Reset Sequence
        #10 rst_n = 1;

        // Test Case 1: No Channel Requests
        #10;
        $display("No Requests - Active: %b, Complete: %b", channel_active, channel_complete);

        // Test Case 2: Single Channel Request
        channel_req = 4'b0010;  // Channel 1 request
        #10;
        $display("Channel 1 Requested - Active: %b, Complete: %b", channel_active, channel_complete);

        // Test Case 3: Transfer Completion
        transfer_complete = 1;
        #10;
        $display("Transfer Complete - Active: %b, Complete: %b", channel_active, channel_complete);

        // Test Case 4: Multiple Channel Requests
        channel_req = 4'b1010;  // Channels 1 and 3 requested
        transfer_complete = 0;
        #10;
        $display("Channels 1 & 3 Requested - Active: %b, Complete: %b", channel_active, channel_complete);

        // Test Case 5: Transfer Completion with Multiple Channels
        transfer_complete = 1;
        #10;
        $display("Multiple Channels Complete - Active: %b, Complete: %b", channel_active, channel_complete);

        // Finish simulation
        #10 $finish;
    end

    // VCD Dump
    /*initial begin
        $dumpfile("channel_status_controller_tb.vcd");
        $dumpvars(0, channel_status_controller_tb);
    end*/
endmodule
