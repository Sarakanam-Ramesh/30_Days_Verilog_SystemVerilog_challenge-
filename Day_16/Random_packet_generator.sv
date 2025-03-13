`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11.03.2025 11:29:29
// Design Name: 
// Module Name: Random_packet_generator
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


// Packet definition module (RTL)
module packet_processor_16 (
    input logic clk,
    input logic rst_n,
    input logic [7:0] data_in,
    input logic valid_in,
    output logic [7:0] data_out,
    output logic valid_out
);
    // Simple RTL to process packets
    // In a real design, this would do something meaningful with packet data
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            data_out <= 8'h00;
            valid_out <= 1'b0;
        end else begin
            data_out <= valid_in ? data_in : data_out;
            valid_out <= valid_in;
        end
    end
endmodule

// Testbench with random packet generation
module packet_processor_16_tb;
    // Testbench signals
    logic clk;
    logic rst_n;
    logic [7:0] data_in;
    logic valid_in;
    logic [7:0] data_out;
    logic valid_out;
    
    // Instantiate the DUT
    packet_processor_16 DUT (
        .clk(clk),
        .rst_n(rst_n),
        .data_in(data_in),
        .valid_in(valid_in),
        .data_out(data_out),
        .valid_out(valid_out)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // Packet class definition with randomization
    class Packet;
        rand bit [7:0] header;
        rand bit [7:0] payload[];
        rand bit [7:0] checksum;
        
        // Constrain payload size between 2 and 10 bytes
        constraint payload_size { payload.size() inside {[2:10]}; }
        
        // Generate a simple checksum (for demonstration)
        function void post_randomize();
            checksum = header;
            foreach (payload[i])
                checksum = checksum ^ payload[i]; // Simple XOR checksum
        endfunction
        
        // Display the packet contents
        function void display();
            $display("Packet Header: 0x%h", header);
            $display("Payload Size: %0d bytes", payload.size());
            foreach (payload[i])
                $display("  Payload[%0d]: 0x%h", i, payload[i]);
            $display("Checksum: 0x%h", checksum);
        endfunction
    endclass
    
    // Test stimulus
    initial begin
        Packet pkt;
        
        // Initialize signals
        rst_n = 0;
        valid_in = 0;
        data_in = 0;
        
        // Reset
        #20 rst_n = 1;
        
        // Generate and send 5 random packets
        repeat (5) begin
            pkt = new();
            assert(pkt.randomize()) else $fatal("Randomization failed");
            pkt.display();
            
            // Send header
            @(posedge clk);
            data_in = pkt.header;
            valid_in = 1;
            @(posedge clk);
            valid_in = 0;
            
            // Send payload
            foreach (pkt.payload[i]) begin
                @(posedge clk);
                data_in = pkt.payload[i];
                valid_in = 1;
                @(posedge clk);
                valid_in = 0;
            end
            
            // Send checksum
            @(posedge clk);
            data_in = pkt.checksum;
            valid_in = 1;
            @(posedge clk);
            valid_in = 0;
            
            // Wait a bit between packets
            repeat (3) @(posedge clk);
        end
        
        // End simulation
        #50 $finish;
    end
    
    // Monitor the output
    initial begin
        $monitor("At time %0t: valid_out=%b, data_out=0x%h", $time, valid_out, data_out);
    end
endmodule
