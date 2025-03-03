`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 02.03.2025 11:23:57
// Design Name: 
// Module Name: memory_interface_tb
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

module memory_interface_tb;
    // Clock and reset
    reg        clk;
    reg        rst_n;
    
    // Host interface signals
    reg        req;
    reg        wr_en;
    reg [15:0] addr;
    reg [31:0] wdata;
    wire [31:0] rdata;
    wire       ready;
    
    // Memory interface signals
    wire        mem_cs;
    wire        mem_we;
    wire [15:0] mem_addr;
    wire [31:0] mem_wdata;
    reg  [31:0] mem_rdata;
    reg         mem_ack;
    
    // Memory model (simple RAM)
    reg [31:0] mem [0:1023];
    integer i;
    // Instantiate DUT
    memory_interface dut (
        .clk(clk),
        .rst_n(rst_n),
        .req(req),
        .wr_en(wr_en),
        .addr(addr),
        .wdata(wdata),
        .rdata(rdata),
        .ready(ready),
        .mem_cs(mem_cs),
        .mem_we(mem_we),
        .mem_addr(mem_addr),
        .mem_wdata(mem_wdata),
        .mem_rdata(mem_rdata),
        .mem_ack(mem_ack)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 100MHz clock
    end
    
    // Memory model behavior
    always @(posedge clk) begin
        if (mem_cs) begin
            if (mem_we) begin
                mem[mem_addr[9:0]] <= mem_wdata;
            end
            mem_rdata <= mem[mem_addr[9:0]];
            mem_ack <= 1'b1;
        end
        else begin
            mem_ack <= 1'b0;
        end
    end
    
    // Test stimulus
    initial begin
        // Initialize signals
        rst_n = 0;
        req = 0;
        wr_en = 0;
        addr = 0;
        wdata = 0;
        mem_rdata = 0;
        mem_ack = 0;
        
        // Initialize memory with test values
        for ( i = 0; i < 1024; i = i + 1) begin
            mem[i] = i;
        end
        
        // Apply reset
        #20 rst_n = 1;
        #10;
        
        // Test Case 1: Write Operation
        $display("\nTest Case 1: Write Operation");
        req = 1;
        wr_en = 1;
        addr = 16'h00A0;
        wdata = 32'hDEADBEEF;
        
        @(posedge ready);
        #10;
        req = 0;
        wr_en = 0;
        
        #20;
        
        // Test Case 2: Read Operation
        $display("\nTest Case 2: Read Operation");
        req = 1;
        wr_en = 0;
        addr = 16'h00A0;
        
        @(posedge ready);
        #10;
        req = 0;
        
        // Verify read data
        if (rdata === 32'hDEADBEEF)
            $display("Read verification successful: %h", rdata);
        else
            $display("Read verification failed: Expected %h, Got %h", 32'hDEADBEEF, rdata);
        
        // Test Case 3: Multiple Operations
        $display("\nTest Case 3: Multiple Operations");
        for ( i = 0; i < 5; i = i + 1) begin
            // Write
            #20;
            req = 1;
            wr_en = 1;
            addr = 16'h0100 + i;
            wdata = 32'hA5A50000 + i;
            
            @(posedge ready);
            #10;
            req = 0;
            wr_en = 0;
            
            // Read back
            #20;
            req = 1;
            wr_en = 0;
            addr = 16'h0100 + i;
            
            @(posedge ready);
            #10;
            req = 0;
            
            // Verify
            if (rdata === (32'hA5A50000 + i))
                $display("Iteration %0d: Read verification successful: %h", i, rdata);
            else
                $display("Iteration %0d: Read verification failed: Expected %h, Got %h", i, 32'hA5A50000 + i, rdata);
        end
        
        // End simulation
        #50;
        $display("Simulation complete");
        $finish;
    end
    
endmodule