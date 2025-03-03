`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 02.03.2025 11:18:35
// Design Name: 
// Module Name: simple_bus_tb
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

module simple_bus_tb;
    // Clock and reset
    reg        clk;
    reg        rst_n;
    
    // Master signals
    reg        m_req;
    reg        m_rw;
    reg  [7:0] m_addr;
    reg  [7:0] m_wdata;
    wire [7:0] m_rdata;
    wire       m_valid;
    
    // Slave signals
    wire       s_req;
    wire       s_rw;
    wire [7:0] s_addr;
    wire [7:0] s_wdata;
    reg  [7:0] s_rdata;
    reg        s_valid;
    
    // Instantiate DUT
    simple_bus dut (
        .clk(clk),
        .rst_n(rst_n),
        .m_req(m_req),
        .m_rw(m_rw),
        .m_addr(m_addr),
        .m_wdata(m_wdata),
        .m_rdata(m_rdata),
        .m_valid(m_valid),
        .s_req(s_req),
        .s_rw(s_rw),
        .s_addr(s_addr),
        .s_wdata(s_wdata),
        .s_rdata(s_rdata),
        .s_valid(s_valid)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 100MHz clock
    end
    
    // Test stimulus
    initial begin
        // Initialize signals
        rst_n = 0;
        m_req = 0;
        m_rw = 0;
        m_addr = 0;
        m_wdata = 0;
        s_rdata = 0;
        s_valid = 0;
        
        // Reset
        #20 rst_n = 1;
        
        // Test Case 1: Write operation
        #10;
        m_req = 1;
        m_rw = 0;  // Write
        m_addr = 8'hA5;
        m_wdata = 8'h37;
        
        #10;
        // Simulate slave response
        s_valid = 1;
        
        #10;
        m_req = 0;
        s_valid = 0;
        
        // Test Case 2: Read operation
        #20;
        m_req = 1;
        m_rw = 1;  // Read
        m_addr = 8'h42;
        
        // Simulate slave response
        #10;
        s_rdata = 8'hBE;
        s_valid = 1;
        
        #10;
        m_req = 0;
        s_valid = 0;
        
        // End simulation
        #20;
        $display("Simulation complete");
        $finish;
    end
    
    // Monitor bus transactions
    initial begin
        $monitor("Time=%0t: m_req=%b, m_rw=%b, m_addr=%h, m_wdata=%h, m_rdata=%h, m_valid=%b", 
                 $time, m_req, m_rw, m_addr, m_wdata, m_rdata, m_valid);
    end
    
endmodule
