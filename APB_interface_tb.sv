`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 02.03.2025 11:39:56
// Design Name: 
// Module Name: APB_interface_tb
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

module apb_interface_tb;
    // Clock and reset
    logic clk;
    logic rst_n;
    
    // APB interface
    apb_if apb_bus (
        .pclk(clk),
        .preset_n(rst_n)
    );
    
    // Master control signals
    logic        req;
    logic        write;
    logic [31:0] addr;
    logic [31:0] wdata;
    logic [31:0] rdata;
    logic        ready;
    
    // Instantiate APB master
    apb_master u_master (
        .clk(clk),
        .rst_n(rst_n),
        .req(req),
        .write(write),
        .addr(addr),
        .wdata(wdata),
        .rdata(rdata),
        .ready(ready),
        .apb(apb_bus.master)
    );
    
    // Instantiate APB slave
    apb_slave u_slave (
        .apb(apb_bus.slave),
        .clk(clk),
        .rst_n(rst_n)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 100MHz clock
    end
    
    // Task for executing APB transfers (module level)
task automatic apb_transfer(input bit is_write, input [31:0] address, 
                           input [31:0] write_data, output [31:0] read_data);
    req   = 1'b1;
    write = is_write;
    addr  = address;
    wdata = write_data;
    
    @(posedge ready);
    #1 req = 1'b0;
    read_data = rdata;
    #10;
endtask

    // Test stimulus
    initial begin
        // Initialize signals
        rst_n = 0;
        req = 0;
        write = 0;
        addr = 0;
        wdata = 0;
        
        // Apply reset
        #20 rst_n = 1;
        #10;

        
        // Test Case 1: Read from registers
        $display("\nTest Case 1: Read Initial Register Values");
        for (int i = 0; i < 8; i++) begin
            logic [31:0] rd_data;
            apb_transfer(0, i<<2, 0, rd_data);  // Read operation
            $display("Register %0d: %h", i, rd_data);
        end
        
        // Test Case 2: Write to registers
        $display("\nTest Case 2: Write to Registers");
        for (int i = 0; i < 8; i++) begin
            logic [31:0] wr_data = 32'hA000_0000 | i;
            logic [31:0] rd_data;
            
            // Write
            apb_transfer(1, i<<2, wr_data, rd_data);
            
            // Read back to verify
            apb_transfer(0, i<<2, 0, rd_data);
            
            // Check
            if (rd_data === wr_data)
                $display("Register %0d: Write/Read Success. Value: %h", i, rd_data);
            else
                $display("Register %0d: Write/Read FAILED. Expected: %h, Got: %h", i, wr_data, rd_data);
        end
        
        // Test Case 3: Access invalid address
        $display("\nTest Case 3: Access Invalid Address");
        begin
            logic [31:0] rd_data;
            
            // Read from invalid address
            apb_transfer(0, 32'h100, 0, rd_data);
            $display("Invalid Read: Got %h, pslverr=%b", rd_data, apb_bus.pslverr);
            
            // Write to invalid address
            apb_transfer(1, 32'h100, 32'hDEAD_BEEF, rd_data);
            $display("Invalid Write: pslverr=%b", apb_bus.pslverr);
        end
        
        // End simulation
        #50;
        $display("Simulation complete");
        $finish;
    end
    
    // Monitor APB transfers
    initial begin
        forever begin
            @(posedge clk);
            if (apb_bus.psel && apb_bus.penable && apb_bus.pready) begin
                if (apb_bus.pwrite)
                    $display("Time=%0t: APB WRITE: addr=%h, data=%h, slverr=%b", 
                             $time, apb_bus.paddr, apb_bus.pwdata, apb_bus.pslverr);
                else
                    $display("Time=%0t: APB READ: addr=%h, data=%h, slverr=%b", 
                             $time, apb_bus.paddr, apb_bus.prdata, apb_bus.pslverr);
            end
        end
    end
    
endmodule