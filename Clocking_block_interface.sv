`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 02.03.2025 12:07:35
// Design Name: 
// Module Name: Clocking_block_tb
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

module spi_tb_top;
    // Clock and reset
    logic clk;
    logic rst_n;
    
    // Master control signals
    logic       start_transaction;
    logic [7:0] master_tx_data;
    logic [7:0] master_rx_data;
    logic       master_busy;
    logic       master_done;
    
    // Slave control signals
    logic [7:0] slave_tx_data;
    logic [7:0] slave_rx_data;
    logic       slave_rx_valid;
    
    // SPI interface
    spi_if spi_bus (
        .clk(clk),
        .rst_n(rst_n)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 100MHz clock
    end
    
    // Reset generation
    initial begin
        rst_n = 0;
        #20 rst_n = 1;
    end
    
    // Instantiate SPI master
    spi_master u_master (
        .clk(clk),
        .rst_n(rst_n),
        .start_transaction(start_transaction),
        .tx_data(master_tx_data),
        .rx_data(master_rx_data),
        .busy(master_busy),
        .done(master_done),
        .spi(spi_bus.master)
    );
    
    // Instantiate SPI slave
    spi_slave u_slave (
        .clk(clk),
        .rst_n(rst_n),
        .tx_data(slave_tx_data),
        .rx_data(slave_rx_data),
        .rx_valid(slave_rx_valid),
        .spi(spi_bus.slave)
    );
    
    // Instantiate test program
    spi_test u_test (
        .clk(clk),
        .rst_n(rst_n),
        .start_transaction(start_transaction),
        .master_tx_data(master_tx_data),
        .master_rx_data(master_rx_data),
        .master_busy(master_busy),
        .master_done(master_done),
        .slave_tx_data(slave_tx_data),
        .slave_rx_data(slave_rx_data),
        .slave_rx_valid(slave_rx_valid),
        .monitor_if(spi_bus.tb_monitor)
    );
    
endmodule

program automatic spi_test (
    input  logic       clk,
    input  logic       rst_n,
    output logic       start_transaction,
    output logic [7:0] master_tx_data,
    input  logic [7:0] master_rx_data,
    input  logic       master_busy,
    input  logic       master_done,
    output logic [7:0] slave_tx_data,
    input  logic [7:0] slave_rx_data,
    input  logic       slave_rx_valid,
    spi_if.tb_monitor  monitor_if
);
    // Sequence item class
    class spi_transaction;
        rand bit [7:0] master_data;
        rand bit [7:0] slave_data;
        bit [7:0] captured_master_rx;
        bit [7:0] captured_slave_rx;
        
        function void display(string tag="");
            $display("Time=%0t: %s - Master TX=%h, Slave TX=%h, Master RX=%h, Slave RX=%h", 
                     $time, tag, master_data, slave_data, captured_master_rx, captured_slave_rx);
        endfunction
    endclass
    
    // Mailbox for transactions
    mailbox #(spi_transaction) gen2drv = new();
    
    // Generator process
    task automatic generator(int num_transactions);
        for (int i = 0; i < num_transactions; i++) begin
            spi_transaction tr = new();
            assert(tr.randomize());
            gen2drv.put(tr);
            $display("Time=%0t: Generated transaction %0d - Master TX=%h, Slave TX=%h", 
                     $time, i, tr.master_data, tr.slave_data);
            #10;
        end
    endtask
    
    // Driver process
    task automatic driver();
        spi_transaction tr;
        
        forever begin
            // Get transaction from mailbox
            gen2drv.get(tr);
            
            // Drive transaction
            @(posedge clk);
            master_tx_data = tr.master_data;
            slave_tx_data = tr.slave_data;
            start_transaction = 1'b1;
            
            @(posedge clk);
            start_transaction = 1'b0;
            
            // Wait for transaction to complete
            wait(master_done);
            @(posedge clk);
            
            // Capture results
            tr.captured_master_rx = master_rx_data;
            tr.captured_slave_rx = slave_rx_data;
            
            // Display results
            tr.display("Completed");
            
            // Check data
            if (tr.captured_master_rx === tr.slave_data && tr.captured_slave_rx === tr.master_data)
                $display("Time=%0t: PASS - Data correctly transferred in both directions", $time);
            else
                $display("Time=%0t: FAIL - Data mismatch! Expected: Master RX=%h, Slave RX=%h", 
                         $time, tr.slave_data, tr.master_data);
            
            #20;
        end
    endtask
    
    // Monitor using clocking block
    task automatic monitor();
        forever begin
            @(monitor_if.cb_monitor);
            
            if (!monitor_if.cb_monitor.cs_n) begin
                // Display sampled signals
                $display("Time=%0t: Monitor - SCLK=%b, CS_N=%b, MOSI=%b, MISO=%b", 
                         $time, monitor_if.cb_monitor.sclk, monitor_if.cb_monitor.cs_n, 
                         monitor_if.cb_monitor.mosi, monitor_if.cb_monitor.miso);
            end
        end
    endtask
    
    // Main test sequence
    initial begin
        // Initialize signals
        start_transaction = 0;
        master_tx_data = 0;
        slave_tx_data = 0;
        
        // Wait for reset to complete
        wait(rst_n);
        #20;
        
        // Start processes
        fork
            generator(10);
            driver();
            monitor();
        join_any
        
        // Wait for all transactions to complete
        #200;
        $display("Test complete");
        $finish;
    end
    
endprogram

