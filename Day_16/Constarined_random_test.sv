`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11.03.2025 11:41:09
// Design Name: 
// Module Name: Constarined_random_test
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


// Memory interface module (RTL)
module memory_interface_16 (
    input logic clk,
    input logic rst_n,
    input logic [31:0] addr,
    input logic [31:0] write_data,
    input logic write_en,
    input logic read_en,
    output logic [31:0] read_data,
    output logic data_valid
);
    // Simple memory implementation (limited size for simulation)
    logic [31:0] mem [0:1023]; // 1K memory locations
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            read_data <= 32'h0;
            data_valid <= 1'b0;
        end else begin
            if (write_en) begin
                // Write operation
                if (addr < 1024) begin
                    mem[addr] <= write_data;
                end
                data_valid <= 1'b0;
            end else if (read_en) begin
                // Read operation
                if (addr < 1024) begin
                    read_data <= mem[addr];
                    data_valid <= 1'b1;
                end else begin
                    data_valid <= 1'b0;
                end
            end else begin
                data_valid <= 1'b0;
            end
        end
    end
endmodule

// Testbench with constrained random testing
module memory_interface_16_tb;
    // Testbench signals
    logic clk;
    logic rst_n;
    logic [31:0] addr;
    logic [31:0] write_data;
    logic write_en;
    logic read_en;
    logic [31:0] read_data;
    logic data_valid;
    
    // Instantiate the DUT
    memory_interface_16 DUT (
        .clk(clk),
        .rst_n(rst_n),
        .addr(addr),
        .write_data(write_data),
        .write_en(write_en),
        .read_en(read_en),
        .read_data(read_data),
        .data_valid(data_valid)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // Transaction class with constraints
    class MemTransaction;
        rand bit [31:0] addr;
        rand bit [31:0] data;
        rand bit is_write;
        
        // Constrain addresses to valid regions
        constraint addr_c {
            // Define memory regions
            addr inside {[0:255], [512:767], [900:1023]};
            
            // No writes to read-only region
            if (is_write) {
                !(addr inside {[900:1023]});
            }
        }
        
        // Constrain data pattern
        constraint data_c {
            // For some addresses, force specific data patterns
            if (addr inside {[0:100]}) {
                data[31:24] == 8'hA5;
            }
            else if (addr inside {[512:600]}) {
                data[7:0] == addr[7:0];
            }
        }
        
        // Display transaction details
        function void display();
            $display("Transaction: %s, Address: 0x%h, Data: 0x%h",
                    is_write ? "WRITE" : "READ", addr, data);
        endfunction
    endclass
    
    // Coverage definition
    covergroup mem_cov;
        option.per_instance = 1;
        
        // Cover address ranges
        addr_cp: coverpoint addr {
            bins low_range = {[0:255]};
            bins mid_range = {[512:767]};
            bins high_range = {[900:1023]};
        }
        
        // Cover operation types
        op_cp: coverpoint {write_en, read_en} {
            bins write_op = {2'b10};
            bins read_op = {2'b01};
            bins invalid_op = {2'b00, 2'b11};
        }
        
        // Cross coverage
        addr_op_cross: cross addr_cp, op_cp;
    endgroup
    
    // Test stimulus
    initial begin
        // Create instance of transaction class and coverage
        MemTransaction trans;
        mem_cov cov = new();
        
        // Initialize signals
        rst_n = 0;
        addr = 0;
        write_data = 0;
        write_en = 0;
        read_en = 0;
        
        // Reset sequence
        #20 rst_n = 1;
        
        // Run constrained random tests
        repeat (100) begin
            trans = new();
            assert(trans.randomize()) else $fatal("Randomization failed");
            trans.display();
            
            // Apply transaction to DUT
            @(posedge clk);
            addr = trans.addr;
            write_data = trans.data;
            write_en = trans.is_write;
            read_en = !trans.is_write;
            
            // Sample coverage
            cov.sample();
            
            // Wait for response
            @(posedge clk);
            write_en = 0;
            read_en = 0;
            
            // For reads, check if data is valid
            if (!trans.is_write) begin
                if (data_valid) begin
                    $display("Read data: 0x%h", read_data);
                end else begin
                    $display("Read did not return valid data");
                end
            end
            
            // Small delay between transactions
            #10;
        end
        
        // Report coverage
        $display("Coverage: %0.2f%%", cov.get_coverage());
        
        // End simulation
        #50 $finish;
    end
    
    // Error checking
    property valid_read_response;
        @(posedge clk) disable iff (!rst_n)
        read_en && addr < 1024 |=> data_valid;
    endproperty
    
    assert property (valid_read_response)
        else $error("Valid read did not produce valid data response");
endmodule