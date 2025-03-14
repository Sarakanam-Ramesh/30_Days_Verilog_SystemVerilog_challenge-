`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 13.03.2025 14:21:26
// Design Name: 
// Module Name: Parameterized_modules
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


module parameterized_fifo_19 #(
    parameter DATA_WIDTH = 8,
    parameter FIFO_DEPTH = 16,
    parameter ALMOST_FULL_THRESHOLD = FIFO_DEPTH - 2,
    parameter ALMOST_EMPTY_THRESHOLD = 2,
    // Derived parameters - do not override
    parameter ADDR_WIDTH = $clog2(FIFO_DEPTH)
)(
    input wire clk,
    input wire rst_n,
    
    // Write interface
    input wire wr_en,
    input wire [DATA_WIDTH-1:0] wr_data,
    output wire full,
    output wire almost_full,
    
    // Read interface
    input wire rd_en,
    output wire [DATA_WIDTH-1:0] rd_data,
    output wire empty,
    output wire almost_empty,
    
    // Status
    output wire [ADDR_WIDTH:0] fifo_count
);
    // Internal registers
    reg [DATA_WIDTH-1:0] mem [0:FIFO_DEPTH-1];
    reg [ADDR_WIDTH:0] wr_ptr;
    reg [ADDR_WIDTH:0] rd_ptr;
    
    // Status signals
    wire [ADDR_WIDTH:0] fifo_count_next;
    
    // FIFO control logic
    assign fifo_count = wr_ptr - rd_ptr;
    assign fifo_count_next = fifo_count + (wr_en & ~full) - (rd_en & ~empty);
    
    // Status flags
    assign empty = (fifo_count == 0);
    assign almost_empty = (fifo_count <= ALMOST_EMPTY_THRESHOLD);
    assign full = (fifo_count >= FIFO_DEPTH);
    assign almost_full = (fifo_count >= ALMOST_FULL_THRESHOLD);
    
    // Write pointer logic
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            wr_ptr <= 0;
        else if (wr_en && !full)
            wr_ptr <= wr_ptr + 1;
    end
    
    // Read pointer logic
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            rd_ptr <= 0;
        else if (rd_en && !empty)
            rd_ptr <= rd_ptr + 1;
    end
    
    // Memory write
    always @(posedge clk) begin
        if (wr_en && !full)
            mem[wr_ptr[ADDR_WIDTH-1:0]] <= wr_data;
    end
    
    // Memory read
    assign rd_data = mem[rd_ptr[ADDR_WIDTH-1:0]];
    
endmodule

`timescale 1ns/1ps

module parameterized_fifo_19_tb();
    // Define parameters for testing
    localparam DATA_WIDTH = 8;
    localparam FIFO_DEPTH = 8;
    localparam ALMOST_FULL_THRESHOLD = 6;
    localparam ALMOST_EMPTY_THRESHOLD = 2;
    localparam ADDR_WIDTH = $clog2(FIFO_DEPTH);
    
    // Testbench signals
    reg clk;
    reg rst_n;
    reg wr_en;
    reg [DATA_WIDTH-1:0] wr_data;
    wire full;
    wire almost_full;
    reg rd_en;
    wire [DATA_WIDTH-1:0] rd_data;
    wire empty;
    wire almost_empty;
    wire [ADDR_WIDTH:0] fifo_count;
    
    // Instantiate the FIFO with parameters
    parameterized_fifo_19 #(
        .DATA_WIDTH(DATA_WIDTH),
        .FIFO_DEPTH(FIFO_DEPTH),
        .ALMOST_FULL_THRESHOLD(ALMOST_FULL_THRESHOLD),
        .ALMOST_EMPTY_THRESHOLD(ALMOST_EMPTY_THRESHOLD)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .wr_en(wr_en),
        .wr_data(wr_data),
        .full(full),
        .almost_full(almost_full),
        .rd_en(rd_en),
        .rd_data(rd_data),
        .empty(empty),
        .almost_empty(almost_empty),
        .fifo_count(fifo_count)
    );
    
    // Clock generation
    always #5 clk = ~clk;
    
    // Test sequence
    initial begin
        // Initialize signals
        clk = 0;
        rst_n = 0;
        wr_en = 0;
        wr_data = 0;
        rd_en = 0;
        
        // Apply reset
        #20 rst_n = 1;
        
        // Fill FIFO
        #10;
        repeat (6) begin
            wr_en = 1;
            wr_data = wr_data + 8'h11;
            #10;
        end
        wr_en = 0;
        
        // Check almost_full flag
        #10;
        
        // Read a few values
        repeat (3) begin
            rd_en = 1;
            #10;
        end
        rd_en = 0;
        
        // Check almost_empty flag
        #10;
        
        // Fill until full
        wr_data = 8'h55;
        repeat (5) begin
            wr_en = 1;
            wr_data = wr_data + 8'h11;
            #10;
        end
        wr_en = 0;
        
        // Try to write when full
        #10 wr_en = 1;
        wr_data = 8'hFF;
        #10 wr_en = 0;
        
        // Empty the FIFO
        #10;
        repeat (8) begin
            rd_en = 1;
            #10;
        end
        rd_en = 0;
        
        // Try to read when empty
        #10 rd_en = 1;
        #10 rd_en = 0;
        
        // End simulation
        $display("Simulation complete");
        $finish;
    end
    
    // Monitor
    always @(posedge clk) begin
        $display("Time=%0t, Count=%d, WR=%b, Data_In=%h, RD=%b, Data_Out=%h, Full=%b, Almost_Full=%b, Empty=%b, Almost_Empty=%b", 
                 $time, fifo_count, wr_en, wr_data, rd_en, rd_data, full, almost_full, empty, almost_empty);
    end
endmodule