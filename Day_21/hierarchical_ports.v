`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 13.03.2025 23:12:10
// Design Name: 
// Module Name: Hierarchical_ports
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


// Hierarchical Ports Module (RTL)
// This module demonstrates hierarchical port connections in Verilog
// with a system containing a controller and multiple sub-modules

module hierarchical_ports #(
    parameter SUB_MODULES = 4,
    parameter ADDR_WIDTH = 8,
    parameter DATA_WIDTH = 32
)(
    input  wire                     clk,
    input  wire                     rst_n,
    
    // Top-level control interface
    input  wire                     cmd_valid_i,
    input  wire [ADDR_WIDTH-1:0]    cmd_addr_i,
    input  wire                     cmd_read_i,
    input  wire [DATA_WIDTH-1:0]    cmd_wdata_i,
    output wire                     cmd_ready_o,
    
    // Top-level response interface
    output wire                     resp_valid_o,
    output wire [DATA_WIDTH-1:0]    resp_data_o,
    input  wire                     resp_ready_i
);

    // Submodule selection based on address range
    reg [SUB_MODULES-1:0] submodule_select;
    reg [$clog2(SUB_MODULES)-1:0] active_submodule;
    
    // Command broadcast to all submodules (hierarchical connection)
    wire                  cmd_valid;
    wire [ADDR_WIDTH-1:0] cmd_addr;
    wire                  cmd_read;
    wire [DATA_WIDTH-1:0] cmd_wdata;
    wire [SUB_MODULES-1:0] cmd_ready;
    
    // Response from submodules (hierarchical connection)
    wire [SUB_MODULES-1:0]              resp_valid;
    wire [SUB_MODULES*DATA_WIDTH-1:0]   resp_data;
    wire                                resp_ready;
    
    // Top-level to internal connections
    assign cmd_valid = cmd_valid_i;
    assign cmd_addr = cmd_addr_i;
    assign cmd_read = cmd_read_i;
    assign cmd_wdata = cmd_wdata_i;
    assign cmd_ready_o = cmd_ready[active_submodule];
    
    assign resp_valid_o = resp_valid[active_submodule];
    assign resp_data_o = resp_data[active_submodule*DATA_WIDTH +: DATA_WIDTH];
    assign resp_ready = resp_ready_i;
    
    // Address decoder to select the target submodule
    always @(*) begin
        // Simple address decoding - each submodule gets a range
        active_submodule = cmd_addr_i[ADDR_WIDTH-1:ADDR_WIDTH-$clog2(SUB_MODULES)];
        submodule_select = (1 << active_submodule);
    end
    
    // Generate SUB_MODULES instances
    genvar i;
    generate
        for (i = 0; i < SUB_MODULES; i = i + 1) begin : submodule_gen
            submodule #(
                .ADDR_WIDTH(ADDR_WIDTH),
                .DATA_WIDTH(DATA_WIDTH),
                .MODULE_ID(i)
            ) submod_inst (
                .clk(clk),
                .rst_n(rst_n),
                .enable_i(submodule_select[i]),
                
                // Command interface (hierarchical)
                .cmd_valid_i(cmd_valid),
                .cmd_addr_i(cmd_addr),
                .cmd_read_i(cmd_read),
                .cmd_wdata_i(cmd_wdata),
                .cmd_ready_o(cmd_ready[i]),
                
                // Response interface (hierarchical)
                .resp_valid_o(resp_valid[i]),
                .resp_data_o(resp_data[i*DATA_WIDTH +: DATA_WIDTH]),
                .resp_ready_i(resp_ready)
            );
        end
    endgenerate

endmodule

// Submodule definition
module submodule #(
    parameter ADDR_WIDTH = 8,
    parameter DATA_WIDTH = 32,
    parameter MODULE_ID = 0
)(
    input  wire                  clk,
    input  wire                  rst_n,
    input  wire                  enable_i,
    
    // Command interface
    input  wire                  cmd_valid_i,
    input  wire [ADDR_WIDTH-1:0] cmd_addr_i,
    input  wire                  cmd_read_i,
    input  wire [DATA_WIDTH-1:0] cmd_wdata_i,
    output wire                  cmd_ready_o,
    
    // Response interface
    output reg                   resp_valid_o,
    output reg  [DATA_WIDTH-1:0] resp_data_o,
    input  wire                  resp_ready_i
);

    // Simple memory implementation (16 locations)
    localparam MEM_DEPTH = 16;
    reg [DATA_WIDTH-1:0] mem [0:MEM_DEPTH-1];
    integer j;
    
    // Local address after dropping the module select bits
    wire [ADDR_WIDTH-$clog2(MODULE_ID+1)-1:0] local_addr;
    assign local_addr = cmd_addr_i[ADDR_WIDTH-$clog2(MODULE_ID+1)-1:0];
    
    // Command is ready when enabled and no pending response
    assign cmd_ready_o = enable_i && (!resp_valid_o || resp_ready_i);
    
    // Command processing
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            resp_valid_o <= 1'b0;
            resp_data_o <= {DATA_WIDTH{1'b0}};
            
            // Initialize memory with module ID pattern
            for (j = 0; j < MEM_DEPTH; j=j+1) begin
                mem[j] <= {DATA_WIDTH{1'b0}} | (MODULE_ID << 28) | j;
            end
        end
        else begin
            // Clear response when accepted
            if (resp_valid_o && resp_ready_i) begin
                resp_valid_o <= 1'b0;
            end
            
            // Process new command when enabled
            if (enable_i && cmd_valid_i && cmd_ready_o) begin
                if (cmd_read_i) begin
                    // Read operation
                    resp_data_o <= mem[local_addr[3:0]];  // Use lower 4 bits for memory addressing
                    resp_valid_o <= 1'b1;
                end
                else begin
                    // Write operation
                    mem[local_addr[3:0]] <= cmd_wdata_i;
                    // Send write acknowledgment
                    resp_data_o <= {DATA_WIDTH{1'b0}} | {8'hAA, 8'h55, 8'hAA, 8'h55};
                    resp_valid_o <= 1'b1;
                end
            end
        end
    end

endmodule

// Hierarchical Ports Testbench
`timescale 1ns/1ps

module hierarchical_ports_tb;
    // Parameters
    localparam SUB_MODULES = 4;
    localparam ADDR_WIDTH = 8;
    localparam DATA_WIDTH = 32;
    
    // Clock and reset
    reg clk = 0;
    reg rst_n = 0;
    
    // Top-level control interface
    reg                     cmd_valid_i;
    reg [ADDR_WIDTH-1:0]    cmd_addr_i;
    reg                     cmd_read_i;
    reg [DATA_WIDTH-1:0]    cmd_wdata_i;
    wire                    cmd_ready_o;
    
    // Top-level response interface
    wire                    resp_valid_o;
    wire [DATA_WIDTH-1:0]   resp_data_o;
    reg                     resp_ready_i;
    
    // Task for sending commands
    task send_command;
        input [ADDR_WIDTH-1:0] addr;
        input read;
        input [DATA_WIDTH-1:0] wdata;
        begin
            // Wait until the command interface is ready
            wait(cmd_ready_o);
            @(posedge clk);
            
            // Send command
            cmd_valid_i = 1'b1;
            cmd_addr_i = addr;
            cmd_read_i = read;
            cmd_wdata_i = wdata;
            
            @(posedge clk);
            cmd_valid_i = 1'b0;
            
            // Wait for response
            wait(resp_valid_o);
            @(posedge clk);
            resp_ready_i = 1'b1;
            
            @(posedge clk);
            resp_ready_i = 1'b0;
            
            // Add some idle cycles
            repeat(2) @(posedge clk);
        end
    endtask
    
    // DUT instantiation
    hierarchical_ports #(
        .SUB_MODULES(SUB_MODULES),
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .cmd_valid_i(cmd_valid_i),
        .cmd_addr_i(cmd_addr_i),
        .cmd_read_i(cmd_read_i),
        .cmd_wdata_i(cmd_wdata_i),
        .cmd_ready_o(cmd_ready_o),
        .resp_valid_o(resp_valid_o),
        .resp_data_o(resp_data_o),
        .resp_ready_i(resp_ready_i)
    );
    
    // Clock generation
    always #5 clk = ~clk;
    
    // Test sequence
    initial begin
        // Initialize signals
        cmd_valid_i = 0;
        cmd_addr_i = 0;
        cmd_read_i = 0;
        cmd_wdata_i = 0;
        resp_ready_i = 0;
        
        // Apply reset
        #10 rst_n = 0;
        #20 rst_n = 1;
        #10;
        
        // Test sequence
        
        // Test writes to each submodule (address MSB selects the submodule)
        $display("Writing to each submodule");
        send_command({2'b00, 6'h04}, 1'b0, 32'h12345678);  // Submodule 0, addr 4
        send_command({2'b01, 6'h08}, 1'b0, 32'h87654321);  // Submodule 1, addr 8
        send_command({2'b10, 6'h0C}, 1'b0, 32'hAABBCCDD);  // Submodule 2, addr C
        send_command({2'b11, 6'h10}, 1'b0, 32'h55667788);  // Submodule 3, addr 10
        
        // Read back from each submodule
        $display("Reading from each submodule");
        send_command({2'b00, 6'h04}, 1'b1, 32'h0);  // Submodule 0, addr 4
        send_command({2'b01, 6'h08}, 1'b1, 32'h0);  // Submodule 1, addr 8
        send_command({2'b10, 6'h0C}, 1'b1, 32'h0);  // Submodule 2, addr C
        send_command({2'b11, 6'h10}, 1'b1, 32'h0);  // Submodule 3, addr 10
        
        // Test rapid switching between submodules
        $display("Rapid switching between submodules");
        send_command({2'b00, 6'h00}, 1'b1, 32'h0);  // Submodule 0
        send_command({2'b01, 6'h00}, 1'b1, 32'h0);  // Submodule 1
        send_command({2'b10, 6'h00}, 1'b1, 32'h0);  // Submodule 2
        send_command({2'b11, 6'h00}, 1'b1, 32'h0);  // Submodule 3
        
        // End simulation
        #20;
        $display("Simulation completed successfully");
        $finish;
    end
    
    // Monitor
    always @(posedge clk) begin
        if (resp_valid_o && resp_ready_i) begin
            $display("Time: %0t, Response Data: 0x%h", $time, resp_data_o);
        end
    end
    
endmodule
