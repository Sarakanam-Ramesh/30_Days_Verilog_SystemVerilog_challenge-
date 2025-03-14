`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 13.03.2025 23:25:42
// Design Name: 
// Module Name: Bus_protocol
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


// Bus Protocol Module (RTL)
// This implements a simple bus protocol with handshaking, similar to AXI-Lite
// with separate address/data phases and transaction ID tracking

module bus_protocol #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32,
    parameter ID_WIDTH = 4
)(
    input  wire                     clk,
    input  wire                     rst_n,
    
    // Master interface (requestor)
    input  wire                     m_req_valid_i,
    input  wire [ADDR_WIDTH-1:0]    m_req_addr_i,
    input  wire                     m_req_write_i,
    input  wire [ID_WIDTH-1:0]      m_req_id_i,
    output wire                     m_req_ready_o,
    
    // Master write data channel
    input  wire                     m_data_valid_i,
    input  wire [DATA_WIDTH-1:0]    m_data_i,
    input  wire [DATA_WIDTH/8-1:0]  m_data_strb_i,
    output wire                     m_data_ready_o,
    
    // Master response channel
    output wire                     m_resp_valid_o,
    output wire [DATA_WIDTH-1:0]    m_resp_data_o,
    output wire [ID_WIDTH-1:0]      m_resp_id_o,
    output wire                     m_resp_error_o,
    input  wire                     m_resp_ready_i,
    
    // Slave interface (target)
    output wire                     s_req_valid_o,
    output wire [ADDR_WIDTH-1:0]    s_req_addr_o,
    output wire                     s_req_write_o,
    output wire [ID_WIDTH-1:0]      s_req_id_o,
    input  wire                     s_req_ready_i,
    
    // Slave write data channel
    output wire                     s_data_valid_o,
    output wire [DATA_WIDTH-1:0]    s_data_o,
    output wire [DATA_WIDTH/8-1:0]  s_data_strb_o,
    input  wire                     s_data_ready_i,
    
    // Slave response channel
    input  wire                     s_resp_valid_i,
    input  wire [DATA_WIDTH-1:0]    s_resp_data_i,
    input  wire [ID_WIDTH-1:0]      s_resp_id_i,
    input  wire                     s_resp_error_i,
    output wire                     s_resp_ready_o
);

    // Request path
    // Simply forward requests but track write transactions
    assign s_req_valid_o = m_req_valid_i;
    assign s_req_addr_o = m_req_addr_i;
    assign s_req_write_o = m_req_write_i;
    assign s_req_id_o = m_req_id_i;
    assign m_req_ready_o = s_req_ready_i;
    
    // Write data path
    assign s_data_valid_o = m_data_valid_i;
    assign s_data_o = m_data_i;
    assign s_data_strb_o = m_data_strb_i;
    assign m_data_ready_o = s_data_ready_i;
    
    // Response path
    assign m_resp_valid_o = s_resp_valid_i;
    assign m_resp_data_o = s_resp_data_i;
    assign m_resp_id_o = s_resp_id_i;
    assign m_resp_error_o = s_resp_error_i;
    assign s_resp_ready_o = m_resp_ready_i;
    
    // Protocol verification logic
    // This can be enhanced for more complex bus protocols
    
    // Check for ID matching between request and response
    reg [ID_WIDTH-1:0] last_req_id;
    
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            last_req_id <= {ID_WIDTH{1'b0}};
        end
        else if (m_req_valid_i && m_req_ready_o) begin
            last_req_id <= m_req_id_i;
        end
    end
    
    // Assert properties for protocol checking
    // These would be actual assertions in a verification environment
    // property id_match;
    //   @(posedge clk) disable iff (!rst_n)
    //   m_resp_valid_o |-> (m_resp_id_o == last_req_id);
    // endproperty
    // assert property(id_match);

endmodule

// Bus Protocol Testbench
`timescale 1ns/1ps

module bus_protocol_tb;
    // Parameters
    localparam ADDR_WIDTH = 32;
    localparam DATA_WIDTH = 32;
    localparam ID_WIDTH = 4;
    
    // Clock and reset
    reg clk = 0;
    reg rst_n = 0;
    
    // Master interface (requestor)
    reg                         m_req_valid_i;
    reg [ADDR_WIDTH-1:0]        m_req_addr_i;
    reg                         m_req_write_i;
    reg [ID_WIDTH-1:0]          m_req_id_i;
    wire                        m_req_ready_o;
    
    // Master write data channel
    reg                         m_data_valid_i;
    reg [DATA_WIDTH-1:0]        m_data_i;
    reg [DATA_WIDTH/8-1:0]      m_data_strb_i;
    wire                        m_data_ready_o;
    
    // Master response channel
    wire                        m_resp_valid_o;
    wire [DATA_WIDTH-1:0]       m_resp_data_o;
    wire [ID_WIDTH-1:0]         m_resp_id_o;
    wire                        m_resp_error_o;
    reg                         m_resp_ready_i;
    
    // Slave signals for the DUT
    wire                        s_req_valid_o;
    wire [ADDR_WIDTH-1:0]       s_req_addr_o;
    wire                        s_req_write_o;
    wire [ID_WIDTH-1:0]         s_req_id_o;
    reg                         s_req_ready_i;
    
    wire                        s_data_valid_o;
    wire [DATA_WIDTH-1:0]       s_data_o;
    wire [DATA_WIDTH/8-1:0]     s_data_strb_o;
    reg                         s_data_ready_i;
    
    reg                         s_resp_valid_i;
    reg [DATA_WIDTH-1:0]        s_resp_data_i;
    reg [ID_WIDTH-1:0]          s_resp_id_i;
    reg                         s_resp_error_i;
    wire                        s_resp_ready_o;
    
    // Transaction counter for verification
    integer read_transactions = 0;
    integer write_transactions = 0;
    
    // Tasks for sending requests
    task send_read_request;
        input [ADDR_WIDTH-1:0] addr;
        input [ID_WIDTH-1:0] id;
        begin
            // Wait for the bus to be ready
            wait(m_req_ready_o);
            @(posedge clk);
            
            // Send read request
            m_req_valid_i = 1'b1;
            m_req_addr_i = addr;
            m_req_write_i = 1'b0;
            m_req_id_i = id;
            
            @(posedge clk);
            m_req_valid_i = 1'b0;
            
            read_transactions = read_transactions+1;
        end
    endtask
    
    task send_write_request;
        input [ADDR_WIDTH-1:0] addr;
        input [DATA_WIDTH-1:0] data;
        input [DATA_WIDTH/8-1:0] strb;
        input [ID_WIDTH-1:0] id;
        begin
            // Wait for the bus to be ready
            wait(m_req_ready_o);
            @(posedge clk);
            
            // Send write request
            m_req_valid_i = 1'b1;
            m_req_addr_i = addr;
            m_req_write_i = 1'b1;
            m_req_id_i = id;
            
            @(posedge clk);
            m_req_valid_i = 1'b0;
            
            // Wait for data path to be ready
            wait(m_data_ready_o);
            @(posedge clk);
            
            // Send write data
            m_data_valid_i = 1'b1;
            m_data_i = data;
            m_data_strb_i = strb;
            
            @(posedge clk);
            m_data_valid_i = 1'b0;
            
            write_transactions=write_transactions+1;
        end
    endtask
    
    // Slave response task
    task send_slave_response;
        input [DATA_WIDTH-1:0] data;
        input [ID_WIDTH-1:0] id;
        input error;
        begin
            // Wait for a few clock cycles to simulate processing
            repeat(3) @(posedge clk);
            
            // Send response
            s_resp_valid_i = 1'b1;
            s_resp_data_i = data;
            s_resp_id_i = id;
            s_resp_error_i = error;
            
            // Wait for master to accept
            wait(s_resp_ready_o);
            @(posedge clk);
            s_resp_valid_i = 1'b0;
        end
    endtask
    
    // DUT instantiation
    bus_protocol #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH),
        .ID_WIDTH(ID_WIDTH)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        
        // Master interface
        .m_req_valid_i(m_req_valid_i),
        .m_req_addr_i(m_req_addr_i),
        .m_req_write_i(m_req_write_i),
        .m_req_id_i(m_req_id_i),
        .m_req_ready_o(m_req_ready_o),
        
        .m_data_valid_i(m_data_valid_i),
        .m_data_i(m_data_i),
        .m_data_strb_i(m_data_strb_i),
        .m_data_ready_o(m_data_ready_o),
        
        .m_resp_valid_o(m_resp_valid_o),
        .m_resp_data_o(m_resp_data_o),
        .m_resp_id_o(m_resp_id_o),
        .m_resp_error_o(m_resp_error_o),
        .m_resp_ready_i(m_resp_ready_i),
        
        // Slave interface
        .s_req_valid_o(s_req_valid_o),
        .s_req_addr_o(s_req_addr_o),
        .s_req_write_o(s_req_write_o),
        .s_req_id_o(s_req_id_o),
        .s_req_ready_i(s_req_ready_i),
        
        .s_data_valid_o(s_data_valid_o),
        .s_data_o(s_data_o),
        .s_data_strb_o(s_data_strb_o),
        .s_data_ready_i(s_data_ready_i),
        
        .s_resp_valid_i(s_resp_valid_i),
        .s_resp_data_i(s_resp_data_i),
        .s_resp_id_i(s_resp_id_i),
        .s_resp_error_i(s_resp_error_i),
        .s_resp_ready_o(s_resp_ready_o)
    );
    
    // Clock generation
    always #5 clk = ~clk;
    
    // Slave side response process
    // This emulates a slave device responding to requests
    /*always @(posedge clk) 
    begin
        if (s_req_valid_o && s_req_ready_i) 
        begin
            automatic logic [ID_WIDTH-1:0] req_id = s_req_id_o;
            automatic logic [ADDR_WIDTH-1:0] req_addr = s_req_addr_o;
            automatic logic req_write = s_req_write_o;    
            fork
                begin
                    if (req_write) 
                    begin
                        // For write requests, wait for data phase
                        wait(s_data_valid_o && s_data_ready_i);
                        // Then send acknowledgment
                        send_slave_response(32'h0, req_id, 1'b0);
                    end
                    else 
                    begin
                        // For read requests, send data back
                        // Use address as data just for testing
                        send_slave_response(req_addr, req_id, 1'b0);
                    end
                end
             join_none
        end
    end*/
    // Declare reg variables at the module level (outside this always block)
reg [ID_WIDTH-1:0] req_id;
reg [ADDR_WIDTH-1:0] req_addr;
reg req_write;
reg wait_for_write;

always @(posedge clk) 
begin
    if (s_req_valid_o && s_req_ready_i) 
    begin
        // Store values in regular registers
        req_id = s_req_id_o;
        req_addr = s_req_addr_o;
        req_write = s_req_write_o;
        
        // In pure Verilog, we can't use fork-join_none
        // Need to handle this differently, perhaps with separate always blocks
        // or additional state machines
        if (req_write) 
        begin
            // For write requests, we'll need a separate process or state machine
            // to handle the wait and response
            wait_for_write = 1'b1;  // Set a flag for another process
        end
        else 
        begin
            // For read requests, send data back immediately
            send_slave_response(req_addr, req_id, 1'b0);
        end
    end
end

// Add a separate always block to handle write responses
always @(posedge clk)
begin
    if (wait_for_write && s_data_valid_o && s_data_ready_i)
    begin
        // Then send acknowledgment
        send_slave_response(32'h0, req_id, 1'b0);
        wait_for_write = 1'b0;  // Clear the flag
    end
end
    
    // Master side response process
    always @(posedge clk) begin
        if (m_resp_valid_o && m_resp_ready_i) begin
            $display("Time: %0t, Received response: ID=%h, Data=%h, Error=%b", 
                      $time, m_resp_id_o, m_resp_data_o, m_resp_error_o);
        end
    end

    // Test sequence
    initial begin
        // Initialize all inputs
        m_req_valid_i = 0;
        m_req_addr_i = 0;
        m_req_write_i = 0;
        m_req_id_i = 0;
        m_data_valid_i = 0;
        m_data_i = 0;
        m_data_strb_i = 0;
        m_resp_ready_i = 1; // Always ready to receive responses
        
        s_req_ready_i = 1;  // Slave always ready for requests
        s_data_ready_i = 1; // Slave always ready for data
        s_resp_valid_i = 0;
        s_resp_data_i = 0;
        s_resp_id_i = 0;
        s_resp_error_i = 0;
        
        // Apply reset
        rst_n = 0;
        #20;
        rst_n = 1;
        #10;
        
        // Test 1: Single read transaction
        $display("\nTest 1: Single read transaction");
        send_read_request(32'h12345678, 4'h1);
        #50;
        
        // Test 2: Single write transaction
        $display("\nTest 2: Single write transaction");
        send_write_request(32'hABCD1234, 32'h87654321, 4'hF, 4'h2);
        #50;
        
        // Test 3: Multiple back-to-back transactions
        $display("\nTest 3: Back-to-back transactions");
        fork
            begin
                send_read_request(32'h00001111, 4'h3);
                send_write_request(32'h00002222, 32'hDEADBEEF, 4'hF, 4'h4);
                send_read_request(32'h00003333, 4'h5);
            end
        join
        #100;
        
        // Test 4: Slave backpressure test (slow slave)
        $display("\nTest 4: Slave backpressure test");
        s_req_ready_i = 0;  // Slave not ready initially
        fork
            begin
                send_read_request(32'h44444444, 4'h6);
            end
            begin
                #30;
                s_req_ready_i = 1;  // Slave becomes ready after delay
            end
        join
        #50;
        
        // Test 5: Master backpressure test (slow master)
        $display("\nTest 5: Master backpressure test");
        m_resp_ready_i = 0;  // Master not ready for responses
        fork
            begin
                send_read_request(32'h55555555, 4'h7);
            end
            begin
                #50;
                m_resp_ready_i = 1;  // Master becomes ready after delay
            end
        join
        #70;
        
        // End simulation
        #50;
        $display("\nSimulation completed - Read transactions: %0d, Write transactions: %0d", 
                  read_transactions, write_transactions);
        $finish;
    end
endmodule