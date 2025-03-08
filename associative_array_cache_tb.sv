`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 28.02.2025 09:02:12
// Design Name: 
// Module Name: associative_array_cache_tb
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

module associative_array_cache_tb;
    // Parameters
    localparam ADDR_WIDTH = 16;
    localparam DATA_WIDTH = 32;
    localparam NUM_WAYS = 4;
    localparam NUM_SETS = 64;
    localparam INDEX_WIDTH = $clog2(NUM_SETS);
    localparam TAG_WIDTH = ADDR_WIDTH - INDEX_WIDTH;
    
    // Clock and reset
    logic clk;
    logic rst_n;
    
    // DUT interface signals
    logic                    i_valid;
    logic                    i_rw;
    logic [ADDR_WIDTH-1:0]   i_addr;
    logic [DATA_WIDTH-1:0]   i_wdata;
    logic                    o_ready;
    logic [DATA_WIDTH-1:0]   o_rdata;
    logic                    o_hit;
    
    // Test data storage - use associative array instead of large arrays
    logic [DATA_WIDTH-1:0] test_memory[string];
    
    // DUT instantiation
    associative_array_cache #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH),
        .NUM_WAYS(NUM_WAYS),
        .NUM_SETS(NUM_SETS)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .i_valid(i_valid),
        .i_rw(i_rw),
        .i_addr(i_addr),
        .i_wdata(i_wdata),
        .o_ready(o_ready),
        .o_rdata(o_rdata),
        .o_hit(o_hit)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // Create address key for associative array
    function string create_addr_key(input logic [ADDR_WIDTH-1:0] addr);
        return $sformatf("%0h", addr);
    endfunction
    
    // Test sequence
    initial begin
        string addr_key;
        
        // Initialize signals
        rst_n = 0;
        i_valid = 0;
        i_rw = 0;
        i_addr = 0;
        i_wdata = 0;
        
        // Reset
        repeat(5) @(posedge clk);
        rst_n = 1;
        repeat(2) @(posedge clk);
        
        // Test 1: Write to cache
        $display("Test 1: Write data to cache");
        
        // Use associative array for test patterns instead of large loops
        logic [ADDR_WIDTH-1:0] test_addresses[1000];
        logic [DATA_WIDTH-1:0] test_data[1000];
        int num_tests = 100; // Well below 2000 limit
        
        // Generate test patterns
        for (int i = 0; i < num_tests; i++) begin
            test_addresses[i] = $urandom_range(0, (2**ADDR_WIDTH)-1);
            test_data[i] = $urandom();
        end
        
        // Write to cache
        for (int i = 0; i < num_tests; i++) begin
            @(posedge clk);
            i_valid = 1;
            i_rw = 1; // Write
            i_addr = test_addresses[i];
            i_wdata = test_data[i];
            
            // Store in test memory (associative array)
            addr_key = create_addr_key(test_addresses[i]);
            test_memory[addr_key] = test_data[i];
            
            @(posedge clk);
            i_valid = 0;
            
            // Small delay between operations
            repeat(2) @(posedge clk);
        end
        
        // Test 2: Read from cache and verify hits/data
        $display("Test 2: Read data from cache and verify hits");
        
        // Read back from addresses written to
        for (int i = 0; i < num_tests; i++) begin
            @(posedge clk);
            i_valid = 1;
            i_rw = 0; // Read
            i_addr = test_addresses[i];
            
            @(posedge clk);
            i_valid = 0;
            
            // Check hit
            if (!o_hit) begin
                $display("Error: Expected hit for address %0h but got miss", test_addresses[i]);
            end
            
            // Verify data on hit
            addr_key = create_addr_key(test_addresses[i]);
            if (o_hit && (o_rdata !== test_memory[addr_key])) begin
                $display("Error: Data mismatch for address %0h. Expected: %0h, Got: %0h", 
                         test_addresses[i], test_memory[addr_key], o_rdata);
            end
            
            // Small delay between operations
            repeat(2) @(posedge clk);
        end
        
        // Test 3: Check conflict misses by accessing addresses that map to same set
        $display("Test 3: Testing conflict misses");
        
        // Generate addresses that map to the same set but have different tags
        logic [ADDR_WIDTH-1:0] conflict_addrs[NUM_WAYS+2];
        logic [DATA_WIDTH-1:0] conflict_data[NUM_WAYS+2];
        logic [INDEX_WIDTH-1:0] target_index = $urandom_range(0, NUM_SETS-1);
        
        for (int i = 0; i < NUM_WAYS+2; i++) begin
            // Same index, different tags
            conflict_addrs[i] = {$urandom_range(1, (2**TAG_WIDTH)-1), target_index};
            conflict_data[i] = $urandom();
            
            // Write to cache
            @(posedge clk);
            i_valid = 1;
            i_rw = 1; // Write
            i_addr = conflict_addrs[i];
            i_wdata = conflict_data[i];
            
            // Store in test memory
            addr_key = create_addr_key(conflict_addrs[i]);
            test_memory[addr_key] = conflict_data[i];
            
            @(posedge clk);
            i_valid = 0;
            
            repeat(2) @(posedge clk);
        end
        
        // Read back first and second addresses (should be misses due to capacity)
        for (int i = 0; i < 2; i++) begin
            @(posedge clk);
            i_valid = 1;
            i_rw = 0; // Read
            i_addr = conflict_addrs[i];
            
            @(posedge clk);
            i_valid = 0;
            
            // Expect misses for first two addresses (should have been evicted)
            if (o_hit) begin
                $display("Error: Expected miss for address %0h but got hit", conflict_addrs[i]);
            end else begin
                $display("Correct: Got expected miss for address %0h", conflict_addrs[i]);
            end
            
            repeat(2) @(posedge clk);
        end
        
        // Read remaining addresses (should be hits)
        for (int i = 2; i < NUM_WAYS+2; i++) begin
            @(posedge clk);
            i_valid = 1;
            i_rw = 0; // Read
            i_addr = conflict_addrs[i];
            
            @(posedge clk);
            i_valid = 0;
            
            // Expect hits for last addresses
            if (!o_hit) begin
                $display("Error: Expected hit for address %0h but got miss", conflict_addrs[i]);
            end else begin
                $display("Correct: Got expected hit for address %0h", conflict_addrs[i]);
            end
            
            repeat(2) @(posedge clk);
        end
        
        // Test 4: Random access pattern
        $display("Test 4: Random access pattern");
        
        logic [ADDR_WIDTH-1:0] rand_addr;
        logic [DATA_WIDTH-1:0] rand_data;
        logic rand_rw;
        
        // Limited to 500 iterations (below 2000 limit)
        for (int i = 0; i < 100; i++) begin
            rand_addr = $urandom_range(0, (2**ADDR_WIDTH)-1);
            rand_data = $urandom();
            rand_rw = $urandom_range(0, 1);  // 0: read, 1: write
            addr_key = create_addr_key(rand_addr);
            
            @(posedge clk);
            i_valid = 1;
            i_rw = rand_rw;
            i_addr = rand_addr;
            
            if (rand_rw) begin  // Write
                i_wdata = rand_data;
                test_memory[addr_key] = rand_data;  // Update test memory
            end
            
            @(posedge clk);
            i_valid = 0;
            
            // For reads, verify if we have the data in test memory
            if (!rand_rw && o_hit && test_memory.exists(addr_key)) begin
                if (o_rdata !== test_memory[addr_key]) begin
                    $display("Error: Data mismatch for address %0h. Expected: %0h, Got: %0h", 
                             rand_addr, test_memory[addr_key], o_rdata);
                end
            end
            
            repeat(1) @(posedge clk);
        end
        
        // Complete the simulation
        $display("Simulation completed");
        repeat(10) @(posedge clk);
        $finish;
    end
    
    // Monitor
    initial begin
        $monitor("Time: %0t, Valid: %0b, RW: %0b, Addr: %0h, WData: %0h, Hit: %0b, RData: %0h",
                 $time, i_valid, i_rw, i_addr, i_wdata, o_hit, o_rdata);
    end

endmodule