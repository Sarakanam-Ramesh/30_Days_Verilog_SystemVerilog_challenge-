`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 28.02.2025 09:01:32
// Design Name: 
// Module Name: associative_array_cache
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


module associative_array_cache #(
    parameter ADDR_WIDTH = 16,             // Address width
    parameter DATA_WIDTH = 32,             // Data width
    parameter NUM_WAYS = 4,                // Number of ways (associativity)
    parameter NUM_SETS = 64,               // Number of sets
    parameter INDEX_WIDTH = $clog2(NUM_SETS),
    parameter TAG_WIDTH = ADDR_WIDTH - INDEX_WIDTH,
    parameter WAY_WIDTH = $clog2(NUM_WAYS)
)(
    input  logic                      clk,
    input  logic                      rst_n,
    
    // CPU Interface
    input  logic                      i_valid,
    input  logic                      i_rw,   // 0: read, 1: write
    input  logic [ADDR_WIDTH-1:0]     i_addr,
    input  logic [DATA_WIDTH-1:0]     i_wdata,
    output logic                      o_ready,
    output logic [DATA_WIDTH-1:0]     o_rdata,
    output logic                      o_hit
);

    // Cache structure definitions
    typedef struct packed {
        logic                   valid;
        logic                   dirty;
        logic [TAG_WIDTH-1:0]   tag;
    } cache_tag_t;
    
    // Cache storage
    cache_tag_t cache_tags[NUM_SETS][NUM_WAYS];
    logic [DATA_WIDTH-1:0] cache_data[NUM_SETS][NUM_WAYS];
    
    // LRU tracking (simple counter-based implementation)
    logic [WAY_WIDTH-1:0] lru_counters[NUM_SETS];
    
    // Address breakdown
    logic [TAG_WIDTH-1:0]    addr_tag;
    logic [INDEX_WIDTH-1:0]  addr_index;
    
    assign addr_tag = i_addr[ADDR_WIDTH-1:INDEX_WIDTH];
    assign addr_index = i_addr[INDEX_WIDTH-1:0];
    
    // Hit detection logic
    logic [NUM_WAYS-1:0] way_hit;
    logic any_hit;
    logic [WAY_WIDTH-1:0] hit_way;
    
    always_comb begin
        way_hit = '0;
        for (int i = 0; i < NUM_WAYS; i++) begin
            way_hit[i] = cache_tags[addr_index][i].valid && 
                         (cache_tags[addr_index][i].tag == addr_tag);
        end
        
        any_hit = |way_hit;
        hit_way = '0;  // Default
        
        // Binary encoder to get the hit way
        for (int i = 0; i < NUM_WAYS; i++) begin
            if (way_hit[i]) hit_way = i[WAY_WIDTH-1:0];
        end
    end
    
    // Output assignments
    assign o_hit = any_hit;
    assign o_rdata = any_hit ? cache_data[addr_index][hit_way] : '0;
    assign o_ready = 1'b1;  // Simplified for this example
    
    // Cache operations
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Reset all cache tags and LRU counters
            for (int i = 0; i < NUM_SETS; i++) begin
                for (int j = 0; j < NUM_WAYS; j++) begin
                    cache_tags[i][j].valid <= 1'b0;
                    cache_tags[i][j].dirty <= 1'b0;
                    cache_tags[i][j].tag <= '0;
                end
                lru_counters[i] <= '0;
            end
        end
        else if (i_valid) begin
            if (i_rw && any_hit) begin
                // Write hit
                cache_data[addr_index][hit_way] <= i_wdata;
                cache_tags[addr_index][hit_way].dirty <= 1'b1;
                lru_counters[addr_index] <= lru_counters[addr_index] + 1'b1;
            end
            else if (!i_rw && !any_hit) begin
                // Read miss - replace LRU way
                // In real implementation, you would issue memory read here
                cache_tags[addr_index][lru_counters[addr_index]].valid <= 1'b1;
                cache_tags[addr_index][lru_counters[addr_index]].dirty <= 1'b0;
                cache_tags[addr_index][lru_counters[addr_index]].tag <= addr_tag;
                // Simulation only: set some data
                cache_data[addr_index][lru_counters[addr_index]] <= {DATA_WIDTH{1'b1}};
                lru_counters[addr_index] <= lru_counters[addr_index] + 1'b1;
            end
            else if (i_rw && !any_hit) begin
                // Write miss - replace LRU way
                cache_tags[addr_index][lru_counters[addr_index]].valid <= 1'b1;
                cache_tags[addr_index][lru_counters[addr_index]].dirty <= 1'b1;
                cache_tags[addr_index][lru_counters[addr_index]].tag <= addr_tag;
                cache_data[addr_index][lru_counters[addr_index]] <= i_wdata;
                lru_counters[addr_index] <= lru_counters[addr_index] + 1'b1;
            end
            // Read hit requires no action other than returning data
        end
    end

endmodule
