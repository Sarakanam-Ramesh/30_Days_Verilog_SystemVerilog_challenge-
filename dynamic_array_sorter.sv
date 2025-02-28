`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 28.02.2025 08:30:24
// Design Name: 
// Module Name: dynamic_array_sorter
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


module dynamic_array_sorter #(
    parameter DATA_WIDTH = 32,
    parameter MAX_ARRAY_SIZE = 16  // Maximum number of elements the sorter can handle
)(
    input  logic clk,
    input  logic reset,
    input  logic add_element,
    input  logic sort_array,
    input  logic clear_array,
    input  logic [DATA_WIDTH-1:0] data_in,
    output logic [DATA_WIDTH-1:0] sorted_data_out,
    output logic valid_out,
    output logic [$clog2(MAX_ARRAY_SIZE+1)-1:0] array_size
);

    // Array to store data (fixed size for synthesis)
    logic [DATA_WIDTH-1:0] data_array [0:MAX_ARRAY_SIZE-1];
    
    // State machine for sorting operation
    typedef enum logic [1:0] {
        IDLE = 2'b00,
        SORTING = 2'b01,
        OUTPUT_DATA = 2'b10
    } state_t;
    
    state_t current_state;
    
    // Output index counter
    logic [$clog2(MAX_ARRAY_SIZE)-1:0] output_idx;
    logic [$clog2(MAX_ARRAY_SIZE)-1:0] sort_i, sort_j;
    logic sorting_active;
    
    // Main state machine
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            current_state <= IDLE;
            array_size <= '0;
            output_idx <= '0;
            valid_out <= 1'b0;
            sorted_data_out <= '0;
            sorting_active <= 1'b0;
            sort_i <= '0;
            sort_j <= '0;
            
            // Clear array
            for (int i = 0; i < MAX_ARRAY_SIZE; i++) begin
                data_array[i] <= '0;
            end
        end
        else begin
            case (current_state)
                IDLE: begin
                    valid_out <= 1'b0;
                    
                    // Add element if there's room
                    if (add_element && array_size < MAX_ARRAY_SIZE) begin
                        data_array[array_size] <= data_in;
                        array_size <= array_size + 1'b1;
                    end
                    
                    // Clear array
                    if (clear_array) begin
                        array_size <= '0;
                    end
                    
                    // Start sorting
                    if (sort_array && array_size > 1) begin
                        current_state <= SORTING;
                        sorting_active <= 1'b1;
                        sort_i <= '0;
                        sort_j <= '0;
                    end
                end
                
                SORTING: begin
                    // Bubble sort implementation with state tracking
                    if (sorting_active) begin
                        if (sort_j < array_size - 1 - sort_i) begin
                            // Compare adjacent elements
                            if (data_array[sort_j] > data_array[sort_j + 1]) begin
                                // Swap elements
                                logic [DATA_WIDTH-1:0] temp;
                                temp = data_array[sort_j];
                                data_array[sort_j] = data_array[sort_j + 1];
                                data_array[sort_j + 1] = temp;
                            end
                            sort_j <= sort_j + 1'b1;
                        end else begin
                            sort_j <= '0;
                            sort_i <= sort_i + 1'b1;
                            
                            // Check if sorting is complete
                            if (sort_i >= array_size - 1) begin
                                sorting_active <= 1'b0;
                                current_state <= OUTPUT_DATA;
                                output_idx <= '0;
                            end
                        end
                    end
                end
                
                OUTPUT_DATA: begin
                    if (output_idx < array_size) begin
                        sorted_data_out <= data_array[output_idx];
                        valid_out <= 1'b1;
                        output_idx <= output_idx + 1'b1;
                    end else begin
                        valid_out <= 1'b0;
                        current_state <= IDLE;
                    end
                end
                
                default: current_state <= IDLE;
            endcase
        end
    end

endmodule
