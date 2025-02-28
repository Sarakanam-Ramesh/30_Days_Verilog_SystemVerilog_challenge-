`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 28.02.2025 08:30:51
// Design Name: 
// Module Name: dynamic_array_sorter_tb
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


module dynamic_array_sorter_tb;
    // Parameters
    localparam DATA_WIDTH = 32;
    localparam MAX_ARRAY_SIZE = 16;
    
    // Testbench signals
    logic clk;
    logic reset;
    logic add_element;
    logic sort_array;
    logic clear_array;
    logic [DATA_WIDTH-1:0] data_in;
    logic [DATA_WIDTH-1:0] sorted_data_out;
    logic valid_out;
    logic [$clog2(MAX_ARRAY_SIZE+1)-1:0] array_size;
    
    // Instantiate the dynamic array sorter module
    dynamic_array_sorter #(
        .DATA_WIDTH(DATA_WIDTH),
        .MAX_ARRAY_SIZE(MAX_ARRAY_SIZE)
    ) dut (
        .clk(clk),
        .reset(reset),
        .add_element(add_element),
        .sort_array(sort_array),
        .clear_array(clear_array),
        .data_in(data_in),
        .sorted_data_out(sorted_data_out),
        .valid_out(valid_out),
        .array_size(array_size)
    );
    
    // Test sequence counter
    integer test_step = 0;
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 10ns period clock
    end
    
    // Controlled test sequence with finite loops
    always @(posedge clk) begin
        case (test_step)
            // Initialize
            0: begin
                reset <= 1;
                add_element <= 0;
                sort_array <= 0;
                clear_array <= 0;
                data_in <= 0;
                test_step <= test_step + 1;
            end
            
            // Release reset
            1: begin
                reset <= 0;
                test_step <= test_step + 1;
            end
            
            // Add first element
            2: begin
                add_element <= 1;
                data_in <= 42;
                test_step <= test_step + 1;
            end
            
            // Add second element
            3: begin
                data_in <= 17;
                test_step <= test_step + 1;
            end
            
            // Add third element
            4: begin
                data_in <= 93;
                test_step <= test_step + 1;
            end
            
            // Add fourth element
            5: begin
                data_in <= 5;
                test_step <= test_step + 1;
            end
            
            // Add fifth element
            6: begin
                data_in <= 61;
                test_step <= test_step + 1;
            end
            
            // Add sixth element
            7: begin
                data_in <= 32;
                test_step <= test_step + 1;
            end
            
            // Stop adding elements
            8: begin
                add_element <= 0;
                test_step <= test_step + 1;
            end
            
            // Start sorting
            9: begin
                sort_array <= 1;
                test_step <= test_step + 1;
            end
            
            // Stop sorting signal
            10: begin
                sort_array <= 0;
                test_step <= test_step + 1;
            end
            
            // Wait for sorting to complete and data to be output
            11: begin
                if (!valid_out && array_size > 0) begin
                    // Still waiting for sorted output
                    test_step <= test_step;
                end else if (valid_out) begin
                    // Data is being output
                    test_step <= test_step;
                end else begin
                    // All data has been output
                    test_step <= test_step + 1;
                end
            end
            
            // Clear the array
            12: begin
                clear_array <= 1;
                test_step <= test_step + 1;
            end
            
            // Stop clear signal
            13: begin
                clear_array <= 0;
                test_step <= test_step + 1;
            end
            
            // Add new elements after clearing
            14: begin
                add_element <= 1;
                data_in <= 100;
                test_step <= test_step + 1;
            end
            
            // Add second element in new set
            15: begin
                data_in <= 50;
                test_step <= test_step + 1;
            end
            
            // Add third element in new set
            16: begin
                data_in <= 75;
                test_step <= test_step + 1;
            end
            
            // Add fourth element in new set
            17: begin
                data_in <= 25;
                test_step <= test_step + 1;
            end
            
            // Stop adding elements
            18: begin
                add_element <= 0;
                test_step <= test_step + 1;
            end
            
            // Sort second set
            19: begin
                sort_array <= 1;
                test_step <= test_step + 1;
            end
            
            // Stop sort signal
            20: begin
                sort_array <= 0;
                test_step <= test_step + 1;
            end
            
            // Wait for second sort to complete
            21: begin
                test_step <= test_step + 1;
            end
            
            // End test
            default: begin
                test_step <= test_step;
            end
        endcase
    end
    
    // Monitor the simulation
    initial begin
        $display("Simulation started");
        
        // Monitor changes
        $monitor("Time: %0t, Step: %0d, Reset: %b, AddElem: %b, Sort: %b, Clear: %b, DataIn: %d, SortedOut: %d, Valid: %b, Size: %d",
                 $time, test_step, reset, add_element, sort_array, clear_array, data_in, sorted_data_out, valid_out, array_size);
        
        // End simulation after a certain time
        #10000;
        $display("Simulation ended");
        $finish;
    end
endmodule