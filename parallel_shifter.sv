`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06.03.2025 18:51:19
// Design Name: 
// Module Name: parallel_shifter
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


module parallel_shifter #(
    parameter WIDTH = 8,
    parameter MAX_SHIFT = 4  // Maximum shift amount
)(
    input logic clk,
    input logic rst_n,
    input logic [WIDTH-1:0] data_in,
    input logic [$clog2(MAX_SHIFT+1)-1:0] shift_amt,  // +1 to allow for no shift
    input logic shift_left,  // Direction control: 1=left, 0=right
    output logic [WIDTH-1:0] data_out
);
    // Define intermediate signals for assertions
    logic [WIDTH-1:0] shifted_data;
    
    // Perform the shift operation
    always_comb begin
        if (shift_left)
            shifted_data = data_in << shift_amt;
        else
            shifted_data = data_in >> shift_amt;
    end
    
    // Register the output
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            data_out <= '0;
        else
            data_out <= shifted_data;
    end
    
    // Generate assertions for each shift amount
    generate
        for (genvar i = 0; i <= MAX_SHIFT; i++) begin : shift_assertions
            // For left shifts
            property left_shift_by_i;
                @(posedge clk) disable iff (!rst_n)
                    (shift_amt == i && shift_left) |-> (data_out == (data_in << i));
            endproperty
            
            // For right shifts
            property right_shift_by_i;
                @(posedge clk) disable iff (!rst_n)
                    (shift_amt == i && !shift_left) |-> (data_out == (data_in >> i));
            endproperty
            
            // Instantiate the assertions
            assert property (left_shift_by_i)
                else $error("Left shift by %0d failed at time %0t", i, $time);
                
            assert property (right_shift_by_i)
                else $error("Right shift by %0d failed at time %0t", i, $time);
        end
    endgenerate
    
    // Assert that shift amount is within valid range
    assert property (@(posedge clk) disable iff (!rst_n)
                     shift_amt <= MAX_SHIFT)
        else $error("Shift amount exceeds maximum allowed at time %0t", $time);
endmodule
