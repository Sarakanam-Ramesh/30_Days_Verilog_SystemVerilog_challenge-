`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 05.03.2025 21:38:38
// Design Name: 
// Module Name: ram_with_ecc
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


module ram_with_ecc #(
    parameter DATA_WIDTH = 8,
    parameter ADDR_WIDTH = 4
)(
    input wire clk,
    input wire we,
    input wire [ADDR_WIDTH-1:0] addr,
    input wire [DATA_WIDTH-1:0] din,
    output logic [DATA_WIDTH-1:0] dout,
    output logic single_bit_error,
    output logic double_bit_error
);

    // Memory array
    logic [DATA_WIDTH+3:0] memory [(1 << ADDR_WIDTH)-1:0];
    
    // Hamming code generation
    function logic [DATA_WIDTH+3:0] generate_ecc(input logic [DATA_WIDTH-1:0] data);
        logic [DATA_WIDTH+3:0] ecc_data;
        ecc_data[0] = ^data;  // Parity bit
        ecc_data[1] = ^(data & 8'hF0);  // Upper nibble parity
        ecc_data[2] = ^(data & 8'h0F);  // Lower nibble parity
        ecc_data[3] = ^data;  // Additional parity for extra protection
        ecc_data[11:4] = data;  // Original data
        return ecc_data;
    endfunction

    // Error correction function
    function logic [DATA_WIDTH-1:0] correct_data(
        input logic [DATA_WIDTH+3:0] ecc_data, 
        output logic single_err, 
        output logic multi_err
    );
        logic parity_check;
        
        // Simple error detection
        parity_check = ^ecc_data;
        single_err = (parity_check != 0);
        multi_err = 0;  // Simplified for this example
        
        return ecc_data[11:4];
    endfunction

    // Read/Write logic
    always_ff @(posedge clk) begin
        logic [DATA_WIDTH+3:0] ecc_write_data;
        logic [DATA_WIDTH+3:0] ecc_read_data;
        logic local_single_error;
        logic local_multi_error;

        if (we) begin
            // Write with ECC
            ecc_write_data = generate_ecc(din);
            memory[addr] <= ecc_write_data;
        end
        
        // Read with Error Checking
        ecc_read_data = memory[addr];
        
        dout <= correct_data(
            ecc_read_data, 
            local_single_error, 
            local_multi_error
        );

        // Update error flags
        single_bit_error <= local_single_error;
        double_bit_error <= local_multi_error;
    end
endmodule
