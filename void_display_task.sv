`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 28.02.2025 22:20:35
// Design Name: 
// Module Name: void_display_task
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


module void_display_task (
    input logic clk,
    input logic rst_n,
    input logic [31:0] data_in,
    input logic [1:0] format_sel,
    input logic display_en,
    output logic display_busy
);
    // Internal signals
    logic [31:0] data_reg;
    logic [1:0] format_reg;
    
    // Void function to format data for display (no return value)
    // Modified to avoid using string type
    function void format_data(input logic [31:0] data, input logic [1:0] format);
        case (format)
            2'b00: begin // Hexadecimal format
                $display("HEX: 0x%h", data);
            end
            2'b01: begin // Decimal format
                $display("DEC: %d", data);
            end
            2'b10: begin // Binary format
                $display("BIN: %b", data);
            end
            2'b11: begin // ASCII format (assuming 4 ASCII characters)
                $display("ASCII: %c%c%c%c", 
                          data[31:24], data[23:16], data[15:8], data[7:0]);
            end
        endcase
    endfunction
    
    // Register data when enabled
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            data_reg <= 32'h0;
            format_reg <= 2'b00;
            display_busy <= 1'b0;
        end else if (display_en && !display_busy) begin
            data_reg <= data_in;
            format_reg <= format_sel;
            display_busy <= 1'b1;
            
            // Call the void function to display formatted data
            format_data(data_in, format_sel);
            
            // In real hardware, this would trigger a display controller
            // For simulation, we just deassert busy after 3 cycles
        end else if (display_busy) begin
            // Using integer counter instead of static int
            // This is more compatible with older tools
            reg [2:0] delay_count;
            delay_count = 0;
            
            // Count 3 cycles before clearing busy flag
            delay_count = delay_count + 1;
            
            if (delay_count >= 3) begin
                display_busy <= 1'b0;
            end
        end
    end
endmodule
