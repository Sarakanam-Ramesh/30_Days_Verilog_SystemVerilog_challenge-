`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 26.02.2025 21:38:07
// Design Name: 
// Module Name: mux_4to1_sv_tb
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


module mux_4to1_sv_tb;
    // Testbench signals
    logic [1:0] sel;
    logic [3:0] data_in;
    logic out;
    
    // Instantiate the DUT
    mux_4to1_sv DUT (
        .sel(sel),
        .data_in(data_in),
        .out(out)
    );
    
    // Test stimulus
    initial begin
        // Initialize display formatting
        $display("Time\tsel\tdata_in\tout");
        $monitor("%0d\t%b\t%b\t%b", $time, sel, data_in, out);
        
        // Test multiple data patterns
        data_in = 4'b1010;
        sel = 2'b00; #10;
        sel = 2'b01; #10;
        sel = 2'b10; #10;
        sel = 2'b11; #10;
        
        data_in = 4'b0101;
        sel = 2'b00; #10;
        sel = 2'b01; #10;
        sel = 2'b10; #10;
        sel = 2'b11; #10;
        
        $display("Test completed");
        $finish;
    end
endmodule
