`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06.03.2025 18:23:39
// Design Name: 
// Module Name: ripple_carry_adder_tb
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


module ripple_carry_adder_tb;
    parameter WIDTH = 8;
    
    reg [WIDTH-1:0] a, b;
    reg cin;
    wire [WIDTH-1:0] sum;
    wire cout;
    
    // Instantiate the DUT
    ripple_carry_adder #(
        .WIDTH(WIDTH)
    ) dut (
        .a(a),
        .b(b),
        .cin(cin),
        .sum(sum),
        .cout(cout)
    );
    
    // Display results
    initial begin
        $monitor("Time=%0t: a=%b, b=%b, cin=%b, sum=%b, cout=%b", 
                 $time, a, b, cin, sum, cout);
    end
    
    // Test vectors
    initial begin
        // Test case 1: Basic addition
        a = 8'h3C; b = 8'h5A; cin = 0;
        #10;
        
        // Test case 2: With carry in
        a = 8'h3C; b = 8'h5A; cin = 1;
        #10;
        
        // Test case 3: Test overflow
        a = 8'hFF; b = 8'h01; cin = 0;
        #10;
        
        // Test case 4: Random values
        a = $random; b = $random; cin = $random % 2;
        #10;
        
        $finish;
    end
endmodule