`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 22.02.2025 21:26:25
// Design Name: 
// Module Name: counter_structural
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


// T Flip-flop
module t_ff (
    input wire clk, rst,
    input wire t,
    output reg q
);
    always @(posedge clk or posedge rst) begin
        if (rst)
            q <= 1'b0;
        else if (t)
            q <= ~q;
    end
endmodule

// 8 bit counter
module counter_structural(
    input wire clk,
    input wire clear,   //reset
    output wire [7:0] q);   //8bit count
    
    wire [7:0] enable;  // input for T-flipflop
    wire [7:0] carry;   //output for each T-flipflop
    
    assign enable[0] = 1'b1;    // first T-flipflop input
    genvar i;
    
    // generates input for every T-flipflop
    for(i=1;i<8;i=i+1)begin
        assign enable[i] = &q[i-1:0];
    end
    
    // T-flipflops for 8-bit counter
    for(i=0;i<8;i=i+1) begin
        t_ff tff_inst(.clk(clk),
                        .rst(clear),
                        .t(enable[i]),
                        .q(q[i]));
    end
endmodule
