`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 03.03.2025 19:05:56
// Design Name: 
// Module Name: vending_machine_controller_tb
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


module vending_machine_tb;
    // Signals
    reg clk;
    reg rst_n;
    reg nickel, dime, quarter;
    wire dispense;
    wire [6:0] change_out, current_value;
    
    // Instantiate the DUT
    vending_machine_controller dut (
        .clk(clk),
        .rst_n(rst_n),
        .nickel(nickel),
        .dime(dime),
        .quarter(quarter),
        .dispense(dispense),
        .change_out(change_out),
        .current_value(current_value)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 10ns period
    end
    
    // Test sequence
    initial begin
        $display("Time\tReset\tNickel\tDime\tQuarter\tValue\tDispense\tChange");
        $monitor("%0t\t%b\t%b\t%b\t%b\t%d\t%b\t%d", 
                $time, rst_n, nickel, dime, quarter, 
                current_value, dispense, change_out);
        
        // Initialize inputs
        rst_n = 0;
        nickel = 0;
        dime = 0;
        quarter = 0;
        
        // Reset sequence
        #10 rst_n = 1;
        
        // Test case 1: Exact amount (35 cents)
        #10 dime = 1;
        #10 dime = 0;
        #10 quarter = 1;
        #10 quarter = 0;
        #30; // Let the machine process
        
        // Test case 2: More than required (50 cents)
        #10 quarter = 1;
        #10 quarter = 0;
        #10 quarter = 1;
        #10 quarter = 0;
        #30; // Let the machine process
        
        // Test case 3: Incremental deposits
        #10 nickel = 1;
        #10 nickel = 0;
        #10 dime = 1;
        #10 dime = 0;
        #10 dime = 1;
        #10 dime = 0;
        #10 nickel = 1;
        #10 nickel = 0;
        #10 nickel = 1;
        #10 nickel = 0;
        #30; // Let the machine process
        
        $display("Simulation complete");
        $finish;
    end
endmodule
