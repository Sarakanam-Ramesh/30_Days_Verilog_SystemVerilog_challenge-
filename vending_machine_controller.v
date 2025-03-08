`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 03.03.2025 19:05:26
// Design Name: 
// Module Name: vending_machine_controller
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


module vending_machine_controller (
    input wire clk,
    input wire rst_n,
    input wire nickel,    // 5 cents
    input wire dime,      // 10 cents
    input wire quarter,   // 25 cents
    output reg dispense,  // Dispense product
    output reg [6:0] change_out,  // Change to return
    output reg [6:0] current_value // Current value inserted
);

    // Product price is 35 cents
    parameter PRODUCT_PRICE = 7'd35;
    
    // State encoding
    parameter IDLE = 2'b00;         // Waiting for money
    parameter COLLECT = 2'b01;      // Collecting money
    parameter DISPENSE = 2'b10;     // Dispensing product
    parameter RETURN_CHANGE = 2'b11; // Returning change
    
    // State registers
    reg [1:0] current_state, next_state;
    reg [6:0] money_inserted;
    reg [6:0] next_money;
    
    // State register update
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_state <= IDLE;
            money_inserted <= 0;
            current_value <= 0;
        end else begin
            current_state <= next_state;
            money_inserted <= next_money;
            current_value <= money_inserted;
        end
    end
    
    // Next state and output logic
    always @(*) begin
        // Default values
        next_state = current_state;
        next_money = money_inserted;
        dispense = 0;
        change_out = 0;
        
        case (current_state)
            IDLE: begin
                next_money = 0;
                if (nickel | dime | quarter)
                    next_state = COLLECT;
            end
            
            COLLECT: begin
                // Update money based on coin inputs
                if (nickel)
                    next_money = money_inserted + 5;
                else if (dime)
                    next_money = money_inserted + 10;
                else if (quarter)
                    next_money = money_inserted + 25;
                    
                // Check if enough money is inserted
                if (next_money >= PRODUCT_PRICE)
                    next_state = DISPENSE;
            end
            
            DISPENSE: begin
                dispense = 1;
                next_state = RETURN_CHANGE;
            end
            
            RETURN_CHANGE: begin
                change_out = money_inserted - PRODUCT_PRICE;
                next_money = 0;
                next_state = IDLE;
            end
            
            default: next_state = IDLE;
        endcase
    end

endmodule
