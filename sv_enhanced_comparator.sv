`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 24.02.2025 20:39:49
// Design Name: 
// Module Name: sv_enhanced_comparator
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


module sv_enhanced_comparator (
    input [3:0] data,
    output logic in_range1,    // Check if data is in range [3:7]
    output logic in_range2,    // Check if data is 2, 5, or 9
    output logic in_range3     // Check if data is in range [10:15]
);
    // Using the inside operator to check if value is within a range
    always_comb begin
        // Check if data is in range [3:7]
        in_range1 = data inside {[3:7]};
        
        // Check if data is 2, 5, or 9
        in_range2 = data inside {2, 5, 9};
        
        // Check if data is in range [10:15]
        in_range3 = data inside {[10:15]};
    end

endmodule
