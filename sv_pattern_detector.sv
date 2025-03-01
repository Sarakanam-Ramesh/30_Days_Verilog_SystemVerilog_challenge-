`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 24.02.2025 20:47:30
// Design Name: 
// Module Name: sv_pattern_detector
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


module sv_pattern_detector (
    input [7:0] data,
    output logic has_pattern1,  // Detect pattern 10xx01xx
    output logic has_pattern2,  // Detect pattern 11??00??
    output logic has_pattern3   // Detect pattern x1x0x1x0
);
    // Using wildcard equality operators
    always_comb begin
        // Wildcard equality (==?) operator with don't care (?)
        // Pattern 10xx01xx (x can be 0 or 1)
        has_pattern1 = (data ==? 8'b10??01??);
        
        // Wildcard equality (==?) with ? representing don't care
        // Pattern 11??00?? (? can be 0 or 1)
        has_pattern2 = (data ==? 8'b11??00??);
        
        // Pattern x1x0x1x0 (x can be 0 or 1)
        has_pattern3 = (data ==? 8'b?1?0?1?0);
    end

endmodule
