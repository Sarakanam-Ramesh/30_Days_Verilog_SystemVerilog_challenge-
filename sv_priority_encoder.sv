`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 24.02.2025 20:52:30
// Design Name: 
// Module Name: sv_priority_encoder
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


module sv_priority_encoder (
    input [7:0] request,
    output logic [2:0] grant,
    output logic valid
);
    // Using unique case to implement priority encoding
    always_comb begin
        // Default values
        valid = 1'b0;
        grant = 3'b000;
        
        // Priority encoding with unique case
        unique case (1'b1)
            request[7]: begin grant = 3'd7; valid = 1'b1; end
            request[6]: begin grant = 3'd6; valid = 1'b1; end
            request[5]: begin grant = 3'd5; valid = 1'b1; end
            request[4]: begin grant = 3'd4; valid = 1'b1; end
            request[3]: begin grant = 3'd3; valid = 1'b1; end
            request[2]: begin grant = 3'd2; valid = 1'b1; end
            request[1]: begin grant = 3'd1; valid = 1'b1; end
            request[0]: begin grant = 3'd0; valid = 1'b1; end
            default:    begin grant = 3'd0; valid = 1'b0; end
        endcase
    end

endmodule
