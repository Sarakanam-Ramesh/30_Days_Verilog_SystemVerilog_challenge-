`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 24.02.2025 20:52:57
// Design Name: 
// Module Name: sv_priority_encoder_tb
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
module sv_priority_encoder_tb;
    // Testbench signals
    logic [7:0] request;
    logic [2:0] grant;
    logic valid;
 
    // Instantiate the DUT
    sv_priority_encoder DUT (.request(request), .grant(grant), .valid(valid));
    // Helper function to check if output is correct
    function automatic void check_output(input [7:0] req, input [2:0] exp_grant, input exp_valid);
        if (grant !== exp_grant || valid !== exp_valid) begin
            $display("ERROR: For request = %b, expected grant = %d, valid = %b, but got grant = %d, valid = %b",
                    req, exp_grant, exp_valid, grant, valid);
        end
    endfunction
    // Test stimulus
    initial begin
        $display("Priority Encoder Test Using Unique Case");
        $display("Request\t\tGrant\tValid");
        $display("--------\t-----\t-----");
        // No requests
        request = 8'b00000000; #10;
        $display("%b\t%d\t%b", request, grant, valid);
        check_output(request, 3'd0, 1'b0);
        // Single request
        request = 8'b00000001; #10;
        $display("%b\t%d\t%b", request, grant, valid);
        check_output(request, 3'd0, 1'b1);
        request = 8'b00000010; #10;
        $display("%b\t%d\t%b", request, grant, valid);
        check_output(request, 3'd1, 1'b1);
        // Multiple requests, priority to highest bit
        request = 8'b00001010; #10;
        $display("%b\t%d\t%b", request, grant, valid);
        check_output(request, 3'd3, 1'b1);
        request = 8'b10101010; #10;
        $display("%b\t%d\t%b", request, grant, valid);
        check_output(request, 3'd7, 1'b1);
        request = 8'b11111111; #10;
        $display("%b\t%d\t%b", request, grant, valid);
        check_output(request, 3'd7, 1'b1);
        #10 $finish;
    end
endmodule
