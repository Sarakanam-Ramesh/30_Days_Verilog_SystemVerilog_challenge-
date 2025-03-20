`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 14.03.2025 23:44:37
// Design Name: 
// Module Name: UVM_based_tb_for_alu
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


`timescale 1ns/1ps
import uvm_pkg::*;
`include "uvm_macros.svh"

// Interface for the ALU
interface alu_4bit_if(input logic clk, input logic rst_n);
    logic [3:0] a;
    logic [3:0] b;
    logic [2:0] op_code;
    logic [4:0] result;
    logic zero_flag;
    
    // Modport for the driver
    modport dut (
        input clk,
        input rst_n,
        input a,
        input b,
        input op_code,
        output result,
        output zero_flag
    );
endinterface

// UVM Transaction
class alu_transaction extends uvm_sequence_item;
    rand bit [3:0] a;
    rand bit [3:0] b;
    rand bit [2:0] op_code;
    bit [4:0] result;
    bit zero_flag;
    
    // Expected outputs
    bit [4:0] expected_result;
    bit expected_zero_flag;
    
    // UVM Automation Macros
    `uvm_object_utils_begin(alu_transaction)
        `uvm_field_int(a, UVM_ALL_ON)
        `uvm_field_int(b, UVM_ALL_ON)
        `uvm_field_int(op_code, UVM_ALL_ON)
        `uvm_field_int(result, UVM_ALL_ON)
        `uvm_field_int(zero_flag, UVM_ALL_ON)
    `uvm_object_utils_end
    
    // Constructor
    function new(string name = "alu_transaction");
        super.new(name);
    endfunction
    
    // Compute expected results
    function void compute_expected();
        case (op_code)
            3'b000: expected_result = a + b;                // ADD
            3'b001: expected_result = a - b;                // SUB
            3'b010: expected_result = a & b;                // AND
            3'b011: expected_result = a | b;                // OR
            3'b100: expected_result = a ^ b;                // XOR
            3'b101: expected_result = {1'b0, a} << 1;       // SHL
            3'b110: expected_result = {1'b0, a} >> 1;       // SHR
            default: expected_result = 5'b0;
        endcase
        
        expected_zero_flag = (expected_result == 5'b0) ? 1'b1 : 1'b0;
    endfunction
    
    // Constraint to limit operations to valid ones
    constraint valid_op_code {
        op_code inside {[0:6]};
    }
endclass

// Sequence for ALU testing
class alu_sequence extends uvm_sequence #(alu_transaction);
    `uvm_object_utils(alu_sequence)
    
    function new(string name = "alu_sequence");
        super.new(name);
    endfunction
    
    task body();
        alu_transaction tx;
        
        repeat(20) begin
            tx = alu_transaction::type_id::create("tx");
            start_item(tx);
            assert(tx.randomize());
            tx.compute_expected();
            finish_item(tx);
            #10; // Allow some time between transactions
        end
    endtask
endclass

// UVM Driver
class alu_driver extends uvm_driver #(alu_transaction);
    `uvm_component_utils(alu_driver)
    
    virtual alu_4bit_if vif;
    
    function new(string name = "alu_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual alu_4bit_if)::get(this, "", "vif", vif))
            `uvm_fatal("DRV", "Could not get virtual interface")
    endfunction
    
    task run_phase(uvm_phase phase);
        forever begin
            alu_transaction tx;
            seq_item_port.get_next_item(tx);
            
            // Drive transaction
            @(posedge vif.clk);
            vif.a <= tx.a;
            vif.b <= tx.b;
            vif.op_code <= tx.op_code;
            
            `uvm_info("DRV", $sformatf("Driving: a=%0d, b=%0d, op_code=%0d", tx.a, tx.b, tx.op_code), UVM_MEDIUM)
            
            seq_item_port.item_done();
        end
    endtask
endclass

// UVM Monitor
class alu_monitor extends uvm_monitor;
    `uvm_component_utils(alu_monitor)
    
    virtual alu_4bit_if vif;
    uvm_analysis_port #(alu_transaction) ap;
    
    function new(string name = "alu_monitor", uvm_component parent = null);
        super.new(name, parent);
        ap = new("ap", this);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if(!uvm_config_db#(virtual alu_4bit_if)::get(this, "", "vif", vif))
            `uvm_fatal("MON", "Could not get virtual interface")
    endfunction
    
    task run_phase(uvm_phase phase);
        forever begin
            alu_transaction tx = alu_transaction::type_id::create("tx");
            
            // Capture inputs
            @(posedge vif.clk);
            tx.a = vif.a;
            tx.b = vif.b;
            tx.op_code = vif.op_code;
            
            // Capture outputs on the next clock
            @(posedge vif.clk);
            tx.result = vif.result;
            tx.zero_flag = vif.zero_flag;
            
            // Compute expected results
            tx.compute_expected();
            
            `uvm_info("MON", $sformatf("Monitoring: a=%0d, b=%0d, op_code=%0d, result=%0d", 
                    tx.a, tx.b, tx.op_code, tx.result), UVM_HIGH)
            
            ap.write(tx);
        end
    endtask
endclass

// UVM Scoreboard
class alu_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(alu_scoreboard)
    
    uvm_analysis_imp #(alu_transaction, alu_scoreboard) analysis_export;
    int passed = 0;
    int failed = 0;
    
    function new(string name = "alu_scoreboard", uvm_component parent = null);
        super.new(name, parent);
        analysis_export = new("analysis_export", this);
    endfunction
    
    function void write(alu_transaction tx);
        if (tx.result === tx.expected_result && tx.zero_flag === tx.expected_zero_flag) begin
            passed++;
            `uvm_info("SCB", $sformatf("PASS: op_code=%0d, a=%0d, b=%0d, result=%0d", 
                      tx.op_code, tx.a, tx.b, tx.result), UVM_LOW)
        end else begin
            failed++;
            `uvm_error("SCB", $sformatf("FAIL: op_code=%0d, a=%0d, b=%0d", 
                      tx.op_code, tx.a, tx.b))
            `uvm_info("SCB", $sformatf("Expected: result=%0d, zero_flag=%0b", 
                      tx.expected_result, tx.expected_zero_flag), UVM_LOW)
            `uvm_info("SCB", $sformatf("Actual: result=%0d, zero_flag=%0b", 
                      tx.result, tx.zero_flag), UVM_LOW)
        end
    endfunction
    
    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("SCB", $sformatf("Scoreboard Report - Passed: %0d, Failed: %0d", passed, failed), UVM_LOW)
    endfunction
endclass

// UVM Agent
class alu_agent extends uvm_agent;
    `uvm_component_utils(alu_agent)
    
    alu_driver driver;
    alu_monitor monitor;
    uvm_sequencer #(alu_transaction) sequencer;
    
    function new(string name = "alu_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        driver = alu_driver::type_id::create("driver", this);
        monitor = alu_monitor::type_id::create("monitor", this);
        sequencer = uvm_sequencer#(alu_transaction)::type_id::create("sequencer", this);
    endfunction
    
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        driver.seq_item_port.connect(sequencer.seq_item_export);
    endfunction
endclass

// UVM Environment
class alu_env extends uvm_env;
    `uvm_component_utils(alu_env)
    
    alu_agent agent;
    alu_scoreboard scoreboard;
    
    function new(string name = "alu_env", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        agent = alu_agent::type_id::create("agent", this);
        scoreboard = alu_scoreboard::type_id::create("scoreboard", this);
    endfunction
    
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        agent.monitor.ap.connect(scoreboard.analysis_export);
    endfunction
endclass

// UVM Test
class alu_test extends uvm_test;
    `uvm_component_utils(alu_test)
    
    alu_env env;
    
    function new(string name = "alu_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = alu_env::type_id::create("env", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        alu_sequence seq;
        
        phase.raise_objection(this);
        
        seq = alu_sequence::type_id::create("seq");
        
        // Apply reset first
        reset_dut();
        
        seq.start(env.agent.sequencer);
        
        // Allow time for completion
        #100;
        
        phase.drop_objection(this);
    endtask
    
    task reset_dut();
        virtual alu_4bit_if vif;
        
        if (!uvm_config_db#(virtual alu_4bit_if)::get(this, "", "vif", vif))
            `uvm_fatal("TEST", "Could not get virtual interface")
        
        vif.a = 0;
        vif.b = 0;
        vif.op_code = 0;
        
        // Apply reset
        force tb_top.rst_n = 0;
        #20;
        release tb_top.rst_n;
    endtask
endclass

// Top-level module
module tb_top;
    logic clk;
    logic rst_n;
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // Interface instance
    alu_4bit_if alu_if(clk, rst_n);
    
    // DUT instance
    alu_4bit DUT (
        .clk(clk),
        .rst_n(rst_n),
        .a(alu_if.a),
        .b(alu_if.b),
        .op_code(alu_if.op_code),
        .result(alu_if.result),
        .zero_flag(alu_if.zero_flag)
    );
    
    // UVM Test start
    initial begin
        rst_n = 0;
        #20 rst_n = 1;
        
        // Set interface in config_db
        uvm_config_db#(virtual alu_4bit_if)::set(null, "*", "vif", alu_if);
        
        // Start UVM phases
        run_test("alu_test");
    end
endmodule
