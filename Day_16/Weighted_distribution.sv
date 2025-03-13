`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11.03.2025 12:05:06
// Design Name: 
// Module Name: Weighted_distribution
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


// Traffic light controller (RTL)
module traffic_light_controller_16 (
    input logic clk,
    input logic rst_n,
    input logic [1:0] traffic_density, // 0=low, 1=medium, 2=high
    output logic [1:0] light_state     // 0=green, 1=yellow, 2=red
);
    // State definitions
    localparam GREEN = 2'b00;
    localparam YELLOW = 2'b01;
    localparam RED = 2'b10;
    
    // Counters for timing
    logic [7:0] timer;
    logic [7:0] green_time;
    
    // State control
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            light_state <= GREEN;
            timer <= 8'h0;
            green_time <= 8'd20; // Default green time
        end else begin
            // Set green light duration based on traffic density
            case (traffic_density)
                2'b00: green_time <= 8'd20; // Low traffic
                2'b01: green_time <= 8'd40; // Medium traffic
                2'b10: green_time <= 8'd60; // High traffic
                default: green_time <= 8'd20;
            endcase
            
            // State transitions
            case (light_state)
                GREEN: begin
                    if (timer >= green_time) begin
                        light_state <= YELLOW;
                        timer <= 8'h0;
                    end else begin
                        timer <= timer + 1;
                    end
                end
                
                YELLOW: begin
                    if (timer >= 8'd10) begin // Yellow always 10 cycles
                        light_state <= RED;
                        timer <= 8'h0;
                    end else begin
                        timer <= timer + 1;
                    end
                end
                
                RED: begin
                    if (timer >= 8'd30) begin // Red always 30 cycles
                        light_state <= GREEN;
                        timer <= 8'h0;
                    end else begin
                        timer <= timer + 1;
                    end
                end
                
                default: light_state <= GREEN;
            endcase
        end
    end
endmodule

// Testbench with weighted randomization
module traffic_light_controller_16_tb;
    // Testbench signals
    logic clk;
    logic rst_n;
    logic [1:0] traffic_density;
    logic [1:0] light_state;
    
    // Instantiate the DUT
    traffic_light_controller_16 DUT (
        .clk(clk),
        .rst_n(rst_n),
        .traffic_density(traffic_density),
        .light_state(light_state)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;
    end
    
    // Traffic model with weighted distribution
    class TrafficModel;
        rand bit [1:0] density;
        rand int duration; // How long this density lasts (in clock cycles)
        
        // Constraint for traffic density distribution
        // Morning rush hour: mostly high traffic
        // Mid-day: mixed traffic
        // Evening rush hour: mostly high traffic
        // Night: mostly low traffic
        rand int time_of_day; // 0=morning, 1=mid-day, 2=evening, 3=night
        
        constraint time_dist {
            time_of_day inside {[0:3]};
        }
        
        constraint density_dist {
            if (time_of_day == 0) { // Morning rush hour
                density dist {0 := 10, 1 := 30, 2 := 60};
            } else if (time_of_day == 1) { // Mid-day
                density dist {0 := 30, 1 := 50, 2 := 20};
            } else if (time_of_day == 2) { // Evening rush hour
                density dist {0 := 10, 1 := 30, 2 := 60};
            } else { // Night
                density dist {0 := 70, 1 := 25, 2 := 5};
            }
        }
        
        // Duration based on time of day
        constraint duration_c {
            if (time_of_day inside {0, 2}) { // Rush hours: shorter changes
                duration inside {[50:150]};
            } else { // Other times: longer steady patterns
                duration inside {[100:300]};
            }
        }
        
        // Display traffic model info
        function void display();
            string tod_str;
            string density_str; // Properly declare the variable
            
            case (time_of_day)
                0: tod_str = "Morning Rush";
                1: tod_str = "Mid-day";
                2: tod_str = "Evening Rush";
                3: tod_str = "Night";
            endcase
            
            case (density)
                0: density_str = "Low";
                1: density_str = "Medium";
                2: density_str = "High";
            endcase        
        /* Display traffic model info
        function void display();
            string tod_str;
            case (time_of_day)
                0: tod_str = "Morning Rush";
                1: tod_str = "Mid-day";
                2: tod_str = "Evening Rush";
                3: tod_str = "Night";
            endcase
            
            string density_str;
            case (density)
                0: density_str = "Low";
                1: density_str = "Medium";
                2: density_str = "High";
            endcase*/
            
            $display("Time of Day: %s, Traffic Density: %s, Duration: %0d cycles",
                    tod_str, density_str, duration);
        endfunction
    endclass
    
    // Test statistics
    int density_counts[3] = '{0, 0, 0};
    int time_of_day_counts[4] = '{0, 0, 0, 0};
    int total_samples = 0;
    
    // Test stimulus with weighted randomization
    initial begin
        TrafficModel traffic;
        
        // Initialize signals
        rst_n = 0;
        traffic_density = 0;
        
        // Reset sequence
        #20 rst_n = 1;
        
        // Run randomized traffic patterns
        for (int sim_hour = 0; sim_hour < 24; sim_hour++) begin
            // Determine time of day category
            int time_category;
            if (sim_hour >= 6 && sim_hour < 9) time_category = 0; // Morning rush 6-9am
            else if (sim_hour >= 9 && sim_hour < 16) time_category = 1; // Mid-day 9am-4pm
            else if (sim_hour >= 16 && sim_hour < 19) time_category = 2; // Evening rush 4-7pm
            else time_category = 3; // Night time
            
            $display("\n--- Hour %0d (Time Category: %0d) ---", sim_hour, time_category);
            
            // Generate several traffic patterns per hour
            repeat (5) begin
                traffic = new();
                traffic.time_of_day = time_category; // Force time of day
                assert(traffic.randomize()) else $fatal("Randomization failed");
                traffic.display();
                
                // Update statistics
                density_counts[traffic.density]++;
                time_of_day_counts[traffic.time_of_day]++;
                total_samples++;
                
                // Apply traffic pattern
                traffic_density = traffic.density;
                
                // Let the traffic pattern run for its duration
                repeat (traffic.duration) @(posedge clk);
            end
        end
        
        // Display distribution statistics
        $display("\n--- Traffic Distribution Statistics ---");
        $display("Low Traffic: %0d (%0.2f%%)", 
                density_counts[0], 100.0 * density_counts[0] / total_samples);
        $display("Medium Traffic: %0d (%0.2f%%)", 
                density_counts[1], 100.0 * density_counts[1] / total_samples);
        $display("High Traffic: %0d (%0.2f%%)", 
                density_counts[2], 100.0 * density_counts[2] / total_samples);
        
        // End simulation
        #50 $finish;
    end
    
    // Monitor state transitions
    string state_names[3] = '{"GREEN", "YELLOW", "RED"};
    
    always @(light_state) begin
        $display("At time %0t: Light changed to %s", $time, state_names[light_state]);
    end
endmodule
