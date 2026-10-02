/**************************************************************************/
// Copyright (c) 2026, SI2 Lab
// MODULE: PATTERN
// FILE NAME: PATTERN.v
// VERSRION: 1.0
// DATE: Aug 01, 2026
// AUTHOR: NYCU IEE
// CODE TYPE: RTL or Behavioral Level (Verilog)
// DESCRIPTION: 2026 Fall IC Lab / Exersise Lab03 / ZUMA
// MODIFICATION HISTORY:
// Date                 Description
//
/**************************************************************************/
`timescale 1ns/10ps

`ifdef RTL
    `define CYCLE_TIME 15.0
`endif
`ifdef GATE
    `define CYCLE_TIME 15.0
`endif
`ifndef CYCLE_TIME
    `define CYCLE_TIME 15.0
`endif

module PATTERN (
    // Output
    clk,
    rst_n,
    in_valid,
    ring_len,
    in_color,
    shot_valid,
    shot_color,
    shot_pos,
    // Input
    out_valid,
    chain_num,
    elim_color,
    elim_cnt
);

//---------------------------------------------------------------------
//   PORT DECLARATION
//---------------------------------------------------------------------
output reg          clk;
output reg          rst_n;
output reg          in_valid;
output reg [7:0]    ring_len;
output reg [2:0]    in_color;
output reg          shot_valid;
output reg [2:0]    shot_color;
output reg [7:0]    shot_pos;

input               out_valid;
input      [6:0]    chain_num;
input      [2:0]    elim_color;
input      [8:0]    elim_cnt;

//---------------------------------------------------------------------
//   PARAMETER & INTEGER DECLARATION
//---------------------------------------------------------------------
integer total_latency;
real    CYCLE = `CYCLE_TIME;
integer MAX_LAT = 1000;

integer fin;
integer pat_num, pat;
integer len_i, shot_num, shot_i;
integer i, tmp_i;
integer sh_color, sh_pos;
integer gap;
integer lat, out_idx, first_chain;
integer exp_cycles;

// golden model storage
integer gring [0:1023];
integer gtmp  [0:1023];
integer gM;
integer g_chain;
integer g_col [0:511];
integer g_cnt [0:511];

// monitor control
reg     mon_en;     // enable SPEC-5 / SPEC-6 monitors
reg     chk_low;    // out_valid must be low at the next posedge
reg     stopped;    // print only one keyword

//---------------------------------------------------------------------
//   CLOCK
//---------------------------------------------------------------------
initial clk = 1'b0;
always #(CYCLE/2.0) clk = ~clk;

//---------------------------------------------------------------------
//   FAIL REPORT (only one keyword is ever printed)
//---------------------------------------------------------------------
task report_spec;
    input integer n;
    begin
        if (!stopped) begin
            stopped = 1'b1;
            $display("                    SPEC-%0d FAIL                   ", n);
            $finish;
        end
    end
endtask

//---------------------------------------------------------------------
//   SPEC-5 / SPEC-6 / out_valid-low monitors (sampled at posedge)
//---------------------------------------------------------------------
always @(posedge clk) begin
    if (mon_en && !stopped) begin
        // SPEC 9 : out_valid stays high longer than chain_num cycles
        if (chk_low && out_valid !== 1'b0)
            report_spec(9);
        // SPEC 6 : out_valid must not overlap with in_valid / shot_valid
        else if (out_valid === 1'b1 && (in_valid === 1'b1 || shot_valid === 1'b1))
            report_spec(6);
        // SPEC 5 : outputs are 0 when out_valid is 0
        else if (out_valid !== 1'b1 &&
                 (out_valid !== 1'b0 || chain_num !== 7'd0 ||
                  elim_color !== 3'd0 || elim_cnt !== 9'd0))
            report_spec(5);
        // SPEC 5 : elim_color / elim_cnt are 0 when chain_num is 0
        else if (out_valid === 1'b1 && chain_num === 7'd0 &&
                 (elim_color !== 3'd0 || elim_cnt !== 9'd0))
            report_spec(5);
    end
    if (chk_low) chk_low = 1'b0;
end

//---------------------------------------------------------------------
//   GOLDEN MODEL
//---------------------------------------------------------------------
integer gp, gc, gL, gR, glen, gstart, ge, gnewM, gnb, gna, gdone, gi;

task calc_golden;
    input integer color;
    input integer pos;
    begin
        g_chain = 0;
        if (gM == 0) begin
            gring[0] = color;
            gM = 1;
            gp = 0;
        end
        else begin
            for (gi = gM; gi > pos + 1; gi = gi - 1) gring[gi] = gring[gi-1];
            gring[pos+1] = color;
            gM = gM + 1;
            gp = pos + 1;
        end

        gdone = 0;
        while (!gdone) begin
            gc = gring[gp];
            gL = 0;
            gR = 0;
            while ((gL + gR + 1 < gM) && (gring[(gp - gL - 1 + gM) % gM] == gc)) gL = gL + 1;
            while ((gL + gR + 1 < gM) && (gring[(gp + gR + 1) % gM] == gc))      gR = gR + 1;
            glen = gL + gR + 1;

            if (glen < 3) gdone = 1;
            else begin
                gstart = (gp - gL + gM) % gM;
                ge     = (gstart + glen - 1) % gM;
                g_col[g_chain] = gc;
                g_cnt[g_chain] = glen;
                g_chain = g_chain + 1;
                gnewM = gM - glen;

                if (gstart != 0 && gstart + glen <= gM) begin
                    // segment does not contain logical index 0 : plain delete
                    for (gi = 0; gi < gstart; gi = gi + 1)  gtmp[gi]        = gring[gi];
                    for (gi = gstart + glen; gi < gM; gi = gi + 1) gtmp[gi - glen] = gring[gi];
                    gnb = (gnewM > 0) ? (gstart % gnewM) : 0;
                end
                else begin
                    // index 0 eliminated : first survivor after segment becomes index 0
                    for (gi = 1; gi <= gnewM; gi = gi + 1) gtmp[gi-1] = gring[(ge + gi) % gM];
                    gnb = 0;
                end

                for (gi = 0; gi < gnewM; gi = gi + 1) gring[gi] = gtmp[gi];
                gM = gnewM;

                if (gM < 3) gdone = 1;
                else begin
                    gna = (gnb + gM - 1) % gM;
                    if (gring[gna] == gring[gnb]) gp = gna;
                    else                          gdone = 1;
                end
            end
        end
    end
endtask

//---------------------------------------------------------------------
//   TASKS
//---------------------------------------------------------------------
// SPEC 4 : every output must be 0 right after reset is asserted
task reset_task;
    begin
        stopped    = 1'b0;
        mon_en     = 1'b0;
        chk_low    = 1'b0;
        rst_n      = 1'b1;
        in_valid   = 1'b0;
        ring_len   = 8'bx;
        in_color   = 3'bx;
        shot_valid = 1'b0;
        shot_color = 3'bx;
        shot_pos   = 8'bx;
        #(CYCLE);
        rst_n = 1'b0;
        #(100);
        if (out_valid !== 1'b0 || chain_num !== 7'd0 ||
            elim_color !== 3'd0 || elim_cnt !== 9'd0)
            report_spec(4);
        #(CYCLE/4.0);
        rst_n  = 1'b1;
        mon_en = 1'b1;
    end
endtask

task rand_gap;   // 1 ~ 4
    begin
        gap = $urandom_range(1, 4);
    end
endtask

// Ring loading phase : in_valid high for exactly ring_len cycles
task load_ring;
    begin
        for (i = 0; i < len_i; i = i + 1) begin
            in_valid = 1'b1;
            in_color = gring[i];
            ring_len = (i == 0) ? len_i : 8'bx;
            @(negedge clk);
        end
        in_valid = 1'b0;
        in_color = 3'bx;
        ring_len = 8'bx;
    end
endtask

task drive_shot;
    input integer color;
    input integer pos;
    begin
        shot_valid = 1'b1;
        shot_color = color;
        shot_pos   = pos;
        @(negedge clk);
        shot_valid = 1'b0;
        shot_color = 3'bx;
        shot_pos   = 8'bx;
    end
endtask

// SPEC 7 / 8 / 9 : wait for and check the response of one shot
task check_output;
    begin
        exp_cycles = (g_chain == 0) ? 1 : g_chain;

        // SPEC 7 : wait for out_valid
        lat = 0;
        @(posedge clk);
        lat = lat + 1;
        while (out_valid !== 1'b1) begin
            if (lat >= MAX_LAT) report_spec(7);
            @(posedge clk);
            lat = lat + 1;
        end

        first_chain = chain_num;
        for (out_idx = 0; out_idx < exp_cycles; out_idx = out_idx + 1) begin
            if (out_idx != 0) begin
                @(posedge clk);
                lat = lat + 1;
                // SPEC 9 : out_valid must stay high for exactly the expected cycles
                if (out_valid !== 1'b1) report_spec(9);
                // SPEC 9 : chain_num must stay constant
                if (chain_num !== first_chain[6:0]) report_spec(9);
            end
            // SPEC 8 : answer correct
            if (chain_num !== g_chain[6:0]) report_spec(8);
            if (g_chain != 0) begin
                if (elim_color !== g_col[out_idx][2:0]) report_spec(8);
                if (elim_cnt   !== g_cnt[out_idx][8:0]) report_spec(8);
            end
        end

        // SPEC 7 : latency measured up to the falling edge of out_valid
        if (lat > MAX_LAT) report_spec(7);
        total_latency = total_latency + lat;
`ifdef LAT_DEBUG
        $display("shot %0d: chain=%0d lat=%0d", shot_i, g_chain, lat);
`endif

        // out_valid must fall after the last expected cycle (checked by monitor)
        @(negedge clk);
        chk_low = 1'b1;
        rand_gap;
        repeat (gap - 1) @(negedge clk);
    end
endtask

//---------------------------------------------------------------------
//   MAIN
//---------------------------------------------------------------------
initial begin
    fin = $fopen("../00_TESTBED/input.txt", "r");
    if (fin == 0) begin
        $display("Cannot open input.txt");
        $finish;
    end
    tmp_i = $fscanf(fin, "%d", pat_num);
    total_latency = 0;

    reset_task;
    @(negedge clk);
    rand_gap;
    repeat (gap) @(negedge clk);

    for (pat = 0; pat < pat_num; pat = pat + 1) begin
        tmp_i = $fscanf(fin, "%d %d", len_i, shot_num);
        for (i = 0; i < len_i; i = i + 1) tmp_i = $fscanf(fin, "%d", gring[i]);
        gM = len_i;

        load_ring;
        rand_gap;
        repeat (gap) @(negedge clk);

        for (shot_i = 0; shot_i < shot_num; shot_i = shot_i + 1) begin
            tmp_i = $fscanf(fin, "%d %d", sh_color, sh_pos);
            calc_golden(sh_color, sh_pos);
            drive_shot(sh_color, sh_pos);
            check_output;
        end
    end

    if (!stopped) begin
        $display("                  Congratulations!               ");
        $display("              total execution latency = %0d", total_latency);
        $display("              clock period = %0.1fns", CYCLE);
        $finish;
    end
end

endmodule
