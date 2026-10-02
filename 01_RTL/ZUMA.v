/**************************************************************************/
// Copyright (c) 2026, SI2 Lab
// MODULE: ZUMA
// FILE NAME: ZUMA.v
// DESCRIPTION: 2026 Fall IC Lab / Exercise Lab03 / ZUMA
//
// Architecture (v7):
//   - The ring is a 256-entry register array in logical order.  Insert and
//     delete are parallel shifts (right to insert, left to delete) that share
//     ONE threshold thermometer.
//   - A shot is *scanned* on the old ring (the new bead is virtual, it sits
//     between old index pos and pos+1).  Every cascade level only extends the
//     eliminated interval outward, so the union of all levels is one
//     contiguous (cyclic) interval: we walk outwards level by level and delete
//     the whole interval ONCE, in the background while the answer is streamed.
//   - The scan reads a WINDOW of 4 consecutive beads per side per cycle.  The
//     ring is viewed as 4 banks (index mod 4); a 4-bead window needs one
//     64:1 mux per bank, which costs about the same as one 256:1 read port.
//   - The cascade results are kept in a shift register (fixed read taps).
/**************************************************************************/

module ZUMA (
    input               clk,
    input               rst_n,
    // ---- ring loading phase ----
    input               in_valid,
    input      [7:0]    ring_len,
    input      [2:0]    in_color,
    // ---- shooting phase ----
    input               shot_valid,
    input      [2:0]    shot_color,
    input      [7:0]    shot_pos,
    // ---- outputs ----
    output reg          out_valid,
    output reg [6:0]    chain_num,
    output reg [2:0]    elim_color,
    output reg [8:0]    elim_cnt
);

//---------------------------------------------------------------------
//   PARAMETER
//---------------------------------------------------------------------
localparam S_IDLE  = 4'd0;   // wait for a shot / loading
localparam S_START = 4'd1;   // start a shot that arrived while deleting
localparam S_SCAN  = 4'd2;   // read a window on each side
localparam S_ADDR  = 4'd3;   // compute the window addresses of the next step
localparam S_DEC   = 4'd4;   // decide / commit one cascade level
localparam S_INSN  = 4'd5;   // no elimination : insert the shot bead
localparam S_APP0  = 4'd6;   // empty ring : shot bead becomes index 0
localparam S_DEL   = 4'd7;   // delete the eliminated interval
localparam S_PRE   = 4'd8;   // compute the delete parameters (wrap case)

// Max cascade levels one shot can trigger.  Each level removes >= 3 beads, so a
// ring of at most 256 beads gives at most 86 levels (safe for any legal pattern).
// A smaller value saves about 940 um^2 per level but fails if a pattern ever
// builds a deeper cascade (nested rings of up to 128 beads need 43 levels).
localparam LV_DEPTH = 86;

//---------------------------------------------------------------------
//   REG & WIRE DECLARATION
//---------------------------------------------------------------------
reg  [3:0]  state;
reg         in_valid_r;
reg  [2:0]  in_color_r;
reg         loading;
reg         pend;

reg  [2:0]  ring [0:255];
reg  [8:0]  M;               // beads in the ring (old coordinates while scanning)

reg  [2:0]  col_r;           // saved shot
reg  [7:0]  pos_r;

reg  [2:0]  c;               // color of the level being scanned
reg  [7:0]  lidx, ridx;      // next bead to examine on each side (old coordinates)
reg  [8:0]  lenc;            // length of the run found so far (incl. virtual bead)
reg  [8:0]  room;            // beads still available to this level
reg         ldone, rdone;
reg         lvl1;            // first level : the shot bead is virtual
reg         crossed;         // a scan pointer wrapped around the ring boundary
reg  [2:0]  a_val, b_val;    // first non-matching bead on the left / right

reg  [7:0]  dst;             // leftmost eliminated bead of the committed levels
reg  [8:0]  dcnt;            // old beads eliminated by the committed levels
reg  [8:0]  tail;            // M - dst
reg         allf;            // committed levels already cover the whole ring
reg  [6:0]  chain;           // levels committed

reg  [7:0]  sst;             // shift start of the deletion
reg  [8:0]  shifts;          // beads still to shift out

reg         out_act;
reg  [6:0]  out_rem;

// window address registers (one 6-bit block address per bank)
reg  [5:0]  la0, la1, la2, la3, ra0, ra1, ra2, ra3;
reg  [1:0]  loff, roff;
reg  [2:0]  nvL, nvR;        // valid beads inside each window (0 < nv <= 4)

reg  [2:0]  lv_col [0:LV_DEPTH-1];
reg  [7:0]  lv_cnt [0:LV_DEPTH-1];   // stored as (length - 3), lengths are 3..256

integer i, j;

//---------------------------------------------------------------------
//   BANKED WINDOW READ
//---------------------------------------------------------------------
wire [2:0] bk0 [0:63];
wire [2:0] bk1 [0:63];
wire [2:0] bk2 [0:63];
wire [2:0] bk3 [0:63];
genvar gk;
generate
    for (gk = 0; gk < 64; gk = gk + 1) begin : g_bank
        assign bk0[gk] = ring[4 * gk];
        assign bk1[gk] = ring[4 * gk + 1];
        assign bk2[gk] = ring[4 * gk + 2];
        assign bk3[gk] = ring[4 * gk + 3];
    end
endgenerate

wire [2:0] lo0 = bk0[la0];
wire [2:0] lo1 = bk1[la1];
wire [2:0] lo2 = bk2[la2];
wire [2:0] lo3 = bk3[la3];
wire [2:0] ro0 = bk0[ra0];
wire [2:0] ro1 = bk1[ra1];
wire [2:0] ro2 = bk2[ra2];
wire [2:0] ro3 = bk3[ra3];

// wL[k] = bead at lidx-k, wR[k] = bead at ridx+k
reg  [2:0] wL0, wL1, wL2, wL3, wR0, wR1, wR2, wR3;
always @(*) begin
    case (loff)
        2'd0: begin wL0 = lo3; wL1 = lo2; wL2 = lo1; wL3 = lo0; end
        2'd1: begin wL0 = lo0; wL1 = lo3; wL2 = lo2; wL3 = lo1; end
        2'd2: begin wL0 = lo1; wL1 = lo0; wL2 = lo3; wL3 = lo2; end
        default: begin wL0 = lo2; wL1 = lo1; wL2 = lo0; wL3 = lo3; end
    endcase
    case (roff)
        2'd0: begin wR0 = ro0; wR1 = ro1; wR2 = ro2; wR3 = ro3; end
        2'd1: begin wR0 = ro1; wR1 = ro2; wR2 = ro3; wR3 = ro0; end
        2'd2: begin wR0 = ro2; wR1 = ro3; wR2 = ro0; wR3 = ro1; end
        default: begin wR0 = ro3; wR1 = ro0; wR2 = ro1; wR3 = ro2; end
    endcase
end

//---------------------------------------------------------------------
//   WINDOW ADDRESS UNIT : address of an ascending 4-bead window at index s
//---------------------------------------------------------------------
function [25:0] win_addr;
    input [7:0] s;
    reg   [5:0] base, base1;
    reg   [1:0] off;
    begin
        base  = s[7:2];
        base1 = base + 6'd1;
        off   = s[1:0];
        win_addr = {(2'd3 < off) ? base1 : base,
                    (2'd2 < off) ? base1 : base,
                    (2'd1 < off) ? base1 : base,
                    (2'd0 < off) ? base1 : base,
                    off};
    end
endfunction

wire [8:0] Mm1_9 = M - 9'd1;
wire [7:0] Mm1   = Mm1_9[7:0];

// (a) start of a shot, straight from the input pins
wire [8:0] g_p1_i = {1'b0, shot_pos} + 9'd1;
wire       wr0_i  = (g_p1_i == M);
wire [25:0] wl_i  = win_addr(shot_pos - 8'd3);
wire [25:0] wr_i  = wr0_i ? win_addr(8'd0) : win_addr(g_p1_i[7:0]);
wire [2:0]  nvL_i = (shot_pos >= 8'd3) ? 3'd4 : ({1'b0, shot_pos[1:0]} + 3'd1);
wire [8:0]  mi_i  = Mm1_9 - {1'b0, shot_pos};
wire [2:0]  nvR_i = wr0_i ? ((M >= 9'd4) ? 3'd4 : M[2:0])
                          : ((mi_i >= 9'd4) ? 3'd4 : mi_i[2:0]);

// (b) from registers : saved shot, next cascade level, next scan step
wire [8:0] pr1_9  = {1'b0, pos_r} + 9'd1;
wire [7:0] pr1    = (pr1_9 == M) ? 8'd0 : pr1_9[7:0];
wire [7:0] l_decp = (lidx == 8'd0) ? Mm1 : (lidx - 8'd1);
wire [7:0] r_incp = (ridx == Mm1)  ? 8'd0 : (ridx + 8'd1);
wire [7:0] gL = (state == S_START) ? pos_r :
                (state == S_DEC)   ? l_decp : lidx;
wire [7:0] gR = (state == S_START) ? pr1 :
                (state == S_DEC)   ? r_incp : ridx;
wire [25:0] wl_g  = win_addr(gL - 8'd3);
wire [25:0] wr_g  = win_addr(gR);
wire [2:0]  nvL_g = (gL >= 8'd3) ? 3'd4 : ({1'b0, gL[1:0]} + 3'd1);
wire [8:0]  mg    = M - {1'b0, gR};
wire [2:0]  nvR_g = (mg >= 9'd4) ? 3'd4 : mg[2:0];

//---------------------------------------------------------------------
//   SCAN STEP
//---------------------------------------------------------------------
wire [3:0] mL = {(nvL > 3'd3) & (wL3 == c), (nvL > 3'd2) & (wL2 == c),
                 (nvL > 3'd1) & (wL1 == c), (wL0 == c)};
wire [3:0] mR = {(nvR > 3'd3) & (wR3 == c), (nvR > 3'd2) & (wR2 == c),
                 (nvR > 3'd1) & (wR1 == c), (wR0 == c)};
wire [2:0] lc = ~mL[0] ? 3'd0 : ~mL[1] ? 3'd1 : ~mL[2] ? 3'd2 : ~mL[3] ? 3'd3 : 3'd4;
wire [2:0] rc = ~mR[0] ? 3'd0 : ~mR[1] ? 3'd1 : ~mR[2] ? 3'd2 : ~mR[3] ? 3'd3 : 3'd4;
wire       lact  = ~ldone;
wire       ract  = ~rdone;
wire [2:0] lcm   = lact ? lc : 3'd0;
wire [2:0] rcm   = ract ? rc : 3'd0;
wire       lstop = lact & (lc < nvL);        // mismatch bead lies inside the window
wire       rstop = ract & (rc < nvR);

wire [2:0] lext  = (room >= {6'd0, lcm}) ? lcm : room[2:0];
wire [8:0] room_l = room - {6'd0, lext};
wire [2:0] rext  = (room_l >= {6'd0, rcm}) ? rcm : room_l[2:0];
wire [8:0] room_n = room_l - {6'd0, rext};
wire       cap   = (room_n == 9'd0);
wire       ldone_n = ldone | lstop | cap;
wire       rdone_n = rdone | rstop | cap;
wire       fin   = ldone_n & rdone_n;
wire [8:0] lenc_n = lenc + {6'd0, lext} + {6'd0, rext};

wire [2:0] wL_sel = (lc == 3'd0) ? wL0 : (lc == 3'd1) ? wL1 : (lc == 3'd2) ? wL2 : wL3;
wire [2:0] wR_sel = (rc == 3'd0) ? wR0 : (rc == 3'd1) ? wR1 : (rc == 3'd2) ? wR2 : wR3;

wire       wrapL  = ({6'd0, lext} > {1'b0, lidx});
wire [8:0] lidx_w = {1'b0, lidx} + M - {6'd0, lext};
wire [7:0] lidx_n = wrapL ? lidx_w[7:0] : (lidx - {5'd0, lext});
wire [8:0] ridx_s = {1'b0, ridx} + {6'd0, rext};
wire       wrapR  = (rext != 3'd0) & (ridx_s >= M);
wire [8:0] ridx_m = ridx_s - M;
wire [7:0] ridx_n = wrapR ? ridx_m[7:0] : ridx_s[7:0];

// the very first step of a shot found no neighbour of the shot color
wire       qnoel  = (state == S_SCAN) & lvl1 & (lenc == 9'd1) & lact & ract &
                    (lc == 3'd0) & (rc == 3'd0);

//---------------------------------------------------------------------
//   DECISION / COMMIT STAGE (registers only)
//---------------------------------------------------------------------
wire       ge3     = (lenc >= 9'd3);
wire       cont    = (room >= 9'd3) & (a_val == b_val);
wire [7:0] dst_n   = (lidx == Mm1) ? 8'd0 : (lidx + 8'd1);
wire [8:0] dcnt_n  = M - room;
wire [6:0] chain_c = chain + 7'd1;

wire noelim_d  = (state == S_DEC) & ~ge3 & lvl1;
wire scan_bad  = (state == S_DEC) & ~ge3 & ~lvl1;
wire commit    = (state == S_DEC) & ge3;
wire term_cmt  = commit & ~cont;

// delete parameters for the wrap case (from registers)
wire       wrap_p = (dcnt > tail);          // dst + dcnt > M
wire       all_p  = allf;
wire [8:0] sh_p   = dcnt - tail;

//---------------------------------------------------------------------
//   RING STORAGE : insert / delete share one threshold
//---------------------------------------------------------------------
wire go_idle  = (state == S_IDLE) && shot_valid;
wire go_start = (state == S_START);
wire go_any   = (go_idle | go_start) & ~in_valid_r;
wire [2:0] g_col = go_start ? col_r : shot_color;
wire [7:0] g_pos = go_start ? pos_r : shot_pos;
wire [8:0] g_p1  = go_start ? pr1_9 : g_p1_i;

wire ins_ld = in_valid_r;
wire ins_n  = (state == S_INSN) & ~in_valid_r;
wire ins_a0 = (state == S_APP0) & ~in_valid_r;
wire ins_op = ins_ld | ins_n | ins_a0;
wire shl    = (state == S_DEL) & ~in_valid_r;
wire k2     = (shifts >= 9'd2);

wire [8:0] thr   = ins_ld ? (loading ? M : 9'd0) :
                   ins_n  ? ({1'b0, pos_r} + 9'd1) :
                   ins_a0 ? 9'd0 : {1'b0, sst};
wire [2:0] wdata = ins_ld ? in_color_r : col_r;

// one thermometer of the threshold shared by insert and delete:
//   ge[i] : i >= thr      gt[i] : i > thr      (i == thr) is ge & ~gt
wire [255:0] ge;
wire [255:0] gt = {ge[254:0], 1'b0};
genvar gi;
generate
    for (gi = 0; gi < 256; gi = gi + 1) begin : g_therm
        assign ge[gi] = (thr <= gi);
    end
endgenerate

always @(posedge clk) begin
    for (i = 0; i < 256; i = i + 1) begin
        if (ins_op) begin
            if (ge[i] & ~gt[i]) ring[i] <= wdata;
            else if (gt[i])     ring[i] <= ring[(i == 0) ? 0 : i - 1];
        end
        else if (shl) begin
            if (ge[i])
                ring[i] <= k2 ? ring[(i + 2 > 255) ? 255 : i + 2]
                              : ring[(i + 1 > 255) ? 255 : i + 1];
        end
    end
end

//---------------------------------------------------------------------
//   LEVEL STORAGE (shift register, fixed read taps lv[0] / lv[1])
//---------------------------------------------------------------------
always @(posedge clk) begin
    if (commit) begin
        lv_col[chain] <= c;
        lv_cnt[chain] <= lenc[7:0] - 8'd3;
    end
    else if (out_act && out_rem != 7'd0) begin
        for (j = 0; j < LV_DEPTH - 1; j = j + 1) begin
            lv_col[j] <= lv_col[j + 1];
            lv_cnt[j] <= lv_cnt[j + 1];
        end
    end
end

//---------------------------------------------------------------------
//   WINDOW ADDRESS REGISTERS
//---------------------------------------------------------------------
wire ld_i = go_idle & ~in_valid_r & (M != 9'd0);
wire ld_g = ((state == S_START) & ~in_valid_r & (M != 9'd0)) | (state == S_ADDR) |
            (state == S_DEC);
wire [25:0] wl_x  = ld_i ? wl_i  : wl_g;
wire [25:0] wr_x  = ld_i ? wr_i  : wr_g;
wire [2:0]  nvL_x = ld_i ? nvL_i : nvL_g;
wire [2:0]  nvR_x = ld_i ? nvR_i : nvR_g;

always @(posedge clk) begin
    if (ld_i | ld_g) begin
        {la3, la2, la1, la0, loff} <= wl_x;
        {ra3, ra2, ra1, ra0, roff} <= wr_x;
        nvL <= nvL_x;
        nvR <= nvR_x;
    end
end

//---------------------------------------------------------------------
//   OUTPUT START
//---------------------------------------------------------------------
wire       empty_go = go_any && (M == 9'd0);
wire       out_go   = qnoel | noelim_d | term_cmt | scan_bad | empty_go;
wire [6:0] cf       = term_cmt ? chain_c : (scan_bad ? chain : 7'd0);
wire       use_cur  = term_cmt && (chain == 7'd0);
wire       use_lv0  = (term_cmt && (chain != 7'd0)) || scan_bad;
wire [2:0] fb_col   = use_cur ? c    : (use_lv0 ? lv_col[0] : 3'd0);
wire [8:0] fb_cnt   = use_cur ? lenc : (use_lv0 ? ({1'b0, lv_cnt[0]} + 9'd3) : 9'd0);

//---------------------------------------------------------------------
//   CONTROL
//---------------------------------------------------------------------
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        state      <= S_IDLE;
        in_valid_r <= 1'b0;
        in_color_r <= 3'd0;
        loading    <= 1'b0;
        pend       <= 1'b0;
        M          <= 9'd0;
        col_r      <= 3'd0;
        pos_r      <= 8'd0;
        c          <= 3'd0;
        lidx       <= 8'd0;
        ridx       <= 8'd0;
        lenc       <= 9'd0;
        room       <= 9'd0;
        ldone      <= 1'b0;
        rdone      <= 1'b0;
        lvl1       <= 1'b0;
        crossed    <= 1'b0;
        a_val      <= 3'd0;
        b_val      <= 3'd0;
        dst        <= 8'd0;
        dcnt       <= 9'd0;
        tail       <= 9'd0;
        allf       <= 1'b0;
        chain      <= 7'd0;
        sst        <= 8'd0;
        shifts     <= 9'd0;
        out_act    <= 1'b0;
        out_rem    <= 7'd0;
        out_valid  <= 1'b0;
        chain_num  <= 7'd0;
        elim_color <= 3'd0;
        elim_cnt   <= 9'd0;
    end
    else begin
        in_valid_r <= in_valid;
        in_color_r <= in_color;
        loading    <= in_valid_r;

        // ---- stream the remaining levels ----
        if (out_act) begin
            if (out_rem != 7'd0) begin
                elim_color <= lv_col[1];
                elim_cnt   <= {1'b0, lv_cnt[1]} + 9'd3;
                out_rem    <= out_rem - 7'd1;
            end
            else begin
                out_valid  <= 1'b0;
                chain_num  <= 7'd0;
                elim_color <= 3'd0;
                elim_cnt   <= 9'd0;
                out_act    <= 1'b0;
            end
        end

        if (in_valid_r) begin
            // loading phase (a new game discards everything)
            M     <= loading ? (M + 9'd1) : 9'd1;
            state <= S_IDLE;
            pend  <= 1'b0;
        end
        else begin
            case (state)
                //-----------------------------------------------------
                S_IDLE, S_START: begin
                    if (go_any) begin
                        col_r <= g_col;
                        pos_r <= g_pos;
                        if (M == 9'd0) state <= S_APP0;
                        else begin
                            c       <= g_col;
                            lidx    <= g_pos;
                            ridx    <= (g_p1 == M) ? 8'd0 : g_p1[7:0];
                            lenc    <= 9'd1;
                            room    <= M;
                            ldone   <= 1'b0;
                            rdone   <= 1'b0;
                            lvl1    <= 1'b1;
                            crossed <= (g_p1 == M);
                            chain   <= 7'd0;
                            state   <= S_SCAN;
                        end
                    end
                end
                //-----------------------------------------------------
                S_SCAN: begin
                    if (qnoel) state <= S_INSN;
                    else begin
                        lenc    <= lenc_n;
                        room    <= room_n;
                        ldone   <= ldone_n;
                        rdone   <= rdone_n;
                        lidx    <= lidx_n;
                        ridx    <= ridx_n;
                        crossed <= crossed | wrapL | wrapR;
                        if (lstop) a_val <= wL_sel;
                        if (rstop) b_val <= wR_sel;
                        state   <= fin ? S_DEC : S_ADDR;
                    end
                end
                //-----------------------------------------------------
                S_ADDR: state <= S_SCAN;
                //-----------------------------------------------------
                S_DEC: begin
                    if (noelim_d) state <= S_INSN;
                    else if (scan_bad) state <= S_PRE;
                    else begin
                        // commit this level
                        chain <= chain_c;
                        dst   <= dst_n;
                        dcnt  <= dcnt_n;
                        tail  <= M - {1'b0, dst_n};
                        allf  <= (room == 9'd0);
                        if (cont) begin
                            c       <= a_val;
                            lenc    <= 9'd2;
                            room    <= room - 9'd2;
                            lidx    <= l_decp;
                            ridx    <= r_incp;
                            ldone   <= 1'b0;
                            rdone   <= 1'b0;
                            lvl1    <= 1'b0;
                            crossed <= crossed | (lidx == 8'd0) | (ridx == Mm1);
                            state   <= S_SCAN;
                        end
                        else if (room == 9'd0) begin
                            M     <= 9'd0;
                            state <= S_IDLE;
                        end
                        else if (!crossed) begin
                            sst    <= dst_n;
                            shifts <= dcnt_n;
                            state  <= S_DEL;
                        end
                        else state <= S_PRE;
                    end
                end
                //-----------------------------------------------------
                S_INSN: begin
                    M     <= M + 9'd1;
                    state <= S_IDLE;
                end
                //-----------------------------------------------------
                S_APP0: begin
                    M     <= 9'd1;
                    state <= S_IDLE;
                end
                //-----------------------------------------------------
                S_PRE: begin
                    if (all_p) begin
                        M     <= 9'd0;
                        state <= S_IDLE;
                    end
                    else begin
                        M      <= wrap_p ? {1'b0, dst} : M;
                        sst    <= wrap_p ? 8'd0 : dst;
                        shifts <= wrap_p ? sh_p : dcnt;
                        state  <= S_DEL;
                    end
                end
                //-----------------------------------------------------
                S_DEL: begin
                    if (shot_valid) begin
                        col_r <= shot_color;
                        pos_r <= shot_pos;
                        pend  <= 1'b1;
                    end
                    M      <= M - (k2 ? 9'd2 : 9'd1);
                    shifts <= shifts - (k2 ? 9'd2 : 9'd1);
                    if (shifts == 9'd1 || shifts == 9'd2) begin
                        state <= (pend | shot_valid) ? S_START : S_IDLE;
                        pend  <= 1'b0;
                    end
                end
                default: state <= S_IDLE;
            endcase

            // ---- start the output sequence ----
            if (out_go) begin
                out_valid  <= 1'b1;
                chain_num  <= cf;
                elim_color <= fb_col;
                elim_cnt   <= fb_cnt;
                out_rem    <= (cf == 7'd0) ? 7'd0 : (cf - 7'd1);
                out_act    <= 1'b1;
            end
        end
    end
end

endmodule
