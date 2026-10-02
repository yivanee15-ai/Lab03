/**************************************************************************/
// Copyright (c) 2026, SI2 Lab
// MODULE: ZUMA
// FILE NAME: ZUMA.v
// DESCRIPTION: 2026 Fall IC Lab / Exercise Lab03 / ZUMA
//
// Architecture (v2):
//   - The ring is a 256-entry register array in logical order.  Insert and
//     delete are both done with parallel shifts (right shift to insert,
//     left shift to delete) driven by ONE shared threshold compare.
//   - A shot is first *scanned* on the old ring (the new bead is virtual,
//     it sits between old index pos and pos+1).  Because every cascade level
//     only extends the eliminated interval outward, the union of all levels
//     is one contiguous (cyclic) interval.  So we only keep walking outwards
//     level by level and delete the whole interval ONCE at the end.
//   - Deletion runs in the background while the results are streamed out.
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
localparam S_IDLE  = 3'd0;   // wait for a shot / loading
localparam S_START = 3'd1;   // start a shot that arrived while deleting
localparam S_SCAN  = 3'd2;   // walk outwards from the junction
localparam S_CMT   = 3'd3;   // commit one cascade level
localparam S_INSN  = 3'd4;   // no elimination : insert the shot bead
localparam S_APP0  = 3'd5;   // empty ring : shot bead becomes index 0
localparam S_DEL   = 3'd6;   // delete the eliminated interval

localparam LV_DEPTH = 86;    // max cascade levels (>= 3 beads each, <= 256)

//---------------------------------------------------------------------
//   REG & WIRE DECLARATION
//---------------------------------------------------------------------
reg  [2:0]  state;
reg         in_valid_r;
reg  [2:0]  in_color_r;
reg         loading;
reg         pend;

reg  [2:0]  ring [0:255];
reg  [8:0]  M;               // beads in the ring (old coordinates while scanning)

reg  [2:0]  col_r;           // saved shot
reg  [7:0]  pos_r;

reg  [2:0]  c;               // color of the level being scanned
reg  [7:0]  lidx, ridx;      // scan pointers (old coordinates)
reg  [8:0]  L, R;            // beads taken on each side in this level
reg         ldone, rdone;
reg         lvl1;            // first level : the shot bead is virtual
reg  [8:0]  avail;           // beads not yet eliminated
reg  [7:0]  dst;             // leftmost eliminated bead (old coordinates)
reg  [6:0]  chain;           // levels committed

reg  [7:0]  sst;             // shift start of the deletion
reg  [8:0]  shifts;          // beads still to shift out

reg         out_act;
reg  [6:0]  out_rem;

reg  [2:0]  lv_col [0:LV_DEPTH-1];
reg  [8:0]  lv_cnt [0:LV_DEPTH-1];

integer i, j;

//---------------------------------------------------------------------
//   SCAN DATAPATH
//---------------------------------------------------------------------
wire [8:0] Mm1_9 = M - 9'd1;
wire [7:0] Mm1   = Mm1_9[7:0];

wire [2:0] ringL = ring[lidx];
wire [2:0] ringR = ring[ridx];

wire [7:0] l_dec = (lidx == 8'd0) ? Mm1 : (lidx - 8'd1);
wire [7:0] r_inc = (ridx == Mm1)  ? 8'd0 : (ridx + 8'd1);

wire [8:0] LR     = L + R;
wire       lmatch = !ldone && (ringL == c);
wire       rmatch = !rdone && (ringR == c);
wire       lext   = lmatch && (LR < avail);
wire       rext   = rmatch && ((LR + {8'd0, lext}) < avail);
wire [8:0] L_n    = L + {8'd0, lext};
wire [8:0] R_n    = R + {8'd0, rext};
wire       ldone_n = ldone | ~lext;
wire       rdone_n = rdone | ~rext;
wire       scan_fin = ldone_n & rdone_n;
wire [8:0] len_n  = L_n + R_n + {8'd0, lvl1};
wire       len_ge3 = (len_n >= 9'd3);

// commit stage
wire [8:0] len_c   = LR + {8'd0, lvl1};
wire [8:0] avail_n = avail - LR;
wire [7:0] dst_n   = (lidx == Mm1) ? 8'd0 : (lidx + 8'd1);
wire [6:0] chain_c = chain + 7'd1;
wire       cont    = (avail_n >= 9'd3) && (ringL == ringR);

//---------------------------------------------------------------------
//   TERMINATION / DELETE PARAMETERS (one shared unit)
//---------------------------------------------------------------------
wire noelim   = (state == S_SCAN) && scan_fin && !len_ge3 && lvl1;
wire scan_bad = (state == S_SCAN) && scan_fin && !len_ge3 && !lvl1;
wire term_cmt = (state == S_CMT)  && !cont;
wire del_go   = term_cmt | scan_bad;

wire [7:0] dst_x  = (state == S_CMT) ? dst_n   : dst;
wire [8:0] av_x   = (state == S_CMT) ? avail_n : avail;
wire [8:0] dcnt_x = M - av_x;
wire [9:0] dend   = {2'b00, dst_x} + {1'b0, dcnt_x};
wire       wrap_x = (dend > {1'b0, M});
wire       all_x  = (av_x == 9'd0);
wire [8:0] sh_x   = dend[8:0] - M;

//---------------------------------------------------------------------
//   RING STORAGE : insert / delete share one threshold
//---------------------------------------------------------------------
wire go_idle  = (state == S_IDLE) && shot_valid;
wire go_start = (state == S_START);
wire go_any   = (go_idle | go_start) & ~in_valid_r;
wire [2:0] g_col = go_start ? col_r : shot_color;
wire [7:0] g_pos = go_start ? pos_r : shot_pos;
wire [8:0] g_p1  = {1'b0, g_pos} + 9'd1;

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

always @(posedge clk) begin
    for (i = 0; i < 256; i = i + 1) begin
        if (ins_op) begin
            if (i == thr)       ring[i] <= wdata;
            else if (i > thr)   ring[i] <= ring[(i == 0) ? 0 : i - 1];
        end
        else if (shl) begin
            if (i >= thr)
                ring[i] <= k2 ? ring[(i + 2 > 255) ? 255 : i + 2]
                              : ring[(i + 1 > 255) ? 255 : i + 1];
        end
    end
end

//---------------------------------------------------------------------
//   LEVEL STORAGE (shift register, fixed read taps lv[0] / lv[1])
//---------------------------------------------------------------------
always @(posedge clk) begin
    if (state == S_CMT) begin
        lv_col[chain] <= c;
        lv_cnt[chain] <= len_c;
    end
    else if (out_act && out_rem != 7'd0) begin
        for (j = 0; j < LV_DEPTH - 1; j = j + 1) begin
            lv_col[j] <= lv_col[j + 1];
            lv_cnt[j] <= lv_cnt[j + 1];
        end
    end
end

//---------------------------------------------------------------------
//   OUTPUT START
//---------------------------------------------------------------------
wire       empty_go = go_any && (M == 9'd0);
wire       out_go   = noelim | term_cmt | scan_bad | empty_go;
wire [6:0] cf       = term_cmt ? chain_c : (scan_bad ? chain : 7'd0);
wire       use_cur  = term_cmt && (chain == 7'd0);
wire       use_lv0  = (term_cmt && (chain != 7'd0)) || scan_bad;
wire [2:0] fb_col   = use_cur ? c     : (use_lv0 ? lv_col[0] : 3'd0);
wire [8:0] fb_cnt   = use_cur ? len_c : (use_lv0 ? lv_cnt[0] : 9'd0);

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
        L          <= 9'd0;
        R          <= 9'd0;
        ldone      <= 1'b0;
        rdone      <= 1'b0;
        lvl1       <= 1'b0;
        avail      <= 9'd0;
        dst        <= 8'd0;
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
                elim_cnt   <= lv_cnt[1];
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
                            c     <= g_col;
                            lidx  <= g_pos;
                            ridx  <= (g_p1 == M) ? 8'd0 : g_p1[7:0];
                            L     <= 9'd0;
                            R     <= 9'd0;
                            ldone <= 1'b0;
                            rdone <= 1'b0;
                            lvl1  <= 1'b1;
                            avail <= M;
                            chain <= 7'd0;
                            state <= S_SCAN;
                        end
                    end
                end
                //-----------------------------------------------------
                S_SCAN: begin
                    L     <= L_n;
                    R     <= R_n;
                    ldone <= ldone_n;
                    rdone <= rdone_n;
                    if (lext) lidx <= l_dec;
                    if (rext) ridx <= r_inc;
                    if (scan_fin) begin
                        if (len_ge3)   state <= S_CMT;
                        else if (lvl1) state <= S_INSN;
                    end
                end
                //-----------------------------------------------------
                S_CMT: begin
                    chain <= chain_c;
                    avail <= avail_n;
                    dst   <= dst_n;
                    if (cont) begin
                        c     <= ringL;
                        L     <= 9'd1;
                        R     <= 9'd1;
                        lidx  <= l_dec;
                        ridx  <= r_inc;
                        ldone <= 1'b0;
                        rdone <= 1'b0;
                        lvl1  <= 1'b0;
                        state <= S_SCAN;
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

            // ---- eliminated interval is final : set up the deletion ----
            if (del_go) begin
                if (all_x) begin
                    M     <= 9'd0;
                    state <= S_IDLE;
                end
                else begin
                    M      <= wrap_x ? {1'b0, dst_x} : M;
                    sst    <= wrap_x ? 8'd0 : dst_x;
                    shifts <= wrap_x ? sh_x : dcnt_x;
                    state  <= S_DEL;
                end
            end

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
