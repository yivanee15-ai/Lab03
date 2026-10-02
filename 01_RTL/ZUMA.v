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
localparam S_PRE   = 3'd7;   // compute the delete parameters

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
reg  [8:0]  lenc;            // length of the run found so far (incl. virtual bead)
reg  [8:0]  room;            // beads still available to this level
reg         ldone, rdone;
reg         lvl1;            // first level : the shot bead is virtual
reg  [8:0]  dcnt;            // old beads eliminated so far (committed levels only)
reg  [8:0]  tail;            // M - dst : beads from dst to the end of the ring
reg         allf;            // committed levels already cover the whole ring
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

wire       lmatch = !ldone && (ringL == c);
wire       rmatch = !rdone && (ringR == c);
wire       room_nz  = |room;
wire       room_ge2 = |room[8:1];
wire       lext   = lmatch && room_nz;
wire       rext   = rmatch && (lext ? room_ge2 : room_nz);
wire [1:0] ext_n  = {lext & rext, lext ^ rext};
wire [8:0] lenc_n = lenc + {7'd0, ext_n};
wire [8:0] room_n = room - {7'd0, ext_n};
wire       ldone_n = ldone | ~lext;
wire       rdone_n = rdone | ~rext;
wire       scan_fin = ldone_n & rdone_n;
wire       len_ge3 = (|lenc[8:2]) | (&lenc[1:0]) |
                     ((lenc[1:0] == 2'd2) & (lext | rext)) |
                     ((lenc[1:0] == 2'd1) & lext & rext);

// commit stage
wire [7:0] dst_n   = (lidx == Mm1) ? 8'd0 : (lidx + 8'd1);
wire [6:0] chain_c = chain + 7'd1;
wire       cont    = (room >= 9'd3) && (ringL == ringR);

//---------------------------------------------------------------------
//   TERMINATION / DELETE PARAMETERS (computed from registers in S_PRE)
//---------------------------------------------------------------------
wire noelim   = (state == S_SCAN) && scan_fin && !len_ge3 && lvl1;
wire scan_bad = (state == S_SCAN) && scan_fin && !len_ge3 && !lvl1;
wire term_cmt = (state == S_CMT)  && !cont;

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
        lv_cnt[chain] <= lenc;
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
wire [8:0] fb_cnt   = use_cur ? lenc : (use_lv0 ? lv_cnt[0] : 9'd0);

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
        dcnt       <= 9'd0;
        tail       <= 9'd0;
        allf       <= 1'b0;
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
                            lenc  <= 9'd1;
                            room  <= M;
                            ldone <= 1'b0;
                            rdone <= 1'b0;
                            lvl1  <= 1'b1;
                            chain <= 7'd0;
                            state <= S_SCAN;
                        end
                    end
                end
                //-----------------------------------------------------
                S_SCAN: begin
                    lenc  <= lenc_n;
                    room  <= room_n;
                    ldone <= ldone_n;
                    rdone <= rdone_n;
                    if (lext) lidx <= l_dec;
                    if (rext) ridx <= r_inc;
                    if (scan_fin) begin
                        if (len_ge3)   state <= S_CMT;
                        else if (lvl1) state <= S_INSN;
                        else           state <= S_PRE;
                    end
                end
                //-----------------------------------------------------
                S_CMT: begin
                    chain <= chain_c;
                    dcnt  <= M - room;
                    tail  <= M - {1'b0, dst_n};
                    allf  <= (room == 9'd0);
                    dst   <= dst_n;
                    if (cont) begin
                        c     <= ringL;
                        lenc  <= 9'd2;
                        room  <= room - 9'd2;
                        lidx  <= l_dec;
                        ridx  <= r_inc;
                        ldone <= 1'b0;
                        rdone <= 1'b0;
                        lvl1  <= 1'b0;
                        state <= S_SCAN;
                    end
                    else state <= S_PRE;
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
