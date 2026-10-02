/**************************************************************************/
// MODULE: ZUMA
// FILE NAME: ZUMA.v
// DESCRIPTION: 2026 Fall IC Lab / Exercise Lab03 / ZUMA
//
// Architecture:
//   - The ring is stored as a 256-entry register array in logical order
//     (index 0 = logical index 0).  A segment that wraps around M-1 -> 0 is
//     removed as "tail part truncated + head part shifted out", which keeps
//     the logical-index rule (first survivor after the segment becomes 0).
//   - Per shot:  INS (parallel insert) -> SCAN (walk left/right from the new
//     bead, one bead per side per cycle) -> DEC (record level, locate segment)
//     -> DEL (shift-left one bead per cycle) -> CHK (compare the two new
//     neighbours, rescan if they have the same color) -> ... -> OUT.
//   - Every level is stored, then chain_num is reported with all levels.
/**************************************************************************/

module ZUMA (
    // Input
    clk,
    rst_n,
    in_valid,
    ring_len,
    in_color,
    shot_valid,
    shot_color,
    shot_pos,
    // Output
    out_valid,
    chain_num,
    elim_color,
    elim_cnt
);

//---------------------------------------------------------------------
//   PORT DECLARATION
//---------------------------------------------------------------------
input             clk;
input             rst_n;
input             in_valid;
input      [7:0]  ring_len;
input      [2:0]  in_color;
input             shot_valid;
input      [2:0]  shot_color;
input      [7:0]  shot_pos;

output reg        out_valid;
output reg [6:0]  chain_num;
output reg [2:0]  elim_color;
output reg [8:0]  elim_cnt;

//---------------------------------------------------------------------
//   PARAMETER
//---------------------------------------------------------------------
localparam S_IDLE = 3'd0;
localparam S_INS  = 3'd1;
localparam S_SCAN = 3'd2;
localparam S_DEC  = 3'd3;
localparam S_DEL  = 3'd4;
localparam S_CHK  = 3'd5;
localparam S_OUT0 = 3'd6;
localparam S_OUT1 = 3'd7;

localparam OP_NOP = 2'd0;
localparam OP_APP = 2'd1;
localparam OP_INS = 2'd2;
localparam OP_SHL = 2'd3;

//---------------------------------------------------------------------
//   REG & WIRE DECLARATION
//---------------------------------------------------------------------
reg [2:0]  state;
reg        loading;

reg [2:0]  ring [0:255];
reg [8:0]  M;                // number of beads in the ring

reg [2:0]  col_r;            // latched shot color
reg [7:0]  pos_r;            // latched shot position

reg [2:0]  c;                // color of the segment being scanned
reg [8:0]  lidx, ridx;       // left / right scan pointers
reg [8:0]  L, R;             // number of extra beads found on each side
reg        ldone, rdone;

reg [8:0]  sst;              // shift start index for deletion
reg [8:0]  rem_cnt;          // beads still to be shifted out

reg [6:0]  chain;            // number of levels recorded
reg [6:0]  oidx;
reg [2:0]  lvl_col [0:95];
reg [8:0]  lvl_cnt [0:95];

integer i;

//---------------------------------------------------------------------
//   COMBINATIONAL
//---------------------------------------------------------------------
wire [2:0] ringL = ring[lidx[7:0]];
wire [2:0] ringR = ring[ridx[7:0]];

wire       lmatch = !ldone && (ringL == c);
wire       rmatch = !rdone && (ringR == c);
wire [8:0] tot    = L + R + 9'd1;
wire       lext   = lmatch && (tot < M);
wire       rext   = rmatch && ((tot + {8'd0, lext}) < M);
wire       ldone_n = ldone | ~lext;
wire       rdone_n = rdone | ~rext;

wire [8:0] seg_len = L + R + 9'd1;
wire [8:0] seg_st  = (lidx == M - 9'd1) ? 9'd0 : (lidx + 9'd1);
wire       seg_wrap = ((seg_st + seg_len) > M);
wire [8:0] new_M_d  = M - 9'd1;                         // value of M after this DEL shift
wire [8:0] nb_idx   = (sst == new_M_d) ? 9'd0 : sst;
wire [8:0] na_idx   = (nb_idx == 9'd0) ? (new_M_d - 9'd1) : (nb_idx - 9'd1);

// ring write control
wire       app_en = (state == S_IDLE) && (in_valid || (shot_valid && (M == 9'd0)));
wire [8:0] widx   = (in_valid && loading) ? M : 9'd0;
wire [2:0] wdata  = in_valid ? in_color : shot_color;
wire [8:0] insidx = {1'b0, pos_r} + 9'd1;

reg  [1:0] ring_op;
always @(*) begin
    ring_op = OP_NOP;
    if (app_en)                              ring_op = OP_APP;
    else if (state == S_INS)                 ring_op = OP_INS;
    else if (state == S_DEL)                 ring_op = OP_SHL;
end

//---------------------------------------------------------------------
//   RING STORAGE (no reset needed, contents are only used within M)
//---------------------------------------------------------------------
always @(posedge clk) begin
    for (i = 0; i < 256; i = i + 1) begin
        case (ring_op)
            OP_APP: begin
                if (i == widx) ring[i] <= wdata;
            end
            OP_INS: begin
                if (i == insidx)      ring[i] <= col_r;
                else if (i > insidx)  ring[i] <= ring[(i == 0) ? 0 : i - 1];
            end
            OP_SHL: begin
                if (i >= sst && i < 255) ring[i] <= ring[i + 1];
            end
            default: ;
        endcase
    end
end

//---------------------------------------------------------------------
//   LEVEL STORAGE
//---------------------------------------------------------------------
always @(posedge clk) begin
    if (state == S_DEC && seg_len >= 9'd3) begin
        lvl_col[chain] <= c;
        lvl_cnt[chain] <= seg_len;
    end
end

//---------------------------------------------------------------------
//   CONTROL
//---------------------------------------------------------------------
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        state      <= S_IDLE;
        loading    <= 1'b0;
        M          <= 9'd0;
        col_r      <= 3'd0;
        pos_r      <= 8'd0;
        c          <= 3'd0;
        lidx       <= 9'd0;
        ridx       <= 9'd0;
        L          <= 9'd0;
        R          <= 9'd0;
        ldone      <= 1'b0;
        rdone      <= 1'b0;
        sst        <= 9'd0;
        rem_cnt    <= 9'd0;
        chain      <= 7'd0;
        oidx       <= 7'd0;
        out_valid  <= 1'b0;
        chain_num  <= 7'd0;
        elim_color <= 3'd0;
        elim_cnt   <= 9'd0;
    end
    else begin
        case (state)
            //---------------------------------------------------------
            S_IDLE: begin
                if (in_valid) begin
                    loading <= 1'b1;
                    M       <= loading ? (M + 9'd1) : 9'd1;
                end
                else begin
                    loading <= 1'b0;
                    if (shot_valid) begin
                        col_r <= shot_color;
                        pos_r <= shot_pos;
                        chain <= 7'd0;
                        oidx  <= 7'd0;
                        if (M == 9'd0) begin
                            M     <= 9'd1;
                            state <= S_OUT0;
                        end
                        else state <= S_INS;
                    end
                end
            end
            //---------------------------------------------------------
            S_INS: begin
                M     <= M + 9'd1;
                c     <= col_r;
                lidx  <= {1'b0, pos_r};
                ridx  <= (insidx == M) ? 9'd0 : (insidx + 9'd1);
                L     <= 9'd0;
                R     <= 9'd0;
                ldone <= 1'b0;
                rdone <= 1'b0;
                state <= S_SCAN;
            end
            //---------------------------------------------------------
            S_SCAN: begin
                if (lext) begin
                    L    <= L + 9'd1;
                    lidx <= (lidx == 9'd0) ? (M - 9'd1) : (lidx - 9'd1);
                end
                if (rext) begin
                    R    <= R + 9'd1;
                    ridx <= (ridx == M - 9'd1) ? 9'd0 : (ridx + 9'd1);
                end
                ldone <= ldone_n;
                rdone <= rdone_n;
                if (ldone_n && rdone_n) state <= S_DEC;
            end
            //---------------------------------------------------------
            S_DEC: begin
                if (seg_len < 9'd3) state <= S_OUT0;
                else begin
                    chain <= chain + 7'd1;
                    if (seg_wrap) begin
                        rem_cnt <= seg_len - (M - seg_st);
                        M       <= seg_st;
                        sst     <= 9'd0;
                    end
                    else begin
                        rem_cnt <= seg_len;
                        sst     <= seg_st;
                    end
                    state <= S_DEL;
                end
            end
            //---------------------------------------------------------
            S_DEL: begin
                M       <= M - 9'd1;
                rem_cnt <= rem_cnt - 9'd1;
                if (rem_cnt == 9'd1) begin
                    lidx  <= na_idx;
                    ridx  <= nb_idx;
                    state <= S_CHK;
                end
            end
            //---------------------------------------------------------
            S_CHK: begin
                if (M >= 9'd3 && ringL == ringR) begin
                    c     <= ringL;
                    lidx  <= (lidx == 9'd0) ? (M - 9'd1) : (lidx - 9'd1);
                    L     <= 9'd0;
                    R     <= 9'd0;
                    ldone <= 1'b0;
                    rdone <= 1'b0;
                    state <= S_SCAN;
                end
                else state <= S_OUT0;
            end
            //---------------------------------------------------------
            S_OUT0: begin
                out_valid  <= 1'b1;
                chain_num  <= chain;
                elim_color <= (chain == 7'd0) ? 3'd0 : lvl_col[0];
                elim_cnt   <= (chain == 7'd0) ? 9'd0 : lvl_cnt[0];
                oidx       <= 7'd1;
                state      <= S_OUT1;
            end
            //---------------------------------------------------------
            S_OUT1: begin
                if (oidx < chain) begin
                    elim_color <= lvl_col[oidx];
                    elim_cnt   <= lvl_cnt[oidx];
                    oidx       <= oidx + 7'd1;
                end
                else begin
                    out_valid  <= 1'b0;
                    chain_num  <= 7'd0;
                    elim_color <= 3'd0;
                    elim_cnt   <= 9'd0;
                    state      <= S_IDLE;
                end
            end
        endcase
    end
end

endmodule
