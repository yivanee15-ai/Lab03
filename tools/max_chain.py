#!/usr/bin/env python3
"""Replay an input.txt with a golden ZUMA model and report the statistics that matter
for sizing the design: deepest cascade, largest ring, how many shots eliminate.

usage: python3 max_chain.py [path/to/input.txt]
"""
import sys

path = sys.argv[1] if len(sys.argv) > 1 else "../00_TESTBED/input.txt"
tok = open(path).read().split()
pos = 0
def nxt():
    global pos
    v = int(tok[pos]); pos += 1
    return v

games = nxt()
max_chain = max_ring = shots = elim_shots = whole = 0
hist = {}
for _ in range(games):
    ring_len, shot_num = nxt(), nxt()
    ring = [nxt() for _ in range(ring_len)]
    max_ring = max(max_ring, len(ring))
    for _ in range(shot_num):
        color, p = nxt(), nxt()
        shots += 1
        if not ring:
            ring = [color]
            hist[0] = hist.get(0, 0) + 1
            continue
        ring.insert(p + 1, color)
        max_ring = max(max_ring, len(ring))
        q, chain = p + 1, 0
        while True:
            M = len(ring); c = ring[q]; L = R = 0
            while L + R + 1 < M and ring[(q - L - 1) % M] == c: L += 1
            while L + R + 1 < M and ring[(q + R + 1) % M] == c: R += 1
            n = L + R + 1
            if n < 3: break
            chain += 1
            if n == M: whole += 1
            st = (q - L) % M
            idx = {(st + k) % M for k in range(n)}
            if 0 in idx:
                e = (st + n - 1) % M
                ring = [ring[(e + k) % M] for k in range(1, M - n + 1)]; nb = 0
            else:
                nb = st % (M - n) if M - n > 0 else 0
                ring = [x for i, x in enumerate(ring) if i not in idx]
            if len(ring) < 3: break
            na = (nb - 1) % len(ring)
            if ring[na] == ring[nb]: q = na
            else: break
        hist[chain] = hist.get(chain, 0) + 1
        max_ring = max(max_ring, len(ring))
        if chain: elim_shots += 1
        max_chain = max(max_chain, chain)

print(f"games={games} shots={shots} shots_with_elimination={elim_shots} whole_ring_clears={whole}")
print(f"max_chain_num={max_chain}  max_ring_size={max_ring}")
print("chain_num histogram:", dict(sorted(hist.items())))
