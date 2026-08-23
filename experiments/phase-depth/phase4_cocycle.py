"""
Phase 4 — canonical arithmetic phase-depth cocycle + discrimination test.

Construction (NO tunable weights — everything determined by the prime sequence):
  - Primes p>5 have residues r_n = p_n mod 5 in {1,2,3,4} (units).
  - Pentagon phase-depth: walk the residue cycle in windows of 5 consecutive primes.
    Window k = (r_{5k}, ..., r_{5k+4}). The roof is the actual residue:
        c_k(j) = r_{5k+j}  (as an element of ZMod 5).
    Canonical holonomy H_k = sum_{j=0..4} c_k(j)  (mod 5)  = total depth of window k.
  - Also a richer 'depth' cocycle: d_k = number of consecutive REPEATS within the window
    (r_{5k+j+1} == r_{5k+j}), the phase-depth accumulation. (Lemke Oliver–Soundararajan
    predicts repeats are SUPPRESSED — a real arithmetic correlation.)

Discrimination test (the three Phase-4 questions):
  (1) Does the holonomy distribution deviate from a residue-statistics-matched null?
      NULL-A = i.i.d. residues with the observed marginal.
      NULL-B = 1-step Markov with the observed transition matrix (matches ALL pairwise
               residue statistics). If holonomy still deviates from NULL-B, it sees beyond
               first-order (Fourier/transition) statistics.
  (2) Stability under symmetry (reverse the window order — orientation).
  (3) Correlation with a meaningful quantity (the L-O-S consecutive-residue bias).

Reported honestly: chi-square vs each null, effect sizes, verdict.
"""
import numpy as np

def sieve(n):
    s = np.ones(n+1, dtype=bool); s[:2]=False
    for i in range(2, int(n**0.5)+1):
        if s[i]: s[i*i::i]=False
    return np.nonzero(s)[0]

N = 50_000_000
primes = sieve(N)
primes = primes[primes>5]
r = (primes % 5).astype(np.int8)           # residues in {1,2,3,4}
M = len(r)
print(f"primes in (5,{N}]: {M:,}")
print("marginal residue counts mod 5:", {int(k):int((r==k).sum()) for k in (1,2,3,4)})

# observed 1-step transition matrix on {1,2,3,4}
idx = {1:0,2:1,3:2,4:3}
T = np.zeros((4,4))
a = np.array([idx[x] for x in r[:-1]]); b = np.array([idx[x] for x in r[1:]])
for i in range(4):
    row = b[a==i]
    for j in range(4):
        T[i,j] = (row==j).mean()
np.set_printoptions(precision=4, suppress=True)
print("observed transition matrix P(r_{n+1}=col | r_n=row), rows/cols=1,2,3,4:")
print(T)
# L-O-S signature: diagonal (repeats) suppressed below 1/4?
print("diagonal (repeat) probs:", T.diagonal(), " -- uniform would be 0.25")
