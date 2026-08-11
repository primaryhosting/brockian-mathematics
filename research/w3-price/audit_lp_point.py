"""Audit an LP optimal point against the EXACT cone (t-grid may leave slack):
recompute S_O, S_PT, X from the returned vector and report the exact-CS
residual; if the point is pair-free (p ~ 0) also audit the repaired point
(p := 0, X := 0), which satisfies the exact cone trivially."""
import numpy as np
from ladder import build, solve_level, MMAX

def audit(flags, label, **kw):
    out = solve_level(flags, label, dual=False, **kw)
    if out["value"] is None:
        return
    c, Aub, bub, Aeq, beq, lb, ub, meta = build(flags, **{k: v for k, v in kw.items() if k in ("DMAX", "tol")})
    x = out["x"]; iX, nA, na = meta["iX"], meta["nA"], meta["na"]
    # reconstruct SO/SPT via the rows used in build: SO>=0 rows are -SO_row
    so = np.zeros(nA); spt = np.zeros(nA)
    k = 0
    for kk, t in enumerate(meta["tags"]):
        if t[0] == "SO>=0":
            so[k] = -(Aub[kk] @ x)
        if t[0] == "SPT>=0":
            spt[k] = -(Aub[kk] @ x); k += 1
    xv = x[iX:iX + nA]
    cs = np.abs(xv) - 2 * np.sqrt(np.maximum(so, 0) * np.maximum(spt, 0))
    i = int(np.argmax(cs))
    print(f"   exact-CS residual of LP point: max = {cs.max():+.3e} at a-index {i}"
          f"  (<=0 means the LP witness IS exact-cone feasible)")
    p = x[meta['iP']:meta['iE']]
    print(f"   sum p = {p.sum():.2e}; max|X| = {np.abs(xv).max():.3e}")

audit({"I5"}, "audit L1B")
