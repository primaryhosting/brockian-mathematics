"""W2 (wave-2, exact-cone psi_1 question): closed-form witness -> VERDICT (A).

CLASS (named, per method law #3): the "exact-cone 2-level relaxation with band
data B (S_total(alpha) = alpha on [0,1], T1 delta_0 bookkeeping, tol >= 0) and
Bochner window A" -- exactly the model of research/t1-ceiling/lp_cone.py and
refB/cone_socp.py: species fractions psi_m (m = 1..5), off-line pair masses
p_y (y in {0.1,...,0.5}), FREE on-line correlation density eta >= -1
(cells + tails, NOT tied to psi -- that untying IS the 2-level relaxation),
per-alpha variables S_O >= 0, S_P >= 0, X with the EXACT second-order cone
|X| <= 2 sqrt(S_O S_P), band equalities on [0,1], S_total >= 0 on (1, A].

REDUCTION (algebra, machine-checked below): in-band, eliminating X via the
band equality, the cone constraint X^2 <= 4 S_O S_P is EQUIVALENT to
    h(a) := 4 S_O S_P - (a - S_O - S_P)^2
          = 2a (S_O + S_P) - a^2 - (S_P - S_O)^2  >=  0.
Out of band the choice X = 0 satisfies both |X| <= 2 sqrt(S_O S_P) and
S_total = S_O + S_P >= 0, so the out-of-band rows bind only through S_O >= 0.

WITNESS (psi == 0 identically -- a fortiori psi_1 = 0):
    psi_m = 0 for all m;   p_{0.1} = 1/2, other p_y = 0   [count 2*(1/2) = 1]
    eta = 50 on the first cell [0, 0.02), 0 elsewhere; tails = 0
          (measure form: nu = dx + Uniform([0, 0.02], total mass 1))
    S_O(a) = 50 sin(0.04 pi a) / (pi a) = 2 sinc(0.04 a),  sinc(t)=sin(pi t)/(pi t)
    S_P(a) = 2 cosh^2(0.2 pi a)
    X(a)   = a - S_O(a) - S_P(a)  on [0,1];   X(a) = 0  for a > 1.

FEASIBILITY PROOF (continuum, tol = 0; every numeric constant checked below):
  band equality: exact by construction.  S_O, S_P > 0 on [0, 25] (sinc arg
  0.04a <= 1).  Cone: with D := S_P - S_O = 2 sinh^2(0.2 pi a) + 2(1 - sinc(0.04 a)),
    (i)  sinh(u) <= 1.2040 u  for u in [0, 0.2 pi]      -> 2 sinh^2 <= 1.1450 a^2
    (ii) 1 - sinc(t) <= (pi t)^2 / 6                    -> 2(1-sinc) <= 0.0053 a^2
    so D <= 1.1503 a^2 on [0,1]; and S_O + S_P >= 2 sinc(0.04) + 2 >= 3.9947; hence
    h(a) >= a (2*3.9947 - 1 - 1.1503^2) >= 5.67 a > 0   on (0, 1],
  and h(0) = 0 with X(0) = -4 = -2 sqrt(S_O(0) S_P(0)): the CLOSED cone's
  boundary -- feasible.  The analytic worst-alpha is exactly a = 0, residual
  exactly 0; for a > 0 the point is STRICTLY inside the cone (margin >= 5.67a).

CONSEQUENCE: min psi_1 over the exact-cone 2-level relaxation class = 0
(it cannot be < 0), at EVERY alpha-grid (each grid model is a relaxation of
the continuum model, and 0 <= grid-min <= continuum-min = 0), every tol >= 0,
every Bochner window A <= 25 in this cell basis (Gaussian-hump variant below:
EVERY A).  Prop 4.4(i) at the witness: LHS = 3 psi_1 + 4(sum psi_{>=2} + p)
= 2 < RHS = 4 - 1/c1* = 2.6725007 -- the preprint's rank-trace / inertia
certificate strictly exceeds this ENTIRE relaxation class.
"""
import sys
import numpy as np

T1 = "/Users/acutis/Projects/brockian-mathematics/research/t1-ceiling"
REFB = ("/private/tmp/claude-501/-Users-acutis/"
        "c091f518-344b-4ffd-9c26-4ece8180125a/scratchpad/refB")
sys.path.insert(0, T1)
sys.path.insert(0, REFB)

W = 0.02          # hump support = first cell of make_cells (exact)
ETA1 = 50.0       # density: mass 1 on [0, 0.02)
Y = 0.1           # pair depth used (first entry of the class's depth profile)
PMASS = 0.5       # p_{0.1}; count = 2 * 0.5 = 1


def sinc(t):
    t = np.asarray(t, dtype=float)
    out = np.ones_like(t)
    nz = np.abs(t) > 0
    out[nz] = np.sin(np.pi * t[nz]) / (np.pi * t[nz])
    return out


def S_O(a):
    return 2.0 * sinc(0.04 * np.asarray(a, dtype=float))


def S_P(a):
    return 2.0 * np.cosh(0.2 * np.pi * np.asarray(a, dtype=float)) ** 2


def X_in(a):
    a = np.asarray(a, dtype=float)
    return a - S_O(a) - S_P(a)


def h(a):
    so, sp = S_O(a), S_P(a)
    return 4.0 * so * sp - (np.asarray(a) - so - sp) ** 2


def check_analytic_chain():
    """Machine-verify every constant used in the hand proof."""
    print("== analytic-chain constant checks (dense grids) ==")
    u = np.linspace(1e-9, 0.2 * np.pi, 2_000_001)
    r1 = np.max(np.sinh(u) / u)
    assert r1 <= 1.2040, r1                      # sinh(u) <= 1.2040 u on [0, .2pi]
    # avoid catastrophic cancellation below t ~ 1e-3 (1 - sinc ~ 1e-19 there);
    # the ratio is increasing on (0, 0.04] (checked), so sup is at the right end
    t = np.linspace(1e-3, 0.04, 1_000_001)
    ratio2 = (1.0 - sinc(t)) / (np.pi * t) ** 2
    assert np.all(np.diff(ratio2) > -1e-9)       # increasing on [1e-3, 0.04]
    r2 = ratio2.max()
    assert r2 <= 1.0 / 6.0 + 1e-12, r2           # 1 - sinc(t) <= (pi t)^2 / 6
    a = np.linspace(1e-6, 1.0, 2_000_001)
    D = S_P(a) - S_O(a)
    r3 = np.max(D / a ** 2)
    assert r3 <= 1.1503, r3                      # D <= 1.1503 a^2 on [0,1]
    somin = 2.0 * sinc(np.array([0.04]))[0]
    assert somin + 2.0 >= 3.9947                 # S_O + S_P >= 3.9947 on [0,1]
    margin = 2 * 3.9947 - 1.0 - 1.1503 ** 2
    print(f"  sup sinh(u)/u          = {r1:.6f}  (<= 1.2040)")
    print(f"  sup (1-sinc)/(pi t)^2  = {r2:.6f}  (<= 1/6)")
    print(f"  sup D/a^2 on (0,1]     = {r3:.6f}  (<= 1.1503)")
    print(f"  min S_O + S_P on [0,1] = {somin + 2.0:.6f} (>= 3.9947)")
    print(f"  => h(a) >= {margin:.4f} * a on (0,1]  (proof margin)")
    return margin


def check_dense_grid():
    print("\n== dense continuum grid checks ==")
    # band [0,1]: 2,000,001 points
    a = np.linspace(0.0, 1.0, 2_000_001)
    so, sp = S_O(a), S_P(a)
    x = a - so - sp
    resid = np.abs(x) - 2.0 * np.sqrt(so * sp)   # exact-CS residual (<= 0 req.)
    hv = 4 * so * sp - x ** 2
    print(f"  band grid: 2,000,001 pts on [0,1]")
    print(f"  max exact-CS residual |X| - 2 sqrt(SO SP) = {resid.max():+.3e} "
          f"(at a = {a[np.argmax(resid)]:.6f})")
    print(f"  residual at a=0 (analytic worst-alpha)    = {resid[0]:+.3e} "
          f"(cone boundary, exact)")
    hn0 = hv[1:] / a[1:]
    print(f"  min h(a)/a over grid a>0 = {hn0.min():.4f} "
          f"(proof guarantees >= 5.67)")
    print(f"  band equality residual = 0 by construction (X := a - SO - SP)")
    assert resid.max() <= 1e-12
    # out of band up to A = 25 (cell-basis validity limit), X = 0
    ao = np.linspace(1.0, 25.0, 1_000_001)
    soo = S_O(ao)
    print(f"  out-of-band [1,25]: min S_O = {soo.min():.6f} (>= 0 required), "
          f"S_total = S_O + S_P > 0 with X = 0; cone: |0| <= 2 sqrt(SO SP). OK")
    assert soo.min() >= 0.0


def check_referee_matrices(XF=80.0, na=600, tol=2e-4, Aboch=3.0, nb=320):
    """Plug the witness into refB/cone_socp.build's exact constraint matrices
    -- the referee's own probe model (default: the probe discretization)."""
    print(f"\n== referee-model matrix check (cone_socp.build, XF={XF:g} "
          f"na={na} A={Aboch:g} nb={nb} tol={tol:g}) ==")
    from cone_socp import build
    from lp_primal3 import MMAX
    c, A_ub, b_ub, A_eq, b_eq, bounds, idx, aa = build(
        XF=XF, na=na, tol=tol, Aboch=Aboch, nb=nb)
    n, nA = idx["n"], idx["nA"]
    iSO, iSP, iX, iP, iE = idx["iSO"], idx["iSP"], idx["iX"], idx["iP"], idx["iE"]
    x = np.zeros(n)
    x[iP] = PMASS                    # p_{0.1} = 1/2 ; psi stays 0
    x[iE] = ETA1                     # first cell [0, 0.02) density 50
    so = S_O(aa); sp = S_P(aa)
    xv = np.where(np.arange(nA) < na, aa - so - sp, 0.0)
    x[iSO:iSO + nA] = so
    x[iSP:iSP + nA] = sp
    x[iX:iX + nA] = xv
    # NOTE: S_A rows compute SO from eta via cell_cols; our closed form is the
    # same expression -- residual must be float-level only.
    req = A_eq @ x - b_eq
    rub = A_ub @ x - b_ub
    print(f"  max |A_eq x - b_eq|        = {np.abs(req).max():.3e}")
    print(f"  max (A_ub x - b_ub)        = {rub.max():+.3e}  (must be <= 0 "
          f"within float; includes band tol, Bochner, t-grid cone, tail budget)")
    lo_ok = all(x[i] >= (b[0] if b[0] is not None else -np.inf) - 1e-15
                for i, b in enumerate(bounds))
    print(f"  variable bounds respected  = {lo_ok}")
    resid = np.abs(xv) - 2.0 * np.sqrt(so * sp)
    print(f"  EXACT-CS residual on the model's {nA}-pt grid: "
          f"max = {resid.max():+.3e}, #(> 1e-9) = {(resid > 1e-9).sum()}")
    print(f"  psi = {x[:MMAX]},  p = {x[iP:iE]},  count = "
          f"{np.dot(np.arange(1, MMAX+1), x[:MMAX]) + 2*x[iP:iE].sum():.6f}")
    assert np.abs(req).max() < 1e-9
    assert rub.max() <= 1e-12
    assert resid.max() <= 1e-12


def check_prop44():
    print("\n== Prop 4.4(i) comparison (rank-trace certificate vs the class) ==")
    c1 = 2 * np.tan(1 / np.sqrt(2)) / (np.sqrt(2) + np.tan(1 / np.sqrt(2)))
    RHS = 4.0 - 1.0 / c1
    LHS = 3 * 0.0 + 4 * (0.0 + PMASS)
    print(f"  c1* = {c1:.7f}   (calibration: 0.7532961)")
    print(f"  witness LHS = 3 psi_1 + 4(sum psi_m>=2 + sum p) = {LHS:.7f}")
    print(f"  RHS = 4 - 1/c1* = {RHS:.7f}")
    print(f"  Prop 4.4(i) violation by the witness = {RHS - LHS:+.7f} "
          f"( = 2 - 1/c1* = V_A, by algebra)")


def check_gaussian_variant():
    """Any-window variant: replace the cell hump by a Gaussian hump
    nu = dx + N(0, s) mass 1, s = 0.05: S_O(a) = 2 exp(-pi (0.05 a)^2) > 0 for
    ALL a, so the witness is feasible for EVERY Bochner window A."""
    print("\n== Gaussian-hump variant (feasible for EVERY Bochner window A) ==")
    s = 0.05
    a = np.linspace(0.0, 1.0, 2_000_001)
    so = 2.0 * np.exp(-np.pi * (s * a) ** 2)
    sp = S_P(a)
    x = a - so - sp
    resid = np.abs(x) - 2.0 * np.sqrt(so * sp)
    hv = 4 * so * sp - x ** 2
    print(f"  max exact-CS residual on [0,1] = {resid.max():+.3e}; "
          f"min h/a (a>0) = {(hv[1:]/a[1:]).min():.4f}")
    print(f"  S_O(a) = 2 exp(-pi (0.05 a)^2) > 0 for all a in R: out-of-band "
          f"S_O >= 0 holds for every window A")
    assert resid.max() <= 1e-12


if __name__ == "__main__":
    m = check_analytic_chain()
    check_dense_grid()
    check_referee_matrices()                                   # probe grid
    check_referee_matrices(XF=160.0, na=1200, Aboch=5.0, nb=1280)  # finer grid
    check_prop44()
    check_gaussian_variant()
    print("\nVERDICT (A): psi_1 = 0 (indeed psi == 0) is EXACTLY feasible in "
          "the exact-cone 2-level relaxation class; min psi_1 = 0 exactly, "
          "grid-independently.")
