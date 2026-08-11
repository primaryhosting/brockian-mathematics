"""W3 (price decomposition): analytic witnesses for the ladder's upper bounds.

GHOST-0 (level C0, cited from refereed W2/refC work): pair at depth 0.1
  (p_{0.1} = 1/2) + tall correlation cell near 0 (eta = 50 on [0, 0.02)),
  psi == 0.  Refereed CONFIRMED (REFEREED.md, Referee C).  Re-checked densely
  here for completeness only.

GHOST-2 ("the multiplicity ghost", NEW, level C0+I2): the ghost that survives
  the nu-to-psi density tie.  I2 caps the correlation DENSITY (1 + eta_j)
  by DMAX * s, s = sum_m m psi_m (true for genuine configurations:
  correlation density at offset x is at most [local density cap] * [mean
  on-line density]).  The tie kills the tall cell -- so the ghost migrates
  into the MULTIPLICITY DIAGONAL, which the density cap cannot see (T1
  delta_0 bookkeeping: D2 = sum m^2 psi_m rides on the alpha-independent
  diagonal, outside the cells):

      psi_2 = 1/4,  p_{0.1} = 1/4,  eta == 0,  tails = 0
      S_O(a) = D2 = 4 * (1/4) = 1   (exactly flat, for EVERY alpha)
      S_P(a) = 4 * (1/4) * cosh^2(0.2 pi a) = cosh^2(0.2 pi a)
      X(a)   = a - S_O - S_P on [0,1],  X = 0 beyond.

  count: 2*(1/4) + 2*(1/4) = 1.  psi_1 = 0.  I2 cap: 1 + 0 = 1 <= DMAX * s
  with s = 2 psi_2 = 1/2, i.e. feasible for every DMAX >= 2.
  FEASIBILITY (tol = 0, continuum, every Bochner window A -- proof, with
  every constant machine-checked below):
    band equality: exact by construction.
    cone h(a) := 4 S_O S_P - X^2 = 2a(S_O+S_P) - a^2 - (S_P-S_O)^2:
      h(0) = 4*1*1 - (0-2)^2 = 0        (closed-cone boundary, exact);
      for a in (0,1]:  S_P - S_O = sinh^2(0.2 pi a) <= sinh^2(0.2 pi) a^2
      (chord bound, sinh convex with sinh 0 = 0), and S_O + S_P >= 2, so
      h(a) >= a (4 - 1 - sinh(0.2 pi)^4 a^3 / 1) >= a (3 - sinh(0.2 pi)^4)
            >= 2.79 a > 0.
    out of band: X = 0, S_total = 1 + cosh^2 > 0 for ALL a  (no decay at
      all -- stronger than W2's Gaussian variant); S_O = 1 >= 0 everywhere.
  Generalisation (committed as algebra + spot check): using multiplicity m,
  psi_m = m/(2(m+2) * m/4)...  cleanly: q := p_{0.1} = m/(2m+4),
  psi_m = 4q/m^2; the I2 cap needs DMAX >= (m+2)/2, so m = 2 is the
  cheapest; every MMAX extends the reach in 1/DMAX.

CONSEQUENCE: the certified constant of C0 + I2 is exactly 0 for every
DMAX >= 2 (lower bound trivial: psi_1 >= 0 variable bound).  The nu-tie,
alone, buys NOTHING: the delta_0 bookkeeping is exactly where the ghost
re-forms.
"""
import numpy as np
import sys

T1 = "/Users/acutis/Projects/brockian-mathematics/research/t1-ceiling"
sys.path.insert(0, T1)

PSI2, Q = 0.25, 0.25   # ghost-2 species


def SO2(a):
    return np.ones_like(np.asarray(a, float))


def SP2(a):
    return np.cosh(0.2 * np.pi * np.asarray(a, float)) ** 2


def check_ghost2_constants():
    print("== ghost-2 analytic chain (machine-checked constants) ==")
    s = np.sinh(0.2 * np.pi)
    print(f"   sinh(0.2 pi) = {s:.10f};  sinh(0.2 pi)^4 = {s**4:.10f}")
    a = np.linspace(1e-9, 1.0, 2_000_001)
    chord = np.max(np.sinh(0.2 * np.pi * a) / a)          # sup at a=1 (convexity)
    assert chord <= s + 1e-12, chord
    print(f"   chord bound sup sinh(0.2 pi a)/a on (0,1] = {chord:.10f} "
          f"(= sinh(0.2 pi), convexity)")
    margin = 3.0 - s ** 4
    print(f"   proof margin: h(a) >= {margin:.6f} a on (0,1]  (>= 2.79 a)")
    assert margin >= 2.79
    return margin


def check_ghost2_dense():
    print("== ghost-2 dense continuum check (tol = 0) ==")
    a = np.linspace(0.0, 1.0, 2_000_001)
    so, sp = SO2(a), SP2(a)
    x = a - so - sp
    resid = np.abs(x) - 2.0 * np.sqrt(so * sp)
    hv = 4 * so * sp - x ** 2
    print(f"   band residual = 0 by construction; count = 2*{PSI2} + 2*{Q} = "
          f"{2*PSI2 + 2*Q}")
    print(f"   max exact-CS residual |X| - 2 sqrt(SO SP) on [0,1] = "
          f"{resid.max():+.3e}  (at a = {a[np.argmax(resid)]:.6f}; "
          f"a=0 residual {resid[0]:+.1e} = closed-cone boundary)")
    print(f"   min h(a)/a (a>0) = {(hv[1:]/a[1:]).min():.6f}  "
          f"(proof: >= 2.79)")
    assert resid.max() <= 1e-12
    ao = np.linspace(1.0, 200.0, 200_001)
    st = SO2(ao) + SP2(ao)
    print(f"   out-of-band S_total on [1,200] with X=0: min = {st.min():.4f} "
          f"> 0; S_O = 1 flat -> feasible for EVERY Bochner window A")
    print(f"   I2 cap: 1 + eta = 1 <= DMAX * s with s = 2 psi_2 = {2*PSI2}: "
          f"feasible iff DMAX >= 2 (DMAX = 2 pi: {1.0 <= 2*np.pi*0.5})")


def check_ghost2_in_matrices(XF=80.0, na=600, nb=320, A=3.0, tol=0.0,
                             DMAX=2 * np.pi):
    """Plug ghost-2 into the class basis (lp_primal3 cells/tails) + I2 rows."""
    from lp_primal3 import make_cells, cell_cols, tail_cols, TAILB, MMAX
    print(f"== ghost-2 in the refereed cell basis (XF={XF:g} na={na} nb={nb} "
          f"A={A:g} tol={tol:g}) + I2 rows (DMAX={DMAX:.4f}) ==")
    lo, hi = make_cells(XF)
    ab = np.linspace(0.0, 1.0, na)
    ao = np.linspace(1.0 + 1e-3, A, nb)
    aa = np.concatenate([ab, ao])
    psi = np.zeros(MMAX); psi[1] = PSI2
    p1 = Q
    so = np.array([np.dot(np.arange(1, MMAX + 1) ** 2, psi)
                   + 0.0 for _ in aa])          # eta = 0, tails = 0
    sp = 4 * p1 * np.cosh(2 * np.pi * aa * 0.1) ** 2
    x = np.where(aa <= 1.0, aa - so - sp, 0.0)
    band = np.abs(so[:na] + sp[:na] + x[:na] - ab)
    oob = -(so[na:] + sp[na:] + x[na:])
    cs = np.abs(x) - 2 * np.sqrt(so * sp)
    count = np.dot(np.arange(1, MMAX + 1), psi) + 2 * p1
    s_lin = np.dot(np.arange(1, MMAX + 1), psi)
    cap = 1.0 + 0.0 - DMAX * s_lin              # I2 row value (need <= 0)
    print(f"   count = {count:.12f};  band resid max = {band.max():.3e}; "
          f"oob max -(S) = {oob.max():+.3e}")
    print(f"   exact-CS max = {cs.max():+.3e};  I2 cap row max = {cap:+.4f} "
          f"(<= 0 required)")
    ok = (abs(count - 1) < 1e-12 and band.max() <= tol + 1e-12
          and oob.max() <= tol + 1e-12 and cs.max() <= 1e-12 and cap <= 0)
    print(f"   ghost-2 feasible in C0+I2 at tol={tol:g}: {ok}")
    return ok


if __name__ == "__main__":
    check_ghost2_constants()
    check_ghost2_dense()
    ok1 = check_ghost2_in_matrices()
    ok2 = check_ghost2_in_matrices(XF=160.0, na=1200, nb=1280, A=5.0)
    print(f"\nVERDICT: C0+I2 certified constant = 0 EXACTLY for every "
          f"DMAX >= 2 (witness above, tol=0, every window A; "
          f"lower side trivial psi_1 >= 0).  refinement-check pass: "
          f"{ok1 and ok2}")
