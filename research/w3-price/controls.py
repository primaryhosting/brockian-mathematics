"""W3 controls, per level (method law #4).

CONTROL P: the genuine GUE all-simple configuration (psi_1 = 1, p = mu = 0,
  eta = exact cell averages of -sinc^2, tail = -F via colF, X = 0) must
  remain FEASIBLE at every level -- it satisfies every TRUE constraint, so a
  level rejecting it is WRONG, not strong.  Test = feasibility LP over the
  level's full row set with (psi, p) pinned (eta/tails free to polish
  discretization error, exactly control_checks.py's fair-test convention).

CONTROL N: pure doubles (psi_2 = 1/2, p = 0) must remain INFEASIBLE at every
  level.  Standard = Referee C's quantitative phase-1 certificate: minimise
  the sup band residual t with everything else hard; t* >> tol is the
  certificate (t* ~ 0.680 at C0; Fejer dual predicts >= 1/3).  For levels
  containing I5 the rejection is already algebraic:
  LHS = 3*0 + 4*(1/2 + 0) = 2 < 4 - 1/c1* = 2.6725007.
"""
import numpy as np
from scipy.optimize import linprog
from scipy.integrate import quad
import ladder
from ladder import build, RHS44
from lp_primal3 import make_cells, MMAX  # noqa  (path set by ladder import)


def phase1(flags, fixpsi, fixp, DMAX=2 * np.pi, i3_tied=True, label=""):
    """Min sup-band-residual t with (psi, p) pinned; all non-band rows hard.
    Returns t* (np.inf if even the t-relaxed problem is infeasible)."""
    c, Aub, bub, Aeq, beq, lb, ub, meta = build(
        flags, tol=0.0, DMAX=DMAX, i3_tied=i3_tied,
        fix={"psi": fixpsi, "p": fixp})
    n = meta["n"]
    isband = np.array([t[0] in ("band+", "band-") for t in meta["tags"]])
    col = np.where(isband, -1.0, 0.0).reshape(-1, 1)
    Aub2 = np.hstack([Aub, col])
    c2 = np.zeros(n + 1); c2[-1] = 1.0
    Aeq2 = np.hstack([Aeq, np.zeros((len(Aeq), 1))])
    bounds = [(lb[j], None) for j in range(n)] + [(0, None)]
    res = linprog(c2, A_ub=Aub2, b_ub=bub, A_eq=Aeq2, b_eq=beq,
                  bounds=bounds, method="highs")
    t = res.fun if res.status == 0 else np.inf
    print(f"   [{label}] phase-1 t* = "
          f"{t if np.isinf(t) else round(t, 6)}"
          f"{'  (hard rows alone infeasible)' if np.isinf(t) else ''}")
    return t


def control_P(flags, DMAX=2 * np.pi, i3_tied=True, tol=2e-4, label=""):
    fixpsi = np.zeros(MMAX); fixpsi[0] = 1.0
    fixp = np.zeros(5)
    c, Aub, bub, Aeq, beq, lb, ub, meta = build(
        flags, tol=tol, DMAX=DMAX, i3_tied=i3_tied,
        fix={"psi": fixpsi, "p": fixp})
    bounds = [(lb[j], None) for j in range(meta["n"])]
    res = linprog(np.zeros(meta["n"]), A_ub=Aub, b_ub=bub, A_eq=Aeq,
                  b_eq=beq, bounds=bounds, method="highs")
    ok = res.status == 0
    print(f"   [{label}] CONTROL P (GUE all-simple, psi_1=1 pinned): "
          f"{'PASS (feasible)' if ok else f'FAIL status={res.status} -- LEVEL IS WRONG'}")
    return ok


def control_N(flags, DMAX=2 * np.pi, i3_tied=True, label=""):
    fixpsi = np.zeros(MMAX); fixpsi[1] = 0.5
    fixp = np.zeros(5)
    if "I5" in flags:
        print(f"   [{label}] CONTROL N: rejected ALGEBRAICALLY by I5 row "
              f"(2 < {RHS44:.7f}); phase-1 over remaining rows:")
    t = phase1(flags, fixpsi, fixp, DMAX=DMAX, i3_tied=i3_tied,
               label=label + " N")
    ok = ("I5" in flags) or (t > 0.05)
    print(f"   [{label}] CONTROL N (pure doubles): "
          f"{'PASS (infeasible, quantitative)' if ok else 'FAIL -- pure doubles accepted, LEVEL BROKEN'}")
    return ok


LEVELS = [
    ("L0  C0", set(), True),
    ("L1A +I1", {"I1"}, True),
    ("L2A +I1+I2", {"I1", "I2"}, True),
    ("L3A +I1+I2+I3", {"I1", "I2", "I3"}, True),
    ("L5  all", {"I1", "I2", "I3", "I4", "I5"}, True),
    ("L1B +I5", {"I5"}, True),
    ("S3u I3-UNTIED", {"I3"}, False),
]

if __name__ == "__main__":
    print("======== CONTROLS PER LEVEL ========")
    allok = True
    for name, fl, tied in LEVELS:
        print(f"-- {name} --")
        okP = control_P(fl, i3_tied=tied, label=name)
        okN = control_N(fl, i3_tied=tied, label=name)
        allok &= okP and okN
    print(f"\nALL CONTROLS: {'PASS' if allok else 'AT LEAST ONE FAILURE (see above)'}")
