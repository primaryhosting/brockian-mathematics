"""W4 library: the one-delta [DATA-1DELTA] LP over the T1 refereed basis,
with dual extraction + independent Lagrangian re-verification.

CLASS C_A(basis) / C_B(basis)  (T1's Variant A/B, refereed numbers live here):
  variables  psi_m >= 0 (m = 1..5), p_y >= 0 (pair depths, optional),
             eta_j >= -1 (cell densities on (0, XF], T1 cell partition),
             tail coefficients >= 0 (T1 tail basis, +/- split);
  S(alpha) = sum m^2 psi_m + sum_y 4 cosh^2(2 pi alpha y) p_y
             + etahat(alpha) + tails(alpha)     [delta_0 bookkeeping: the
             background dx absorbs the diagonal delta_0 exactly -- T1's
             refereed bookkeeping, carried unchanged];
  band:      |S(alpha) - alpha| <= tol,  alpha in grid[0, 1] (na points);
  C_B adds   S(alpha) >= -tol,  alpha in grid(1, A] (nb points)   <-- THE
             out-of-band spectral positivity rows (binding in this frame;
             vacuous in the 2-level frame by Lemma F, frame_lemma.py);
  count:     sum m psi_m + 2 sum p_y = 1;   objective min psi_1.

LOWER-BOUND VALIDITY DIRECTIONS (stated once, used everywhere):
  * finite alpha-grids RELAX the adversary  -> grid dual bounds transfer to
    the continuum-alpha class;
  * tol > 0 RELAXES the adversary          -> bounds transfer to tol = 0;
  * cellwise eta RESTRICTS the adversary   -> grid bounds do NOT transfer to
    densities off the cell partition; promotion needs the pointwise kernel
    check K(x) >= 0 on (0, XF] (kernel_check below, Lipschitz-certified);
  * the tail basis + XF cutoff are CLASS RESTRICTIONS -> every bound here is
    scoped to the committed T1 class C(XF, tailbasis), the same scope as the
    refereed V_A/V_B quantification.  (First-unjustified-step register, W4-1.)
"""
import numpy as np
from scipy.optimize import linprog

import _t1_lp_primal3 as t1   # vendored copy of the refereed T1 basis module

MMAX = t1.MMAX
TAILB = t1.TAILB


def build(XF=80.0, na=251, tol=2e-4, A=None, nb=400, depths=(), amax=1.0):
    lo, hi = t1.make_cells(XF)
    ncell = len(lo)
    ntail = len(TAILB) + 1
    npair = len(depths)
    n = MMAX + npair + ncell + 2 * ntail
    iP, iE, iT = MMAX, MMAX + npair, MMAX + npair + ncell

    ab = np.linspace(0.0, amax, na)
    ao = (np.linspace(1.0 + 1e-3, A, nb) if A is not None
          else np.zeros(0))
    aa = np.concatenate([ab, ao])

    def srow(a):
        row = np.zeros(n)
        row[:MMAX] = np.arange(1, MMAX + 1) ** 2
        for k, y in enumerate(depths):
            row[iP + k] = 4 * np.cosh(2 * np.pi * a * y) ** 2
        row[iE:iT] = t1.cell_cols(a, lo, hi)
        tc = t1.tail_cols(a, XF)
        row[iT:iT + ntail] = tc
        row[iT + ntail:] = -tc
        return row

    S = np.array([srow(a) for a in aa])
    A_ub, b_ub, tags = [], [], []
    for i, a in enumerate(ab):
        A_ub.append(S[i]);  b_ub.append(a + tol); tags.append(("band+", a))
        A_ub.append(-S[i]); b_ub.append(-(a - tol)); tags.append(("band-", a))
    for i in range(na, len(aa)):
        A_ub.append(-S[i]); b_ub.append(tol); tags.append(("oob", aa[i]))
    # tail positivity budget (T1 artifact row; dual mass on it is reported)
    row = np.zeros(n)
    row[iT:iT + ntail - 1] = 1.0
    row[iT + ntail:-1] = 1.0
    row[iT + ntail - 1] = 1 / np.pi ** 2
    row[-1] = 1 / np.pi ** 2
    A_ub.append(row); b_ub.append(XF ** 2 * 0.9); tags.append(("tailbudget",))

    A_eq = np.zeros((1, n))
    A_eq[0, :MMAX] = np.arange(1, MMAX + 1)
    A_eq[0, iP:iE] = 2.0
    b_eq = np.array([1.0])

    lb = np.zeros(n)
    lb[iE:iT] = -1.0
    c = np.zeros(n); c[0] = 1.0
    meta = dict(n=n, iP=iP, iE=iE, iT=iT, ncell=ncell, ntail=ntail,
                lo=lo, hi=hi, aa=aa, na=na, tags=tags, XF=XF, tol=tol,
                depths=depths, A=A)
    return c, np.array(A_ub), np.array(b_ub), A_eq, b_eq, lb, meta


def solve(dual=True, fix_psi=None, fix_p=None, label="", **kw):
    c, Aub, bub, Aeq, beq, lb, meta = build(**kw)
    if fix_psi is not None or fix_p is not None:
        rows, rhs = [Aeq], [beq]
        if fix_psi is not None:
            for k, v in enumerate(fix_psi):
                if v is None or (isinstance(v, float) and np.isnan(v)):
                    continue                      # NaN/None = leave free
                r = np.zeros(meta["n"]); r[k] = 1.0
                rows.append(r[None, :]); rhs.append([v])
        if fix_p is not None:
            for k, v in enumerate(fix_p):
                r = np.zeros(meta["n"]); r[meta["iP"] + k] = 1.0
                rows.append(r[None, :]); rhs.append([v])
        Aeq = np.vstack(rows); beq = np.concatenate(rhs)
    bounds = [(lb[j], None) for j in range(meta["n"])]
    res = linprog(c, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq,
                  bounds=bounds, method="highs")
    out = dict(label=label, status=res.status, value=None, meta=meta)
    hdr = (f"[{label}] XF={meta['XF']:g} na={meta['na']} tol={meta['tol']:g}"
           + (f" A={meta['A']:g}" if meta['A'] else " band-only")
           + (f" depths={meta['depths']}" if meta['depths'] else ""))
    if res.status != 0:
        print(f"{hdr}\n   status {res.status}: {res.message.strip()}")
        return out
    x = res.x
    psi = x[:MMAX]; p = x[meta["iP"]:meta["iE"]]
    print(f"{hdr}\n   LP value = {res.fun:.7f}   psi = {np.round(psi, 5)}"
          + (f"   p = {np.round(p, 6)}" if len(p) else ""))
    out.update(value=res.fun, x=x, psi=psi, p=p)
    if dual:
        y = np.maximum(-np.asarray(res.ineqlin.marginals), 0.0)
        z = -np.asarray(res.eqlin.marginals)
        bnd, leak, tbm, r = verify_dual(c, Aub, bub, Aeq, beq, lb, y, z,
                                        meta, x)
        print(f"   DUAL re-verified grid-class bound = {bnd:.7f}  "
              f"(leakage <= {leak:.2e}; tail-budget dual mass = {tbm:.2e})")
        out.update(dual_bound=bnd, leak=leak, tb_mass=tbm, y=y, z=z, r=r)
    return out


def verify_dual(c, Aub, bub, Aeq, beq, lb, y, z, meta, xstar):
    """Independent Lagrangian reconstruction (ladder.py's method, W3-refereed
    shape): bound = -y.b - z.beq + sum_j min_{x_j >= lb_j} r_j x_j."""
    r = c + Aub.T @ y + Aeq.T @ z
    bound = -float(y @ bub) - float(z @ beq)
    leak = 0.0
    for j in range(len(c)):
        if r[j] >= 0:
            bound += r[j] * lb[j]
        else:
            leak += abs(r[j]) * (abs(xstar[j]) + 1.0)
    tb = [k for k, t in enumerate(meta["tags"]) if t[0] == "tailbudget"]
    tbm = float(sum(y[k] for k in tb))
    return bound, leak, tbm, r


def dual_kernel(out, ngrid=400_001):
    """Spectral dual measure rho (band signed atoms + oob nonpositive atoms)
    and the x-space kernel K(x) = 2 sum rho_i cos(2 pi alpha_i x).
    Returns (min over dense grid, certified min via Lipschitz, rho info).
    Continuum-x promotion of the dual bound requires certified min >= 0."""
    meta, y = out["meta"], out["y"]
    aa, na = meta["aa"], meta["na"]
    rho = np.zeros(len(aa))
    kb = 0
    for k, t in enumerate(meta["tags"]):
        if t[0] == "band+":
            rho[kb // 2] += y[k]; kb += 1
        elif t[0] == "band-":
            rho[kb // 2] -= y[k]; kb += 1
        elif t[0] == "oob":
            rho[na + (k - 2 * na)] = -y[k]
    xs = np.linspace(1e-9, meta["XF"], ngrid)
    nz = np.abs(rho) > 0
    aan, rhon = aa[nz], rho[nz]
    kmin, xmin = np.inf, 0.0
    for s in range(0, ngrid, 50_000):          # chunked: memory-safe
        xc = xs[s:s + 50_000]
        Kc = 2.0 * (np.cos(2 * np.pi * np.outer(xc, aan)) @ rhon)
        j = int(np.argmin(Kc))
        if Kc[j] < kmin:
            kmin, xmin = float(Kc[j]), float(xc[j])
    lipK = 4 * np.pi * float(np.abs(rhon) @ aan)
    h = xs[1] - xs[0]
    cert_min = kmin - lipK * h / 2
    return dict(kmin_grid=kmin, kmin_cert=cert_min, lip=lipK, rho=rho,
                x_at_min=xmin, n_atoms=int(nz.sum()),
                oob_mass=float(rho[na:].sum()), band_mass=float(rho[:na].sum()))
