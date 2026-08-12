"""W4 main ladder [DATA-1DELTA]: pricing out-of-band spectral positivity in
the one-delta frame, with verified duals at every basis.

Every LP value below is a property of the committed class C(XF, cells, tail
basis) at the stated (na, nb, A, tol); "DUAL re-verified" numbers are
independent Lagrangian reconstructions (certified lower bounds for the
grid-cell class; they transfer to continuum-alpha and tol=0 by the
relaxation directions stated in oned.py).  Kernel check = continuum-x
promotion test (K(x) >= 0 pointwise on (0, XF], Lipschitz-certified).

RUN GROUPS (argv[1]):
  ladder   Variant A vs Variant B at matched bases -> the marginal price
  pairs    Variant C (+ off-line pair species) with depth ladders
  simples  the no-multiplicity probe (psi_2..5 == 0): OOB price w/o
           the integrality mechanism
  anatomy  primal structure of the finest Variant-B optimum: what replaces
           7.5(a) as the binding adversary (touch points, dual atoms)
"""
import sys
import numpy as np
import oned

BASES = [  # (XF, na, nb, A)
    (80.0, 601, 400, 3.0),
    (80.0, 1201, 800, 3.0),
    (160.0, 1201, 800, 3.0),
    (160.0, 2001, 1200, 3.0),
    (240.0, 2001, 1200, 3.0),
]


def kreport(out):
    if "y" not in out:
        return
    k = oned.dual_kernel(out)
    print(f"   KERNEL: {k['n_atoms']} atoms; band mass {k['band_mass']:+.4f} "
          f"oob mass {k['oob_mass']:+.4f}")
    print(f"   KERNEL min on (0,XF]: grid {k['kmin_grid']:+.3e} at "
          f"x = {k['x_at_min']:.3f}; Lipschitz-certified min "
          f"{k['kmin_cert']:+.3e} -> continuum-x promotion "
          f"{'PASS' if k['kmin_cert'] >= 0 else 'FAIL (grid-cell class only)'}")
    out["kern"] = k


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "ladder"

    if which == "ladder":
        print("======== VARIANT A (band-only) vs VARIANT B (+oob rows), "
              "matched bases ========")
        for XF, na, nb, A in BASES:
            ra = oned.solve(label="A", XF=XF, na=na, tol=2e-4)
            rb = oned.solve(label="B", XF=XF, na=na, tol=2e-4, A=A, nb=nb)
            kreport(rb)
            if ra["value"] is not None and rb["value"] is not None:
                print(f"   MARGINAL PRICE of oob rows at this basis: "
                      f"{rb['value'] - ra['value']:+.7f}\n")
        print("---- tol sensitivity at (160, 1201, 800, 3) ----")
        for tol in (2e-4, 5e-5, 1e-5):
            rb = oned.solve(label=f"B tol={tol:g}", XF=160.0, na=1201,
                            tol=tol, A=3.0, nb=800)
        print("---- window sensitivity at (160, 1201) ----")
        for A, nb in ((2.0, 600), (3.0, 800), (5.0, 1600)):
            rb = oned.solve(label=f"B A={A:g}", XF=160.0, na=1201,
                            tol=2e-4, A=A, nb=nb)

    elif which == "pairs":
        print("======== VARIANT C: adversary WITH off-line pair species "
              "========")
        for XF, na, nb, A in ((80.0, 601, 400, 3.0), (160.0, 1201, 800, 3.0)):
            for dep in ((0.1, 0.2, 0.3, 0.4, 0.5),
                        (0.1, 0.2, 0.3, 0.4, 0.5, 0.75, 1.0),
                        (0.1, 0.2, 0.3, 0.4, 0.5, 1.0, 1.5, 2.0)):
                rc = oned.solve(label=f"C ymax={dep[-1]:g}", XF=XF, na=na,
                                tol=2e-4, A=A, nb=nb, depths=dep)
                if rc["value"] is not None and len(rc["p"]):
                    act = {y: round(float(m), 6)
                           for y, m in zip(dep, rc["p"]) if m > 1e-9}
                    print(f"   active pair masses: {act}")
            print()

    elif which == "simples":
        print("======== SIMPLES-ONLY PROBE (psi_2..5 == 0): does OOB pay "
              "without the multiplicity mechanism? ========")
        fix = [np.nan, 0.0, 0.0, 0.0, 0.0]
        ra = oned.solve(label="simples band-only", XF=80.0, na=601,
                        tol=2e-4, fix_psi=fix)
        rb = oned.solve(label="simples +oob", XF=80.0, na=601, tol=2e-4,
                        A=3.0, nb=400, fix_psi=fix)
        rc = oned.solve(label="simples+pairs band-only", XF=80.0, na=601,
                        tol=2e-4, depths=(0.1, 0.2, 0.3, 0.4, 0.5),
                        fix_psi=fix)
        rd = oned.solve(label="simples+pairs +oob", XF=80.0, na=601,
                        tol=2e-4, A=3.0, nb=400,
                        depths=(0.1, 0.2, 0.3, 0.4, 0.5), fix_psi=fix)
        print(f"\n   OOB price w/o integrality (no pairs):  "
              f"{rb['value'] - ra['value']:+.7f}")
        print(f"   OOB price w/o integrality (with pairs): "
              f"{rd['value'] - rc['value']:+.7f}")

    elif which == "anatomy":
        print("======== BINDING-ADVERSARY ANATOMY, finest Variant B ========")
        XF, na, nb, A = 160.0, 2001, 1200, 3.0
        rb = oned.solve(label="B finest", XF=XF, na=na, tol=2e-4, A=A, nb=nb)
        kreport(rb)
        meta, x = rb["meta"], rb["x"]
        # rebuild S(alpha) on a dense oob grid straight from the primal
        lo, hi = meta["lo"], meta["hi"]
        iE, iT, ntail = meta["iE"], meta["iT"], meta["ntail"]
        eta = x[iE:iT]; tails = x[iT:]
        ao = np.linspace(1.0, A, 4001)
        S = np.empty_like(ao)
        for i, a in enumerate(ao):
            S[i] = (np.arange(1, 6) ** 2 @ x[:5]
                    + oned.t1.cell_cols(a, lo, hi) @ eta
                    + oned.t1.tail_cols(a, XF) @ (tails[:ntail]
                                                  - tails[ntail:]))
        print(f"   oob S(alpha): min = {S.min():+.4e}; "
              f"S(1.0) = {S[0]:+.4e}; S({A:g}) = {S[-1]:+.4e}")
        thr = 2e-3
        touch = ao[S < thr]
        if len(touch):
            # collapse runs into intervals
            runs, start = [], touch[0]
            for u, v in zip(touch[:-1], touch[1:]):
                if v - u > 2 * (ao[1] - ao[0]):
                    runs.append((start, u)); start = v
            runs.append((start, touch[-1]))
            print(f"   S ~ 0 touch regions (S < {thr}): "
                  + ", ".join(f"[{a:.3f},{b:.3f}]" for a, b in runs))
        # dual oob atom locations
        y, aa = rb["y"], meta["aa"]
        oobtags = [(k, t[1]) for k, t in enumerate(meta["tags"])
                   if t[0] == "oob"]
        atoms = [(al, y[k]) for k, al in oobtags if y[k] > 1e-8]
        atoms.sort(key=lambda t: -t[1])
        print(f"   dual oob atoms (top 12 of {len(atoms)}): "
              + ", ".join(f"({al:.3f}: {w:.3g})" for al, w in atoms[:12]))
        # eta anatomy: where does the correlation sit at -1 / above 0?
        cen = 0.5 * (lo + hi)
        at_floor = cen[eta < -0.999]
        print(f"   eta at floor -1 on x in "
              f"[{at_floor.min():.3f}, {at_floor.max():.3f}] "
              f"({len(at_floor)} cells)" if len(at_floor) else
              "   eta never at -1")
        big = np.argsort(eta)[-5:][::-1]
        print("   largest eta cells: "
              + ", ".join(f"x~{cen[j]:.3f}: {eta[j]:+.3f}" for j in big))
    print("\nDone.")
