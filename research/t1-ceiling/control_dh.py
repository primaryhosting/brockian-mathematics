"""T1 controls (mandatory): Davenport-Heilbronn-type configurations.

Control 1 (paper's certificate, species level): for random self-conjugate
configurations (on-line points with multiplicities; off-line pairs of any
depth c >= 1; nonneg cross-correlations), verify
    cert := 4*tr - 2*count - frob2  <=  s1   (never overcertifies),
matching Prop 4.4(ii) in units (4.4): on-line point mult m: tr m, frob2 m^2;
pair (m, c): tr 2m, frob2 2m^2(1+c^2); cross terms only ADD to frob2.

Control 2 (Cohn-Elkies/doubly-positive certificate): the CE chain
    D2 * R(0) <= band-read
requires pair internal charge 2m^2 (R(0) + R(2iy)) >= what the count needs;
with Rhat < 0 anywhere outside [-1,1], R(2iy) -> -infty as depth grows.
Exhibit: explicit R > 0 on R with Rhat(alpha) < 0 on a patch outside the band,
and a configuration with one deep pair for which the CE-certified s1 EXCEEDS
the true s1  ->  CE-certificates are unconditionally DEAD (graveyard).
"""
import numpy as np

rng = np.random.default_rng(7)

def control1(trials=20000):
    bad = 0
    worst = np.inf
    for _ in range(trials):
        n_species = rng.integers(1, 6)
        tr = frob2 = count = s1 = 0.0
        for _ in range(n_species):
            if rng.random() < 0.6:      # on-line point species
                m = rng.integers(1, 5)
                w = rng.random()
                tr += m * w; frob2 += m * m * w; count += m * w
                if m == 1: s1 += w
            else:                        # off-line pair species
                m = rng.integers(1, 3)
                c = 1.0 + rng.exponential(2.0)
                w = rng.random() * 0.3
                tr += 2 * m * w; frob2 += 2 * m * m * (1 + c * c) * w
                count += 2 * m * w
        frob2 += rng.random() * 0.5      # nonneg cross correlations
        cert = 4 * tr - 2 * count - frob2
        slack = s1 - cert
        worst = min(worst, slack)
        if slack < -1e-12: bad += 1
    print(f"[control 1] paper certificate: {trials} random configs, "
          f"violations = {bad}, worst slack = {worst:.6f} (>=0 required)")

def control2():
    # base strictly positive bandwidth-1 kernel: F_1 + F_{1/sqrt2} (zeros disjoint)
    def F(x, lam=1.0):
        x = np.atleast_1d(np.asarray(x, dtype=complex))
        z = np.pi * lam * x
        out = np.ones_like(z)
        nz = np.abs(z) > 1e-9
        out[nz] = (np.sin(z[nz]) / z[nz]) ** 2
        return lam * out            # Fejer of bandwidth lam: hat = tri on [-lam,lam]
    def R0(x):                      # strictly positive, bandwidth 1
        return (F(x, 1.0) + F(x, 1/np.sqrt(2))).real
    # outside-band negative piece: q(x) = -eps * 2 cos(2 pi * 1.5 x) * F(x, 0.25)
    # => qhat = -eps * tri_{0.25} centered at +-1.5  (support [1.25,1.75])
    eps = 0.02
    def q(x):
        x = np.atleast_1d(np.asarray(x, dtype=complex))
        return (-eps * 2 * np.cos(2 * np.pi * 1.5 * x) * F(x, 0.25)).real
    def R(x): return R0(x) + q(x)
    xs = np.linspace(0, 200, 400001)
    rmin = np.min(R(xs))
    print(f"[control 2] CE kernel: min R on [0,200] = {rmin:.6f} "
          f"(must be > 0 for the on-line discard)")
    # R at imaginary argument 2iy: R(2iy) = int Rhat cosh(4 pi a y) da
    # compute directly from the analytic pieces:
    def Fc(z, lam):   # Fejer at complex argument
        w = np.pi * lam * z
        return lam * (np.sin(w) / w) ** 2 if abs(w) > 1e-9 else lam + 0j
    def Rimag(y):
        z = 2j * y
        base = Fc(z, 1.0) + Fc(z, 1 / np.sqrt(2))
        qq = -eps * 2 * np.cos(2 * np.pi * 1.5 * z) * Fc(z, 0.25)
        return (base + qq).real
    print("            depth y :  R(2iy)  [pair charge; paper-safe kernels have >= R(0)]")
    for y in (0.0, 0.2, 0.4, 0.6, 0.8, 1.0):
        print(f"              {y:4.1f}   :  {Rimag(y):+.4e}")
    # CE-certified D2-bound (band read) vs actual chain on a deep-pair config:
    # config: simples (1-2w) + one pair species mass w at depth y.
    # CE claims: D2 <= band-read/R(0). Actual D2 contribution of pair internal
    # in Sigma_all R is 2 m^2 (R(0)+R(2iy)) -> very negative, so the claimed
    # inequality chain asserts a WRONG upper bound on the pair-inclusive count.
    R00 = float(R(np.array([0.0]))[0])
    y, w = 1.0, 1e-3
    lhs_claim = (1 - 2*w) * R00 + w * 2 * (R00 + Rimag(y))   # true Sigma_diag R
    print(f"            claimed >= D2*R(0) = {R00 * (1 - 2*w + 4*w):.6f} ; "
          f"true diagonal read = {lhs_claim:.6f}")
    print(f"            -> pair of depth {y} with mass {w} makes the CE discard "
          f"INVALID by {R00*(1-2*w+4*w) - lhs_claim:.4f} (chain overcertifies)")

if __name__ == "__main__":
    control1()
    control2()
