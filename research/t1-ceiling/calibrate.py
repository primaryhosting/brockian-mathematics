"""T1 ceiling gap: Step 1 -- calibration gate.

Paper's constants to recover (MUST pass before anything else):
  H(1) = 2/3                       (flat window, rank-trace certificate)
  MT optimum: c1* = 0.7532960, 2 - 1/c1* = 0.67250...   (Montgomery-Taylor)
  Cauchy-Schwarz: 2F(1) - 1 = 1/2  (flat window CS route)

Model (paper eq (7.3) at lambda = 1):
  M(V) = [ int V^2 + int int |s-s'| V(s)V(s') ] / (int V)^2 ,  V on [-1/2,1/2]
  certificate: s1/N >= 2 - min_V M(V);  CS: s1/N >= 2/M - 1 (flat).
Closed form (7.4): c1* = 2 tan(1/sqrt2) / (sqrt2 + tan(1/sqrt2)), optimizer
  V*(s) = cos(sqrt2 * s).
Identity check: M(V) = 1 + int_R K_V(x) (1 - F(x)) dx,
  K_V(x) = (Vhat(2 pi x)/Vhat(0))^2, F = Fejer = (sin pi x / pi x)^2.
"""
import numpy as np

def M_of_V(V, s):
    """M(V) on grid s (uniform, spacing h) via trapezoid-free midpoint sums."""
    h = s[1] - s[0]
    iV = np.sum(V) * h
    iV2 = np.sum(V * V) * h
    D = np.abs(s[:, None] - s[None, :])
    cross = V @ (D * h * h) @ V
    return (iV2 + cross) / iV**2

def minimize_M(n=2000):
    """min over signed V (paper says positivity constraint inactive).
    Stationarity of [V^T A V]/(1^T V h)^2: A V = const * 1  -> solve A V = 1."""
    h = 1.0 / n
    s = (np.arange(n) + 0.5) * h - 0.5
    D = np.abs(s[:, None] - s[None, :])
    A = np.eye(n) / h + D          # (1/h) I + |s-s'|  acting with weight h^2:
    # quadratic form: h * V^T (I/h... ) keep it simple: Q = h*diag + h^2*D
    Q = np.eye(n) * h + D * h * h
    one = np.ones(n)
    Vopt = np.linalg.solve(Q, one)
    return M_of_V(Vopt, s), Vopt, s

def main():
    # --- closed forms ---
    t = np.tan(1 / np.sqrt(2))
    c1 = 2 * t / (np.sqrt(2) + t)
    print(f"c1* closed form            = {c1:.7f}   (paper: 0.7532960)")
    print(f"1/c1*                      = {1/c1:.7f}   (paper M_opt: 1.3274992...)")
    print(f"2 - 1/c1*                  = {2-1/c1:.7f}   (paper: 0.67250...)")
    print(f"(3-1/c1*)/2                = {(3-1/c1)/2:.7f}   (paper Nd: 0.83625...)")

    # --- flat window ---
    n = 4000
    h = 1.0 / n
    s = (np.arange(n) + 0.5) * h - 0.5
    Vflat = np.ones(n)
    Mflat = M_of_V(Vflat, s)
    print(f"\nM(flat) numeric            = {Mflat:.6f}   (exact 4/3 = {4/3:.6f})")
    print(f"H(1) = 2 - M(flat)         = {2-Mflat:.6f}   (exact 2/3)")
    print(f"CS: 2/M - 1                = {2/Mflat-1:.6f}   (exact 1/2)")

    # --- MT window closed-form check ---
    Vmt = np.cos(np.sqrt(2) * s)
    Mmt = M_of_V(Vmt, s)
    print(f"\nM(cos sqrt2 s) numeric     = {Mmt:.7f}   vs 1/c1* = {1/c1:.7f}")

    # --- variational minimum over signed V ---
    Mmin, Vopt, sg = minimize_M(n=2000)
    print(f"M variational min (n=2000) = {Mmin:.7f}")
    print(f"optimizer min value        = {Vopt.min():.4f} (positive => V>=0 inactive)")
    # cosine-ness check
    Vn = Vopt / Vopt[len(Vopt)//2]
    err = np.max(np.abs(Vn - np.cos(np.sqrt(2) * sg)))
    print(f"||Vopt/V(0) - cos(sqrt2 s)||_inf = {err:.2e}")

    # --- identity M(V) = 1 + int K_V (1-F) ---
    x = np.linspace(-60, 60, 240001)
    dx = x[1] - x[0]
    om = 2 * np.pi * x
    Vhat_flat = np.where(np.abs(om) < 1e-12, 1.0, 2 * np.sin(om / 2) / om)
    K = Vhat_flat**2
    F = np.where(np.abs(x) < 1e-12, 1.0, (np.sin(np.pi * x) / (np.pi * x))**2)
    tail = 1 / (np.pi**2 * 60)   # int_{|x|>60} F dx  (mean of sin^2 = 1/2)
    ident = 1 + np.sum(K * (1 - F)) * dx + tail
    print(f"\nidentity flat: 1 + int K(1-F) = {ident:.6f}  (should be 4/3; tail-corrected)")

    gate = (abs(c1 - 0.7532960) < 1e-6 and abs(Mflat - 4/3) < 1e-3
            and abs(Mmt - 1/c1) < 1e-3 and abs(Mmin - 1/c1) < 1e-3
            and abs(ident - 4/3) < 1e-3)
    print(f"\nCALIBRATION GATE: {'PASS' if gate else 'FAIL'}")

if __name__ == "__main__":
    main()
