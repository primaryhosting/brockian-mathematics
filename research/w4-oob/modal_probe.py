"""W4 second-order probe: can the structural modulated family improve on
Montgomery-Taylor at second order?  [certificate-side analysis]

Around the MT point (R = 1, J+G = 1/c1* + 1), adding an envelope env >= 0
modulated at frequency phi (admissible: cos(2 pi phi alpha) <= 0 on the
whole (1, 3/2], i.e. phi in [1/4, 1/2]) changes
    LB = 2 - (J+G)/R    by    eps^2 * Q_phi(env) + O(eps^4),
    Q_phi(env) = (1/c1*) |int env e^{2 pi i phi t} dt|^2
                 - 2 int_0^1 a cos(2 pi phi a) g_env(a) da - int env^2,
(g_env the autocorrelation).  Q_phi is a quadratic form; the family helps
at second order iff sup_{env >= 0} Q_phi > 0 for some admissible phi.
This file computes the top of Q_phi over env >= 0 (projected gradient on
the unit sphere) and over UNSIGNED env (top eigenvalue -- an upper bound
for the constrained sup).  A negative unsigned top settles the question.
"""
import numpy as np

INVC = 1.3274992785663613     # 1/c1* (matches calibrated V_A chain)
T2 = 1.5
m = 241
t = np.linspace(0, T2, m)
dt = t[1] - t[0]
w = np.full(m, dt); w[0] = w[-1] = dt / 2

# Build Q_phi as an m x m symmetric matrix over env grid values.
# term 1: INVC * |sum_j w_j env_j e^{2 pi i phi t_j}|^2
# term 2: -2 int_0^1 a cos(2 pi phi a) g(a) da,
#         g(a_k) = sum_j w'_j env_j env_{j-k}-style -> assemble directly:
#         -2 * sum_{j,l} env_j env_l F(t_j - t_l),
#         F(x) = |x| cos(2 pi phi x) restricted |x| <= 1 ... careful:
#         2 int_0^1 a cos g(a) da = int_{-1}^{1} |a| cos(2 pi phi a) g(a) da
#         and int g(a) H(a) da = sum_{j,l} env_j env_l H(t_j - t_l) exactly
#         (autocorrelation pairing identity).
# term 3: -int env^2 -> -sum w_j env_j^2 (diagonal)


def build_Q(phi):
    e = np.exp(2j * np.pi * phi * t) * w
    Q1 = INVC * np.real(np.outer(e, np.conj(e)))
    D = t[:, None] - t[None, :]
    H = np.where(np.abs(D) <= 1.0,
                 np.abs(D) * np.cos(2 * np.pi * phi * D), 0.0)
    Q2 = -(np.outer(w, w) * H)
    Q3 = -np.diag(w)
    return Q1 + Q2 + Q3


def top_constrained(Q, iters=3000, seed=0):
    rng = np.random.default_rng(seed)
    v = np.abs(rng.standard_normal(m)); v /= np.linalg.norm(v)
    lam = 0.0
    # projected power iteration with spectral shift
    shift = np.abs(Q).sum(1).max() + 1.0
    for _ in range(iters):
        v = np.maximum(Q @ v + shift * v, 0.0)
        n = np.linalg.norm(v)
        if n == 0:
            return 0.0, v
        v /= n
        lam = float(v @ Q @ v)
    return lam, v


print("phi    top eig (unsigned)   sup over env>=0 (proj. power)")
for phi in (0.25, 0.30, 0.35, 0.40, 0.45, 0.50):
    Q = build_Q(phi)
    Qs = 0.5 * (Q + Q.T)
    lam_max = float(np.linalg.eigvalsh(Qs)[-1])
    lam_pos, _ = top_constrained(Qs)
    print(f"{phi:.2f}   {lam_max:+.6f}          {lam_pos:+.6f}")
print("\nsup Q_phi <= 0 for all admissible phi  ==>  the structural "
      "modulated family CANNOT leave V_A at second order (graveyard); "
      "any positive value ==> a strictly improving direction exists.")
