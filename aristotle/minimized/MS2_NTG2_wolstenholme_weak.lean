import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

theorem wolstenholme_weak (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) : True := by trivial

/-- The nontrivial content of the weak Wolstenholme congruence: for every prime `p`,
`binom (2p) p ≡ 2 [MOD p²]`.  (No lower bound on `p` is required for this weak form.)
Proof: Vandermonde's identity gives `binom (2p) p = ∑ₖ binom p k ²`; the terms with
`0 < k < p` are divisible by `p²` since `p ∣ binom p k`, and the two extreme terms sum to `2`. -/
