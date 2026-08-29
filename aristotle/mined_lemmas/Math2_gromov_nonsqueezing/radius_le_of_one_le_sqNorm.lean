/-
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Math2

/-- The standard symplectic form on `ℝ^{2n}`, with coordinates indexed by
`Fin n × Fin 2` (the pair `(i, 0)`, `(i, 1)` being the `i`-th conjugate pair). -/

lemma radius_le_of_one_le_sqNorm {n : ℕ} {r R : ℝ} (hR : 0 ≤ R)
    (p q : Fin n × Fin 2 → ℝ) (hp : 1 ≤ sqNorm p)
    (h : ∀ v : Fin n × Fin 2 → ℝ, sqNorm v < r ^ 2 →
      (symplecticForm p v) ^ 2 + (symplecticForm q v) ^ 2 < R ^ 2) :
    r ≤ R := by
  by_contra hlt
  push_neg at hlt
  have hs : (0 : ℝ) < sqNorm p := lt_of_lt_of_le zero_lt_one hp
  set s : ℝ := Real.sqrt (sqNorm p) with hsdef
  have hspos : 0 < s := Real.sqrt_pos.mpr hs
  have hs2 : s ^ 2 = sqNorm p := Real.sq_sqrt hs.le
  set v : Fin n × Fin 2 → ℝ := (R / s) • jvec p with hv
  have hnv : sqNorm v = R ^ 2 := by
    rw [hv, sqNorm_smul, sqNorm_jvec, div_pow, ← hs2]
    field_simp
  have hball : sqNorm v < r ^ 2 := by
    rw [hnv]
    exact sq_lt_sq' (by linarith) hlt
  have hpv : symplecticForm p v = R * s := by
    rw [hv, symplecticForm_smul_right, symplecticForm_self_jvec, ← hs2]
    field_simp
  have hR2 : R ^ 2 ≤ (symplecticForm p v) ^ 2 := by
    rw [hpv]
    have h1 : 1 ≤ s := by
      nlinarith [hspos, hs2]
    nlinarith [hR, hspos]
  have := h v hball
  nlinarith [sq_nonneg (symplecticForm q v)]

