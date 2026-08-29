import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-!
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped ComplexConjugate
open Matrix

namespace QI

section Frobenius

variable {m n : Type} [Fintype m] [Fintype n]

/-- The squared Frobenius norm of a complex matrix, as a real number. -/

lemma eigen_on_code {P : Matrix m m ℂ} (hP : IsCodeProjector P) (A : Matrix m m ℂ)
    (h : ∀ v : Matrix m (Fin 1) ℂ, P * v = v → ∃ l : ℂ, A * v = l • v) :
    ∃ l : ℂ, A * P = l • P := by
  obtain ⟨j0, hj0⟩ := exists_colVec_ne_zero hP.ne_zero
  set v0 : Matrix m (Fin 1) ℂ := colVec P j0 with hv0def
  have hv0code : P * v0 = v0 := by rw [hv0def, mul_colVec, hP.idem]
  obtain ⟨l, hl⟩ := h v0 hv0code
  refine ⟨l, ?_⟩
  have main : ∀ v : Matrix m (Fin 1) ℂ, P * v = v → A * v = l • v := by
    intro v hv
    obtain ⟨n, hn⟩ := h v hv
    by_cases hcase : ∃ t : ℂ, v = t • v0
    · obtain ⟨t, rfl⟩ := hcase
      rw [Matrix.mul_smul, hl, smul_smul, smul_smul, mul_comm]
    · obtain ⟨n', hn'⟩ := h (v + v0) (by rw [Matrix.mul_add, hv, hv0code])
      have e : n' • v + n' • v0 = n • v + l • v0 := by
        rw [← smul_add, ← hn', Matrix.mul_add, hn, hl]
      have e2 : (n' - n) • v = (l - n') • v0 := by
        rw [sub_smul, sub_smul, sub_eq_sub_iff_add_eq_add, e]
        exact add_comm _ _
      have hnn : n' = n := by
        by_contra hc
        apply hcase
        refine ⟨(n' - n)⁻¹ * (l - n'), ?_⟩
        rw [← smul_smul, ← e2, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hc), one_smul]
      have hz : (l - n') • v0 = 0 := by rw [← e2, hnn, sub_self, zero_smul]
      have hln : l = n' := by
        rcases smul_eq_zero.mp hz with h1 | h1
        · exact sub_eq_zero.mp h1
        · exact absurd h1 hj0
      rw [hn, hln, hnn]
  ext i j
  have hcol := main (colVec P j) (by rw [mul_colVec, hP.idem])
  rw [mul_colVec] at hcol
  have := congrFun (congrFun hcol i) 0
  simpa [colVec] using this

end CodeVectors

section Forward

variable {m ι : Type} [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι]

/-- A correctable code satisfies the Knill–Laflamme conditions. -/
