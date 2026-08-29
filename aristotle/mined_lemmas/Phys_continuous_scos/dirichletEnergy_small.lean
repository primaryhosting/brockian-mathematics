import Mathlib

/-!
# The circle-valued spin space

The spin space of the classical XY model is the circle `Spin = ℝ / 2πℤ`, a compact
abelian group carrying a translation invariant (Haar) measure.  This file sets up the
cosine and sine functions on `Spin` together with the elementary trigonometric facts
used in the Mermin–Wagner argument.
-/

namespace Phys

noncomputable section

open MeasureTheory

instance factTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The spin space: the circle `ℝ / 2πℤ`. -/
abbrev Spin := AddCircle (2 * Real.pi)

/-- The cosine function on the circle. -/

theorem dirichletEnergy_small (hd : d ≤ 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℕ, 1 ≤ R ∧ ∀ N, R ≤ N → dirichletEnergy (d := d) R N < ε := by
  set M : ℝ := max 1 (35 / ε) with hM
  set R : ℕ := max 1 ⌈Real.exp M⌉₊ with hRdef
  have hR1 : 1 ≤ R := le_max_left _ _
  have hexp : Real.exp M ≤ (R:ℝ) := by
    have h1 : Real.exp M ≤ (⌈Real.exp M⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Real.exp M⌉₊ : ℕ) : ℝ) ≤ (R:ℝ) := by
      exact_mod_cast Nat.le_max_right 1 ⌈Real.exp M⌉₊
    linarith
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMe : 35 / ε ≤ M := le_max_right _ _
  have hLge : M ≤ Real.log (1 + (R:ℝ)) := by
    have h := Real.log_le_log (Real.exp_pos M) (show Real.exp M ≤ 1 + (R:ℝ) by linarith)
    rwa [Real.log_exp] at h
  refine ⟨R, hR1, fun N hN => ?_⟩
  have hle := dirichletEnergy_le (d := d) hd hR1 hN
  set L := Real.log (1 + (R:ℝ)) with hLdef
  have hL1 : 1 ≤ L := le_trans hM1 hLge
  have hLpos : 0 < L := by linarith
  have hbound : (18 + 16 * L) / L ^ 2 ≤ 34 / L := by
    rw [div_le_div_iff₀ (by positivity) hLpos]
    nlinarith
  have h35 : 35 / ε ≤ L := le_trans hMe hLge
  have hfin : 34 / L < ε := by
    rw [div_lt_iff₀ hLpos]
    have h1 : ε * (35 / ε) ≤ ε * L := mul_le_mul_of_nonneg_left h35 hε.le
    have h2 : ε * (35 / ε) = 35 := by field_simp
    rw [h2] at h1
    linarith
  linarith

end

end Phys

