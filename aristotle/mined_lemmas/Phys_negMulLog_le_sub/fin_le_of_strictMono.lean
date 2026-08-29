import Mathlib
/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` to be the very first command of a module, so the
requested header block appears immediately after the single `import Mathlib` line.
-/

open scoped BigOperators ComplexOrder
open Matrix

namespace Phys

/-! ## Elementary entropy inequalities -/

/-- Gibbs-type pointwise bound: for `x ≥ 0` and a reference weight `r > 0`,
`-x log x ≤ (r - x) - x log r`. -/

theorem fin_le_of_strictMono {n m : ℕ} {f : Fin n → Fin m} (hf : StrictMono f) (a : Fin n) :
    (a : ℕ) ≤ (f a : ℕ) := by
  obtain ⟨x, hx⟩ := a
  induction x with
  | zero => simp
  | succ y ih =>
      have hy : y < n := by omega
      have h1 : (f ⟨y, hy⟩ : ℕ) < (f ⟨y + 1, hx⟩ : ℕ) := hf (by simp [Fin.lt_def])
      have h2 := ih hy
      simp only at *
      omega

/-- Sum over a finset of `Fin N`, re-expressed along its monotone enumeration. -/
