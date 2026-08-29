import Mathlib

/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Set

namespace Frontier

open Classical in
/-- The `U`-generic colour at `n`: the colour `b` such that `{m | c n m = b} ∈ U`. -/

lemma rstep_fst_mem (c : ℕ → ℕ → Bool) (b : Bool) (p : ℕ × Set ℕ) (h : p.2.Nonempty) :
    (rstep c b p).1 ∈ p.2 := by
  classical
  simp only [rstep, dif_pos h]
  exact h.choose_spec

