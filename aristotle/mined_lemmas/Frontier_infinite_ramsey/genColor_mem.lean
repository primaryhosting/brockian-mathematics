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

lemma genColor_mem (U : Ultrafilter ℕ) (c : ℕ → ℕ → Bool) (n : ℕ) :
    {m | c n m = genColor U c n} ∈ U := by
  classical
  by_cases h : {m | c n m = true} ∈ U
  · simpa [genColor, h] using h
  · have hc : {m | c n m = true}ᶜ ∈ U := Ultrafilter.compl_mem_iff_notMem.2 h
    have : {m | c n m = true}ᶜ = {m | c n m = false} := by
      ext m; simp [Bool.not_eq_true]
    rw [this] at hc
    simpa [genColor, h] using hc

open Classical in
/-- One step of the recursive construction: pick an element of the current set and shrink. -/
