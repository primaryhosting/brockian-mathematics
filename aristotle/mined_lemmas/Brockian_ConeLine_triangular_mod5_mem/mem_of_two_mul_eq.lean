import Mathlib

/-!
# Triangular Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.triangular_mod5_mem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


set_option autoImplicit false

namespace Brockian.ConeLine

/-- The `n`-th triangular number, `T n = n(n+1)/2` (natural-number division, which is
exact here since `n(n+1)` is even). -/

lemma mem_of_two_mul_eq (a b : ZMod 5) (h : 2 * a = b * (b + 1)) :
    a = 0 ∨ a = 1 ∨ a = 3 := by
  revert a b
  decide

/-- Triangular numbers land only on the residues `0, 1, 3` modulo `5`:
for every `n`, `T n = n(n+1)/2` satisfies `(T n : ZMod 5) ∈ {0, 1, 3}`. -/
