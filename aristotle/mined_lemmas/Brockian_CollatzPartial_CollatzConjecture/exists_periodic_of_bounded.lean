import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Collatz Conjecture
Category: Brockian Conjecture
Target: Brockian.CollatzPartial.CollatzConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring, so the header above is a
-- plain comment and is repeated verbatim as the module docstring below.)

import Mathlib

/-!
# Collatz Conjecture
Category: Brockian Conjecture
Target: Brockian.CollatzPartial.CollatzConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.CollatzPartial

/-- One step of the Collatz map: `n ↦ n / 2` if `n` is even, `n ↦ 3 * n + 1` if `n` is odd. -/

lemma exists_periodic_of_bounded {n : ℕ} {B : ℕ}
    (hB : ∀ k : ℕ, collatz^[k] n ≤ B) :
    ∃ (i t : ℕ), 0 < t ∧ collatz^[t] (collatz^[i] n) = collatz^[i] n := by
  -- the orbit lands in a finite set, so the iteration map is not injective
  set f : ℕ → Fin (B + 1) := fun k => ⟨collatz^[k] n, Nat.lt_succ_of_le (hB k)⟩
  obtain ⟨a, b, hab, hfab⟩ := Finite.exists_ne_map_eq_of_infinite f
  have key : ∀ a b : ℕ, a < b → collatz^[a] n = collatz^[b] n →
      ∃ (i t : ℕ), 0 < t ∧ collatz^[t] (collatz^[i] n) = collatz^[i] n := by
    intro a b hlt heq
    refine ⟨a, b - a, by omega, ?_⟩
    rw [← Function.iterate_add_apply]
    have : b - a + a = b := by omega
    rw [this, ← heq]
  have heq : collatz^[a] n = collatz^[b] n := congrArg Fin.val hfab
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b h heq
  · exact key b a h heq.symm

/--
**Collatz Conjecture (conditional reduction).**

Assuming
* `hbdd`: every positive integer has a bounded Collatz orbit (no divergent trajectory), and
* `hcyc`: the only periodic points of the Collatz map among the positive integers are
  `1`, `2`, `4` (no nontrivial cycle),

every positive integer eventually reaches `1`.

Both hypotheses are necessary conditions for the Collatz conjecture (see
`bounded_of_collatz` and `cycle_of_collatz` below), so this is an exact reduction of
the conjecture to the conjunction "no divergent orbit" ∧ "no nontrivial cycle".
-/
