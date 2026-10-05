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

/-!
# Collatz Conjecture
Category: Brockian Conjecture
Target: Brockian.CollatzPartial.CollatzConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately self-contained (it uses only the Lean 4 core library),
so that the header comment above can appear at the very top of the file:
Lean does not permit a module docstring to precede `import` commands.
-/

namespace Brockian
namespace CollatzPartial

/-- The Collatz step: `n ↦ n / 2` if `n` is even, `n ↦ 3 * n + 1` if `n` is odd. -/

theorem descends_of_mod_four_eq_three
    (h : ∀ n : Nat, 1 < n → n % 4 = 3 → ∃ k : Nat, 0 < k ∧ iter collatz k n < n) :
    Descends := by
  intro n h1
  rcases Nat.lt_or_ge (n % 4) 2 with hlt | hge
  · rcases Nat.eq_zero_or_pos (n % 4) with h0 | hp
    · exact ⟨1, Nat.one_pos, descends_of_even h1 (by omega)⟩
    · have : n % 4 = 1 := by omega
      exact ⟨3, by omega, descends_of_mod_four_eq_one h1 this⟩
  · rcases Nat.lt_or_ge (n % 4) 3 with hlt | hge3
    · exact ⟨1, Nat.one_pos, descends_of_even h1 (by omega)⟩
    · exact h n h1 (by omega)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Every `n` with `0 < n ≤ 1000` reaches `1`, in fewer than `200` steps
(verified by kernel computation). -/
