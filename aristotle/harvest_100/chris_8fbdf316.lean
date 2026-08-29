/-!
# Schur Five
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.schur_five
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace AdditiveComb

/-- The Boolean core of the argument: for any five colours `a, b, c, d, e`
(the colours of `1, 2, 3, 4, 5`), at least one of the six equations
`1 + 1 = 2`, `1 + 2 = 3`, `1 + 3 = 4`, `1 + 4 = 5`, `2 + 2 = 4`, `2 + 3 = 5`
is monochromatic. Verified by exhausting the `32` colourings. -/
private theorem schur_five_bool (a b c d e : Bool) :
    (a = a ∧ a = b) ∨ (a = b ∧ b = c) ∨ (a = c ∧ c = d) ∨ (a = d ∧ d = e) ∨
      (b = b ∧ b = d) ∨ (b = c ∧ c = e) := by
  revert a b c d e
  decide

/-- **Schur's theorem, the instance `S(2) < 5`.**

For every `2`-colouring `f` of `{1, 2, 3, 4, 5}` — encoded as `f : Fin 5 → Bool`,
where the index `i` stands for the number `i + 1` — there is a monochromatic
Schur triple: elements `x`, `y`, `z` of `{1, …, 5}` with `x + y = z` and
`f x = f y = f z`. (Here `x = y` is allowed, as in the usual definition of a
sum-free set.) -/
theorem schur_five (f : Fin 5 → Bool) :
    ∃ x y z : Fin 5, (x.val + 1) + (y.val + 1) = (z.val + 1) ∧
      f x = f y ∧ f y = f z := by
  rcases schur_five_bool (f 0) (f 1) (f 2) (f 3) (f 4) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨0, 0, 1, rfl, h1, h2⟩
  · exact ⟨0, 1, 2, rfl, h1, h2⟩
  · exact ⟨0, 2, 3, rfl, h1, h2⟩
  · exact ⟨0, 3, 4, rfl, h1, h2⟩
  · exact ⟨1, 1, 3, rfl, h1, h2⟩
  · exact ⟨1, 2, 4, rfl, h1, h2⟩

end AdditiveComb

import Mathlib
import RequestProject.SchurFive

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
set_option pp.piBinderTypes true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true

set_option grind.warning false

namespace AdditiveComb

/-- Restatement of `AdditiveComb.schur_five` for a colouring of the natural
numbers: every `2`-colouring of `{1, 2, 3, 4, 5}` admits a monochromatic
Schur triple `x + y = z` inside that interval. -/
theorem schur_five_nat (g : ℕ → Bool) :
    ∃ x ∈ Finset.Icc 1 5, ∃ y ∈ Finset.Icc 1 5, ∃ z ∈ Finset.Icc 1 5,
      x + y = z ∧ g x = g y ∧ g y = g z := by
  obtain ⟨x, y, z, hsum, hxy, hyz⟩ := schur_five (fun i : Fin 5 => g (i.val + 1))
  exact ⟨x.val + 1, by simp [Finset.mem_Icc],
    y.val + 1, by simp [Finset.mem_Icc],
    z.val + 1, by simp [Finset.mem_Icc], hsum, hxy, hyz⟩

end AdditiveComb

#print axioms AdditiveComb.schur_five
#print axioms AdditiveComb.schur_five_nat

