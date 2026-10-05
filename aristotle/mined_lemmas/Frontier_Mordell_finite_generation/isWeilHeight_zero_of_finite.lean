/-
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The doubling endomorphism `P ↦ 2 • P` of an additive commutative group. -/

theorem isWeilHeight_zero_of_finite [Finite A] : IsWeilHeight A (fun _ => 0) where
  translate := fun _ => ⟨0, by intro P; norm_num⟩
  double := ⟨0, by intro P; norm_num⟩
  finite_le := fun _ => Set.toFinite _

/-- A nontrivial instantiation of the descent theorem: the squared absolute value is a Weil
height on `ℤ`. -/
