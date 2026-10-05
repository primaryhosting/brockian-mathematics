import Mathlib

/-!
# Aleph Fixed Point Statement
Category: Frontier Wave 2 (deeper machinery)
Target: Cardinal.aleph_fixed_point_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Ordinal

/-- Every normal function on the ordinals has a fixed point above any given ordinal,
obtained as the normal fixed point (`Ordinal.nfp`) of the function at that ordinal. -/

theorem exists_ge_aleph_fixed_point (a : Ordinal) :
    ∃ o : Ordinal, a ≤ o ∧ (Cardinal.aleph o).ord = o := by
  obtain ⟨o, hao, ho⟩ := Ordinal.exists_fixed_point_of_isNormal Ordinal.isNormal_omega a
  exact ⟨o, hao, by rw [Cardinal.ord_aleph]; exact ho⟩

end Cardinal

