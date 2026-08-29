/-!
# Aleph Fixed Point Statement
Category: Frontier Wave 2 (deeper machinery)
Target: Cardinal.aleph_fixed_point_statement
Statement: There is a fixed point of the aleph function: there exists an ordinal o such that Cardinal.aleph o = Cardinal.aleph0 raised through the normal-function fixed point, i.e. exists o, (Ordinal.toType (Cardinal.aleph o).ord) has the aleph-fixed-point property — state cleanly: the aleph function (as a normal function on ordinals) has a fixed point, exists o, Cardinal.aleph o = o-indexed value. Use Ma...
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace Ordinal

/-- Every normal function on the ordinals has a fixed point above any given ordinal,
obtained as the normal fixed point (`Ordinal.nfp`) of the function at that ordinal. -/
theorem exists_fixed_point_of_isNormal {f : Ordinal → Ordinal} (hf : Order.IsNormal f)
    (a : Ordinal) : ∃ o : Ordinal, a ≤ o ∧ f o = o :=
  ⟨nfp f a, le_nfp f a, nfp_fp hf a⟩

end Ordinal

namespace Cardinal

/-- **Aleph fixed point.** The aleph function, viewed as a normal function on the
ordinals via `Cardinal.ord`, has a fixed point: there is an ordinal `o` with
`(aleph o).ord = o`. -/
theorem aleph_fixed_point_statement : ∃ o : Ordinal, (Cardinal.aleph o).ord = o := by
  obtain ⟨o, -, ho⟩ := Ordinal.exists_fixed_point_of_isNormal Ordinal.isNormal_omega 0
  exact ⟨o, by rw [Cardinal.ord_aleph]; exact ho⟩

/-- There are arbitrarily large aleph fixed points. -/
theorem exists_ge_aleph_fixed_point (a : Ordinal) :
    ∃ o : Ordinal, a ≤ o ∧ (Cardinal.aleph o).ord = o := by
  obtain ⟨o, hao, ho⟩ := Ordinal.exists_fixed_point_of_isNormal Ordinal.isNormal_omega a
  exact ⟨o, hao, by rw [Cardinal.ord_aleph]; exact ho⟩

end Cardinal

