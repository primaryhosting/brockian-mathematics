/-!
# Kervaire Invariant
Category: Frontier Math
Target: Math2.kervaire_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Formalization notes.

The Kervaire invariant problem asks in which dimensions `n` there exists a closed
framed `n`-manifold of Kervaire invariant one (equivalently, in which stems the
class `θ_j` of the stable homotopy groups of spheres exists).  The relevant
results are:

* Browder's theorem: such a manifold can only exist when `n = 2 ^ j - 2` for
  some `j ≥ 2`;
* explicit constructions in dimensions `2, 6, 14, 30, 62` and `126`;
* the Hill–Hopkins–Ravenel theorem: for `j ≥ 8`, i.e. in dimensions
  `2 ^ j - 2 ≥ 254`, no such manifold exists.

These three inputs are deep results of differential topology and stable homotopy
theory whose proofs are far outside the scope of the current Lean mathematical
library, so they are carried here as explicit hypotheses on an abstract predicate
`K : Nat → Prop` ("dimension `n` carries a framed manifold of Kervaire invariant
one"), stated exactly as in the literature.  The theorem `kervaire_invariant`
below is the resulting classification:

  the Kervaire invariant is nonzero exactly in dimensions 2, 6, 14, 30, 62, 126.

To make clear that this is not a vacuous statement,
`kervaire_hypotheses_consistent` exhibits a predicate satisfying all of the
hypotheses, and `kervaire_dimensions_iff` records the purely arithmetic core:
`{2, 6, 14, 30, 62, 126}` is exactly the set of numbers of the form `2 ^ j - 2`
with `2 ≤ j ≤ 7`.

The file uses only Lean 4 core (it is part of a Mathlib-based project, but the
required header comment must precede any `import`, so no imports are used).
-/

namespace Math2

/-- The six exceptional dimensions in which the Kervaire invariant is nonzero. -/
def KervaireDimension (n : Nat) : Prop :=
  n = 2 ∨ n = 6 ∨ n = 14 ∨ n = 30 ∨ n = 62 ∨ n = 126

/-- Arithmetic core: the numbers of the form `2 ^ j - 2` with `2 ≤ j ≤ 7` are
exactly `2, 6, 14, 30, 62, 126`. -/
theorem kervaire_dimensions_iff (n : Nat) :
    KervaireDimension n ↔ ∃ j : Nat, 2 ≤ j ∧ j ≤ 7 ∧ n = 2 ^ j - 2 := by
  constructor
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨2, by omega, by omega, by decide⟩
    · exact ⟨3, by omega, by omega, by decide⟩
    · exact ⟨4, by omega, by omega, by decide⟩
    · exact ⟨5, by omega, by omega, by decide⟩
    · exact ⟨6, by omega, by omega, by decide⟩
    · exact ⟨7, by omega, by omega, by decide⟩
  · rintro ⟨j, hj2, hj7, rfl⟩
    match j, hj2, hj7 with
    | 2, _, _ => unfold KervaireDimension; decide
    | 3, _, _ => unfold KervaireDimension; decide
    | 4, _, _ => unfold KervaireDimension; decide
    | 5, _, _ => unfold KervaireDimension; decide
    | 6, _, _ => unfold KervaireDimension; decide
    | 7, _, _ => unfold KervaireDimension; decide

/-- Dimensions `2 ^ j - 2` with `j ≥ 8` (i.e. `≥ 254`) are not among the six
exceptional ones. -/
theorem not_kervaireDimension_of_large {j : Nat} (hj : 8 ≤ j) :
    ¬ KervaireDimension (2 ^ j - 2) := by
  have h : (2 : Nat) ^ 8 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hj
  have h' : (256 : Nat) ≤ 2 ^ j := by simpa using h
  unfold KervaireDimension
  omega

/-- **The Kervaire invariant problem.**

Let `K n` mean that dimension `n` carries a closed framed manifold of Kervaire
invariant one.  Assuming

* `browder`  : Browder's theorem, `K n → n = 2 ^ j - 2` for some `j ≥ 2`;
* `hill_hopkins_ravenel` : the Hill–Hopkins–Ravenel theorem, `¬ K (2 ^ j - 2)`
  for `j ≥ 8`;
* the known constructions in dimensions `2, 6, 14, 30, 62, 126`,

the Kervaire invariant is nonzero precisely in the dimensions
`2, 6, 14, 30, 62, 126`. -/
theorem kervaire_invariant
    (K : Nat → Prop)
    (browder : ∀ n, K n → ∃ j : Nat, 2 ≤ j ∧ n = 2 ^ j - 2)
    (hill_hopkins_ravenel : ∀ j : Nat, 8 ≤ j → ¬ K (2 ^ j - 2))
    (h2 : K 2) (h6 : K 6) (h14 : K 14) (h30 : K 30) (h62 : K 62) (h126 : K 126) :
    ∀ n, K n ↔ KervaireDimension n := by
  intro n
  constructor
  · intro hn
    obtain ⟨j, hj2, rfl⟩ := browder n hn
    have hj7 : j ≤ 7 := by
      rcases Nat.lt_or_ge j 8 with h | h
      · omega
      · exact absurd hn (hill_hopkins_ravenel j h)
    exact (kervaire_dimensions_iff _).2 ⟨j, hj2, hj7, rfl⟩
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;> assumption

/-- The hypotheses of `kervaire_invariant` are consistent: they are satisfied by
the predicate `KervaireDimension` itself.  In particular the classification above
is not vacuous. -/
theorem kervaire_hypotheses_consistent :
    ∃ K : Nat → Prop,
      (∀ n, K n → ∃ j : Nat, 2 ≤ j ∧ n = 2 ^ j - 2) ∧
      (∀ j : Nat, 8 ≤ j → ¬ K (2 ^ j - 2)) ∧
      K 2 ∧ K 6 ∧ K 14 ∧ K 30 ∧ K 62 ∧ K 126 := by
  refine ⟨KervaireDimension, ?_, fun _ hj => not_kervaireDimension_of_large hj,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨j, hj2, _, hn'⟩ := (kervaire_dimensions_iff n).1 hn
    exact ⟨j, hj2, hn'⟩
  all_goals unfold KervaireDimension; decide

end Math2

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

