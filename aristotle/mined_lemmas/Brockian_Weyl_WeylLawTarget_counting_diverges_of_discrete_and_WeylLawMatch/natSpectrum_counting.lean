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
# Counting Diverges Of Discrete And Weyl Law Match
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_WeylLawMatch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Counting Diverges Of Discrete And Weyl Law Match
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_WeylLawMatch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set

namespace Brockian.Weyl.WeylLawTarget

/-- The eigenvalue counting function of a spectrum `S ⊆ ℝ`:
`counting S Λ` is the number of points of `S` that are `≤ Λ`.
(For a set with infinitely many points below `Λ` this is `0`, by the convention for
`Set.ncard`; the `Discrete` hypothesis below rules out that degenerate case.) -/

lemma natSpectrum_counting (L : ℝ) (hL : 0 ≤ L) :
    counting (Set.range ((↑) : ℕ → ℝ)) L = ⌊L⌋₊ + 1 := by
  have hset : (Set.range ((↑) : ℕ → ℝ)) ∩ Set.Iic L
      = ((Finset.range (⌊L⌋₊ + 1)).image (fun n : ℕ => (n : ℝ)) : Finset ℝ) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_Iic, Finset.coe_image,
      Finset.coe_range, Set.mem_image, Set.mem_Iio]
    constructor
    · rintro ⟨⟨n, rfl⟩, hx⟩
      exact ⟨n, Nat.lt_succ_of_le (Nat.le_floor hx), rfl⟩
    · rintro ⟨n, hn, rfl⟩
      refine ⟨⟨n, rfl⟩, ?_⟩
      have hn' : n ≤ ⌊L⌋₊ := Nat.lt_succ_iff.mp hn
      calc (n : ℝ) ≤ (⌊L⌋₊ : ℝ) := by exact_mod_cast hn'
        _ ≤ L := Nat.floor_le hL
  rw [counting, hset, Set.ncard_coe_finset,
    Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]

/-- The model spectrum `ℕ ⊆ ℝ` is discrete. -/
