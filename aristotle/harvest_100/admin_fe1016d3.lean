/-
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


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

namespace Brockian

/-- A finite set of integers `H` (thought of as a tuple of shifts `h₁ < ⋯ < h_k`) is
*admissible* if for every prime `p` the elements of `H` do not cover all residue classes
modulo `p`; equivalently, some residue class mod `p` is missed by `H`.  This is the
classical admissibility condition from the Hardy–Littlewood prime `k`-tuple conjecture. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ a : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ a

/-- If a prime `p` exceeds the size of `H`, then `H` automatically misses a residue class
modulo `p`. -/
theorem missesResidue_of_card_lt (H : Finset ℤ) (p : ℕ) (hp : p.Prime) (hcard : H.card < p) :
    ∃ a : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ a := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h1 : (H.image (fun h : ℤ => (h : ZMod p))).card < (Finset.univ : Finset (ZMod p)).card := by
    calc (H.image (fun h : ℤ => (h : ZMod p))).card ≤ H.card := Finset.card_image_le
      _ < p := hcard
      _ = Fintype.card (ZMod p) := (ZMod.card p).symm
      _ = (Finset.univ : Finset (ZMod p)).card := by simp [Finset.card_univ]
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card h1
  refine ⟨a, ?_⟩
  intro h hh hcon
  exact ha (Finset.mem_image.2 ⟨h, hh, hcon⟩)

/-- **Admissibility criterion for `4`-tuples.**
A `4`-element set of integers is admissible (i.e. misses a residue class modulo *every*
prime) as soon as it misses a residue class modulo the primes `2` and `3`.  All larger
primes are automatically fine, since `4` integers cannot cover `p ≥ 5` residue classes. -/
theorem AdmissibilityKTupleK4 (H : Finset ℤ) (hH : H.card = 4) :
    Admissible H ↔
      ((∃ a : ZMod 2, ∀ h ∈ H, (h : ZMod 2) ≠ a) ∧ (∃ a : ZMod 3, ∀ h ∈ H, (h : ZMod 3) ≠ a)) := by
  constructor
  · intro hadm
    exact ⟨hadm 2 Nat.prime_two, hadm 3 Nat.prime_three⟩
  · rintro ⟨h2, h3⟩ p hp
    rcases eq_or_ne p 2 with rfl | hp2
    · exact h2
    rcases eq_or_ne p 3 with rfl | hp3
    · exact h3
    refine missesResidue_of_card_lt H p hp ?_
    rw [hH]
    have h2le := hp.two_le
    have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
    omega

/-- The classical admissible `4`-tuple `(0, 2, 6, 8)`. -/
theorem admissible_zero_two_six_eight : Admissible ({0, 2, 6, 8} : Finset ℤ) := by
  have hcard : ({0, 2, 6, 8} : Finset ℤ).card = 4 := by decide
  rw [AdmissibilityKTupleK4 _ hcard]
  constructor
  · exact ⟨1, by decide⟩
  · exact ⟨1, by decide⟩

/-- Tuple form of the criterion: for an injective `4`-tuple `h : Fin 4 → ℤ`, admissibility of
its range is equivalent to missing a residue class modulo `2` and modulo `3`. -/
theorem admissibilityKTupleK4_tuple (h : Fin 4 → ℤ) (hinj : Function.Injective h) :
    Admissible (Finset.image h Finset.univ) ↔
      ((∃ a : ZMod 2, ∀ i : Fin 4, (h i : ZMod 2) ≠ a) ∧
        (∃ a : ZMod 3, ∀ i : Fin 4, (h i : ZMod 3) ≠ a)) := by
  have hcard : (Finset.image h Finset.univ).card = 4 := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  rw [AdmissibilityKTupleK4 _ hcard]
  simp

/-- The `4`-tuple `(0, 1, 2, 3)` is *not* admissible: it covers both residue classes mod `2`. -/
theorem not_admissible_zero_one_two_three : ¬ Admissible ({0, 1, 2, 3} : Finset ℤ) := by
  intro hadm
  obtain ⟨a, ha⟩ := hadm 2 Nat.prime_two
  have h0 : (0 : ZMod 2) ≠ a := by simpa using ha 0 (by decide)
  have h1 : (1 : ZMod 2) ≠ a := by simpa using ha 1 (by decide)
  revert h0 h1
  decide +revert

end Brockian


