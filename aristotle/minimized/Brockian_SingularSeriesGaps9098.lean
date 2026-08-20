/-
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment because Lean 4 does not permit a module
-- docstring before `import`; the same header is repeated as a module docstring below.)


import Mathlib

/-!
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
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

/-- A finite set `H` of integers is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture: the singular series `𝔖(H)` is nonzero exactly for such `H`)
if for every prime `p` the reductions of the elements of `H` modulo `p` miss at least one
residue class. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- For a prime `p` strictly larger than the size of `H`, the residues of `H` modulo `p`
cannot cover all of `ZMod p`; this is the pigeonhole half of admissibility. -/
theorem exists_missed_residue_of_card_lt (H : Finset ℤ) (p : ℕ) [Fact p.Prime]
    (hp : H.card < p) : ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r := by
  by_contra hcon
  push_neg at hcon
  -- if no residue is missed, the cast map from `H` is onto `ZMod p`
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun h : ℤ => (h : ZMod p)) := by
    intro r _
    obtain ⟨h, hh, hr⟩ := hcon r
    exact Finset.mem_image.2 ⟨h, hh, hr⟩
  have hcard : p ≤ H.card := by
    have h1 : (Finset.univ : Finset (ZMod p)).card ≤ (H.image fun h : ℤ => (h : ZMod p)).card :=
      Finset.card_le_card hsub
    have h2 : (H.image fun h : ℤ => (h : ZMod p)).card ≤ H.card := Finset.card_image_le
    have h3 : (Finset.univ : Finset (ZMod p)).card = p := by
      simp [ZMod.card]
    omega
  omega

/-- `0 ≠ 1` in `ZMod 2`. -/
theorem zmod_two_zero_ne_one : (0 : ZMod 2) ≠ 1 := by decide

/-- Every pair `{0, d}` with `d` even is admissible: modulo `2` both entries are `0`,
and for odd `p` the pigeonhole bound applies. -/
theorem admissible_pair_of_even (d : ℤ) (hd : Even d) : Admissible {0, d} := by
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne p 2 with rfl | hp2
  · refine ⟨1, ?_⟩
    intro h hh
    have hh' : h = 0 ∨ h = d := by simpa using hh
    have hzero : ((d : ℤ) : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd d 2).2 (by exact_mod_cast hd.two_dvd)
    rcases hh' with rfl | rfl
    · simp
    · rw [hzero]
      exact zmod_two_zero_ne_one
  · have hcard : ({0, d} : Finset ℤ).card < p := by
      have h1 : ({0, d} : Finset ℤ).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
      have h2 : 2 ≤ p := hp.two_le
      have h3 : p ≠ 2 := hp2
      omega
    exact exists_missed_residue_of_card_lt _ p hcard

/-- The tuple `{0, 2, 6, 8, 9098}` misses the residue `1` modulo `2`. -/
theorem tuple_ne_one_mod_two (h : ℤ) (hh : h = 0 ∨ h = 2 ∨ h = 6 ∨ h = 8 ∨ h = 9098) :
    (h : ZMod 2) ≠ 1 := by
  rcases hh with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The tuple `{0, 2, 6, 8, 9098}` misses the residue `1` modulo `3`. -/
theorem tuple_ne_one_mod_three (h : ℤ) (hh : h = 0 ∨ h = 2 ∨ h = 6 ∨ h = 8 ∨ h = 9098) :
    (h : ZMod 3) ≠ 1 := by
  rcases hh with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The tuple `{0, 2, 6, 8, 9098}` misses the residue `4` modulo `5`. -/
theorem tuple_ne_four_mod_five (h : ℤ) (hh : h = 0 ∨ h = 2 ∨ h = 6 ∨ h = 8 ∨ h = 9098) :
    (h : ZMod 5) ≠ 4 := by
  rcases hh with rfl | rfl | rfl | rfl | rfl <;> decide

/-- **Singular Series Gaps 9098.**

`(a)` every even gap `d` gives an admissible pair `{0, d}` — in particular the gap `9098`;
`(b)` the `5`-tuple `{0, 2, 6, 8, 9098}` is admissible, so it is a new admissible gap range:
its residues miss `1 mod 2`, `1 mod 3`, `4 mod 5`, and pigeonhole covers all primes `p ≥ 7`.

Mathlib ingredients used: `Finset.card_le_card`, `Finset.card_image_le` and `ZMod.card`
for the pigeonhole step, and `ZMod.intCast_zmod_eq_zero_iff_dvd` for the even-gap step. -/
theorem SingularSeriesGaps9098 :
    (∀ d : ℤ, Even d → Admissible {0, d}) ∧
      Admissible ({0, 9098} : Finset ℤ) ∧
      Admissible ({0, 2, 6, 8, 9098} : Finset ℤ) := by
  refine ⟨admissible_pair_of_even, admissible_pair_of_even 9098 ⟨4549, by norm_num⟩, ?_⟩
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  have hmem : ∀ h ∈ ({0, 2, 6, 8, 9098} : Finset ℤ),
      h = 0 ∨ h = 2 ∨ h = 6 ∨ h = 8 ∨ h = 9098 := by
    intro h hh
    simpa using hh
  by_cases hlt : ({0, 2, 6, 8, 9098} : Finset ℤ).card < p
  · exact exists_missed_residue_of_card_lt _ p hlt
  · -- `p ≤ 5`, so `p ∈ {2, 3, 5}`
    have hcard : ({0, 2, 6, 8, 9098} : Finset ℤ).card = 5 := by decide
    have hple : p ≤ 5 := by omega
    have h2le : 2 ≤ p := hp.two_le
    interval_cases p
    · exact ⟨1, fun h hh => tuple_ne_one_mod_two h (hmem h hh)⟩
    · exact ⟨1, fun h hh => tuple_ne_one_mod_three h (hmem h hh)⟩
    · exact absurd hp (by norm_num)
    · exact ⟨4, fun h hh => tuple_ne_four_mod_five h (hmem h hh)⟩

end Brockian

