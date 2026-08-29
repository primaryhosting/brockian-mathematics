/-!
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: Lean requires every `import` line to precede all other commands, while the
required header above is itself a command (a module docstring).  The development below is
therefore written against the Lean 4 core library only, with no `import` line, so that the
file both begins with the exact required header and compiles.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

/-- Primality, spelled out without Mathlib: `p ≥ 2` and the only divisors of `p` are `1` and
`p`. -/

theorem not_coversMod_of_five_le {p : Nat} (hp : 5 ≤ p) (h₀ h₁ h₂ h₃ : Int) :
    ¬ CoversMod [h₀, h₁, h₂, h₃] p := by
  intro cov
  have hpZ : (5 : Int) ≤ (p : Int) := by exact_mod_cast hp
  obtain ⟨i0, hi0, hd0⟩ := exists_index_of_covers cov 0
  obtain ⟨i1, hi1, hd1⟩ := exists_index_of_covers cov 1
  obtain ⟨i2, hi2, hd2⟩ := exists_index_of_covers cov 2
  obtain ⟨i3, hi3, hd3⟩ := exists_index_of_covers cov 3
  obtain ⟨i4, hi4, hd4⟩ := exists_index_of_covers cov 4
  -- distinct residues force distinct indices
  have key : ∀ (i j : Nat) (a b : Int), i = j →
      (p : Int) ∣ (entry h₀ h₁ h₂ h₃ i - a) → (p : Int) ∣ (entry h₀ h₁ h₂ h₃ j - b) →
      0 ≤ a → a < 5 → 0 ≤ b → b < 5 → a = b := by
    intro i j a b hij hda hdb ha0 ha hb0 hb
    subst hij
    exact eq_of_common_witness hpZ hda hdb ha0 ha hb0 hb
  have n01 : i0 ≠ i1 := fun h => by have := key _ _ _ _ h hd0 hd1 (by omega) (by omega) (by omega) (by omega); omega
  have n02 : i0 ≠ i2 := fun h => by have := key _ _ _ _ h hd0 hd2 (by omega) (by omega) (by omega) (by omega); omega
  have n03 : i0 ≠ i3 := fun h => by have := key _ _ _ _ h hd0 hd3 (by omega) (by omega) (by omega) (by omega); omega
  have n04 : i0 ≠ i4 := fun h => by have := key _ _ _ _ h hd0 hd4 (by omega) (by omega) (by omega) (by omega); omega
  have n12 : i1 ≠ i2 := fun h => by have := key _ _ _ _ h hd1 hd2 (by omega) (by omega) (by omega) (by omega); omega
  have n13 : i1 ≠ i3 := fun h => by have := key _ _ _ _ h hd1 hd3 (by omega) (by omega) (by omega) (by omega); omega
  have n14 : i1 ≠ i4 := fun h => by have := key _ _ _ _ h hd1 hd4 (by omega) (by omega) (by omega) (by omega); omega
  have n23 : i2 ≠ i3 := fun h => by have := key _ _ _ _ h hd2 hd3 (by omega) (by omega) (by omega) (by omega); omega
  have n24 : i2 ≠ i4 := fun h => by have := key _ _ _ _ h hd2 hd4 (by omega) (by omega) (by omega) (by omega); omega
  have n34 : i3 ≠ i4 := fun h => by have := key _ _ _ _ h hd3 hd4 (by omega) (by omega) (by omega) (by omega); omega
  omega

/-- Every prime other than `2` and `3` is at least `5`. -/
