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
def PrimeNat (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- A list of integers `L` **covers** the modulus `p` when the reductions of its entries meet
every residue class modulo `p`. -/
def CoversMod (L : List Int) (p : Nat) : Prop :=
  ∀ a : Int, ∃ h ∈ L, (p : Int) ∣ (h - a)

/-- A list of integers is **admissible** (in the sense of the prime `k`-tuples conjecture) when
for every prime `p` it misses at least one residue class modulo `p`. -/
def Admissible (L : List Int) : Prop :=
  ∀ p : Nat, PrimeNat p → ¬ CoversMod L p

/-! ## Arithmetic preliminaries -/

/-- A nonzero integer of absolute value smaller than `p` is not divisible by `p`. -/
theorem eq_of_dvd_sub_of_small {p a b : Int} (hp : 5 ≤ p) (hab : (p : Int) ∣ (a - b))
    (ha0 : 0 ≤ a) (ha : a < 5) (hb0 : 0 ≤ b) (hb : b < 5) : a = b := by
  rcases Int.lt_trichotomy a b with h1 | h1 | h1
  · obtain ⟨c, hc⟩ := hab
    have hdvd : p ∣ (b - a) := ⟨-c, by rw [Int.mul_neg, ← hc]; omega⟩
    have := Int.le_of_dvd (by omega) hdvd
    omega
  · exact h1
  · have := Int.le_of_dvd (by omega) hab
    omega

/-- Two residues represented by the *same* integer, both small, coincide. -/
theorem eq_of_common_witness {p x a b : Int} (hp : 5 ≤ p) (h1 : p ∣ (x - a)) (h2 : p ∣ (x - b))
    (ha0 : 0 ≤ a) (ha : a < 5) (hb0 : 0 ≤ b) (hb : b < 5) : a = b := by
  obtain ⟨c, hc⟩ := h1
  obtain ⟨d, hd⟩ := h2
  refine eq_of_dvd_sub_of_small hp ⟨d - c, ?_⟩ ha0 ha hb0 hb
  have : a - b = p * d - p * c := by omega
  rw [this, Int.mul_sub]

/-! ## The four entries of a `4`-tuple, indexed by `Nat` -/

/-- The `i`-th entry of the `4`-tuple `(h₀, h₁, h₂, h₃)`. -/
def entry (h₀ h₁ h₂ h₃ : Int) (i : Nat) : Int :=
  if i = 0 then h₀ else if i = 1 then h₁ else if i = 2 then h₂ else h₃

/-- Covering the modulus `p` produces, for every residue, an index `i < 4` whose entry
represents it. -/
theorem exists_index_of_covers {p : Nat} {h₀ h₁ h₂ h₃ : Int}
    (cov : CoversMod [h₀, h₁, h₂, h₃] p) (a : Int) :
    ∃ i : Nat, i < 4 ∧ (p : Int) ∣ (entry h₀ h₁ h₂ h₃ i - a) := by
  obtain ⟨h, hmem, hdvd⟩ := cov a
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact ⟨0, by omega, by simpa [entry] using hdvd⟩
  · exact ⟨1, by omega, by simpa [entry] using hdvd⟩
  · exact ⟨2, by omega, by simpa [entry] using hdvd⟩
  · exact ⟨3, by omega, by simpa [entry] using hdvd⟩

/-! ## The pigeonhole step: four integers cannot cover a modulus `p ≥ 5` -/

/-- **Contrapositive form of the reduction.** A `4`-tuple never covers a modulus `p ≥ 5`:
the five residues `0, 1, 2, 3, 4` would have to be represented by only four integers. -/
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
theorem five_le_of_prime {p : Nat} (hp : PrimeNat p) (h2 : p ≠ 2) (h3 : p ≠ 3) : 5 ≤ p := by
  obtain ⟨hple, hdiv⟩ := hp
  rcases Nat.lt_or_ge p 5 with hlt | hge
  · exfalso
    have hp4 : p = 4 := by omega
    subst hp4
    rcases hdiv 2 ⟨2, rfl⟩ with h | h <;> omega
  · exact hge

/-! ## Main result -/

/-- **Admissibility for `4`-tuples.**  A tuple of four integers is admissible for the prime
`k`-tuples conjecture if and only if it fails to cover the residues modulo `2` and modulo `3`.
All larger primes are automatic: four integers can never occupy all `p ≥ 5` residue classes. -/
theorem AdmissibilityKTupleK4 (h₀ h₁ h₂ h₃ : Int) :
    Admissible [h₀, h₁, h₂, h₃] ↔
      (¬ CoversMod [h₀, h₁, h₂, h₃] 2 ∧ ¬ CoversMod [h₀, h₁, h₂, h₃] 3) := by
  constructor
  · intro hadm
    refine ⟨hadm 2 ⟨by omega, ?_⟩, hadm 3 ⟨by omega, ?_⟩⟩
    · intro d hd
      have hle := Nat.le_of_dvd (by omega) hd
      have hd0 : d ≠ 0 := by
        rintro rfl
        have := Nat.eq_zero_of_zero_dvd hd
        omega
      omega
    · intro d hd
      have hle := Nat.le_of_dvd (by omega) hd
      have hd0 : d ≠ 0 := by
        rintro rfl
        have := Nat.eq_zero_of_zero_dvd hd
        omega
      have hd2 : d ≠ 2 := by
        rintro rfl
        omega
      omega
  · rintro ⟨c2, c3⟩ p hp
    by_cases h2 : p = 2
    · subst h2; exact c2
    by_cases h3 : p = 3
    · subst h3; exact c3
    exact not_coversMod_of_five_le (five_le_of_prime hp h2 h3) h₀ h₁ h₂ h₃

/-- Sanity check: the tuple `(0, 2, 6, 8)` is admissible. -/
theorem admissible_zero_two_six_eight : Admissible [0, 2, 6, 8] := by
  rw [AdmissibilityKTupleK4]
  constructor
  · intro cov
    obtain ⟨h, hmem, hdvd⟩ := cov 1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl <;> revert hdvd <;> decide
  · intro cov
    obtain ⟨h, hmem, hdvd⟩ := cov 1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl <;> revert hdvd <;> decide

/-- Sanity check: the tuple `(0, 1, 2, 3)` is *not* admissible, since it covers the residues
modulo `2`. -/
theorem not_admissible_zero_one_two_three : ¬ Admissible [0, 1, 2, 3] := by
  intro hadm
  rw [AdmissibilityKTupleK4] at hadm
  refine hadm.1 ?_
  intro a
  by_cases h : (2 : Int) ∣ a
  · exact ⟨0, by simp, by simpa using (Int.dvd_neg).mpr h⟩
  · refine ⟨1, by simp, ?_⟩
    omega

end Brockian

