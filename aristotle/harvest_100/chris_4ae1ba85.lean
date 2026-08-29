/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option grind.warning false

namespace Frontier

/-- The radical of a natural number: the product of its distinct prime factors. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

lemma rad_pos (n : ℕ) : 0 < rad n :=
  Finset.prod_pos fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos

lemma one_le_rad (n : ℕ) : (1 : ℝ) ≤ (rad n : ℝ) := by
  exact_mod_cast rad_pos n

/-- An `abc`-triple: positive coprime `a`, `b` with `a + b = c`. -/
def ABCTriple (a b c : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ a + b = c ∧ Nat.Coprime a b

/-- The set of `abc`-triples violating the bound `c ≤ rad (a * b * c) ^ (1 + ε)`. -/
def exceptionalSet (ε : ℝ) : Set (ℕ × ℕ × ℕ) :=
  {t | ABCTriple t.1 t.2.1 t.2.2 ∧
      ((rad (t.1 * t.2.1 * t.2.2) : ℝ)) ^ (1 + ε) < (t.2.2 : ℝ)}

/-- **The abc conjecture**: for every `ε > 0` there are only finitely many coprime triples
`a + b = c` of positive integers with `c > rad (a * b * c) ^ (1 + ε)`. -/
def ABCConjecture : Prop := ∀ ε : ℝ, 0 < ε → (exceptionalSet ε).Finite

/-- The "effective-shape" form of the abc conjecture: for every `ε > 0` there is a constant `K`
with `c ≤ K * rad (a * b * c) ^ (1 + ε)` for every coprime triple `a + b = c`. -/
def ABCBounded : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ a b c : ℕ, ABCTriple a b c →
    (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε)

lemma one_le_rad_rpow (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (1 : ℝ) ≤ (rad n : ℝ) ^ (1 + ε) :=
  Real.one_le_rpow (one_le_rad n) (by linarith)

/-- Finiteness of the exceptional sets implies the bounded form. -/
theorem abc_finite_imp_bounded (h : ABCConjecture) : ABCBounded := by
  intro ε hε
  classical
  set F : Finset (ℕ × ℕ × ℕ) := (h ε hε).toFinset with hF
  refine ⟨1 + ∑ t ∈ F, (t.2.2 : ℝ), ?_⟩
  intro a b c ht
  have hsum : (0 : ℝ) ≤ ∑ t ∈ F, (t.2.2 : ℝ) :=
    Finset.sum_nonneg fun t _ => by positivity
  set K : ℝ := 1 + ∑ t ∈ F, (t.2.2 : ℝ) with hK
  have hK1 : (1 : ℝ) ≤ K := by simp [hK]; linarith
  have hr : (1 : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε) := one_le_rad_rpow _ ε hε
  by_cases hex : ((rad (a * b * c) : ℝ)) ^ (1 + ε) < (c : ℝ)
  · have hmem : (a, b, c) ∈ F := by
      rw [hF, Set.Finite.mem_toFinset]
      exact ⟨ht, hex⟩
    have hcle : (c : ℝ) ≤ ∑ t ∈ F, (t.2.2 : ℝ) := by
      have := Finset.single_le_sum (f := fun t : ℕ × ℕ × ℕ => (t.2.2 : ℝ))
        (fun t _ => by positivity) hmem
      simpa using this
    calc (c : ℝ) ≤ K := by rw [hK]; linarith
      _ = K * 1 := by ring
      _ ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε) := by
          apply mul_le_mul_of_nonneg_left hr (by linarith)
  · push_neg at hex
    calc (c : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε) := hex
      _ = 1 * (rad (a * b * c) : ℝ) ^ (1 + ε) := by ring
      _ ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε) := by
          apply mul_le_mul_of_nonneg_right hK1 (by linarith)

/-- The bounded form implies finiteness of the exceptional sets. -/
theorem abc_bounded_imp_finite (h : ABCBounded) : ABCConjecture := by
  intro ε hε
  obtain ⟨K₀, hK₀⟩ := h (ε / 2) (by linarith)
  set K : ℝ := max K₀ 1 with hKdef
  have hK1 : (1 : ℝ) ≤ K := le_max_right _ _
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le one_pos hK1
  have hK : ∀ a b c : ℕ, ABCTriple a b c →
      (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε / 2) := by
    intro a b c ht
    refine le_trans (hK₀ a b c ht) ?_
    have hpos : (0 : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε / 2) := by positivity
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
  set M : ℝ := K ^ (2 / ε) with hMdef
  set N : ℕ := ⌈K * M ^ (1 + ε / 2)⌉₊ with hNdef
  apply Set.Finite.subset
    (((Set.finite_Iic N).prod ((Set.finite_Iic N).prod (Set.finite_Iic N))))
  rintro ⟨a, b, c⟩ ⟨ht, hlt⟩
  obtain ⟨ha, hb, habc, hcop⟩ := ht
  -- bound the radical
  set r : ℝ := (rad (a * b * c) : ℝ) with hrdef
  have hr1 : (1 : ℝ) ≤ r := one_le_rad (a * b * c)
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr1
  have hub : (c : ℝ) ≤ K * r ^ (1 + ε / 2) := hK a b c ⟨ha, hb, habc, hcop⟩
  have hsplit : r ^ (1 + ε) = r ^ (1 + ε / 2) * r ^ (ε / 2) := by
    rw [← Real.rpow_add hr0]; ring_nf
  have hpos2 : (0 : ℝ) < r ^ (1 + ε / 2) := Real.rpow_pos_of_pos hr0 _
  have hkey : r ^ (ε / 2) < K := by
    have : r ^ (1 + ε / 2) * r ^ (ε / 2) < K * r ^ (1 + ε / 2) := by
      rw [← hsplit]; exact lt_of_lt_of_le hlt hub
    nlinarith [hpos2]
  have hrM : r < M := by
    have h2 : (0 : ℝ) < 2 / ε := by positivity
    have := Real.rpow_lt_rpow (by positivity : (0:ℝ) ≤ r ^ (ε / 2)) hkey h2
    rw [← Real.rpow_mul (le_of_lt hr0)] at this
    have he : ε / 2 * (2 / ε) = 1 := by field_simp
    rw [he, Real.rpow_one] at this
    exact this
  have hcM : (c : ℝ) ≤ K * M ^ (1 + ε / 2) := by
    refine le_trans hub ?_
    have : r ^ (1 + ε / 2) ≤ M ^ (1 + ε / 2) :=
      Real.rpow_le_rpow (le_of_lt hr0) (le_of_lt hrM) (by linarith)
    exact mul_le_mul_of_nonneg_left this (le_of_lt hK0)
  have hcN : c ≤ N := by
    have : (⌈(c : ℝ)⌉₊ : ℕ) ≤ N := Nat.ceil_le_ceil hcM
    simpa using this
  have habc' : a + b = c := habc
  have hac : a ≤ c := by omega
  have hbc : b ≤ c := by omega
  exact ⟨le_trans hac hcN, le_trans hbc hcN, hcN⟩

/-- The exceptional sets shrink as `ε` grows. -/
lemma exceptionalSet_subset_of_le {ε ε' : ℝ} (h : ε ≤ ε') :
    exceptionalSet ε' ⊆ exceptionalSet ε := by
  rintro ⟨a, b, c⟩ ⟨ht, hlt⟩
  refine ⟨ht, lt_of_le_of_lt ?_ hlt⟩
  exact Real.rpow_le_rpow_of_exponent_le (one_le_rad _) (by linarith)

/-- It suffices to prove the abc conjecture for arbitrarily small `ε`. -/
theorem abc_of_small_eps (h : ∀ ε : ℝ, 0 < ε → ε < 1 → (exceptionalSet ε).Finite) :
    ABCConjecture := by
  intro ε hε
  rcases lt_or_ge ε 1 with hlt | hge
  · exact h ε hε hlt
  · exact Set.Finite.subset (h (1 / 2) (by norm_num) (by norm_num))
      (exceptionalSet_subset_of_le (by linarith))

/-- A concrete exceptional triple: `1 + 8 = 9` with `rad (1 * 8 * 9) = 6 < 9`. -/
lemma mem_exceptionalSet_one_eight_nine : ((1, 8, 9) : ℕ × ℕ × ℕ) ∈ exceptionalSet 0 := by
  have h72 : (1 * 8 * 9 : ℕ) = 72 := by norm_num
  have hrad : rad (1 * 8 * 9) = 6 := by
    rw [h72]
    simp [rad, Nat.primeFactors, show (72 : ℕ) = 2 ^ 3 * 3 ^ 2 by norm_num]
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by decide⟩, ?_⟩
  show ((rad (1 * 8 * 9) : ℝ)) ^ (1 + (0 : ℝ)) < ((9 : ℕ) : ℝ)
  rw [hrad]
  norm_num

/-- **The abc conjecture, reduced**: the finiteness formulation of the abc conjecture is
equivalent to the effective-shape formulation with an implied constant. -/
theorem abc_statement : ABCConjecture ↔ ABCBounded :=
  ⟨abc_finite_imp_bounded, abc_bounded_imp_finite⟩

end Frontier

