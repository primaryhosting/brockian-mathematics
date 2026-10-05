/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
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

set_option grind.warning false

namespace Frontier

/-- The radical of a natural number: the product of its distinct prime factors. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

lemma one_le_rad (n : ℕ) : 1 ≤ rad n := by
  refine Finset.one_le_prod' ?_
  intro p hp
  exact (Nat.prime_of_mem_primeFactors hp).one_lt.le

lemma rad_pos (n : ℕ) : 0 < rad n := one_le_rad n

/-- The set of "exceptional" coprime pairs `(a, b)` of positive integers for the
exponent `1 + ε`: those for which `a + b > rad (a * b * (a + b)) ^ (1 + ε)`. -/
def Exceptional (ε : ℝ) : Set (ℕ × ℕ) :=
  {p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
    ((rad (p.1 * p.2 * (p.1 + p.2)) : ℝ)) ^ (1 + ε) < ((p.1 + p.2 : ℕ) : ℝ)}

/-- **The abc conjecture** (finiteness form): for every `ε > 0` there are only finitely many
coprime pairs of positive integers `a, b` with `c = a + b > rad (a * b * c) ^ (1 + ε)`. -/
def abcConjecture : Prop := ∀ ε : ℝ, 0 < ε → (Exceptional ε).Finite

/-- **The abc conjecture** (bounded form): for every `ε > 0` there is a constant `K` with
`c ≤ K * rad (a * b * c) ^ (1 + ε)` for all coprime positive `a, b` and `c = a + b`. -/
def abcBounded : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b →
    ((a + b : ℕ) : ℝ) ≤ K * ((rad (a * b * (a + b)) : ℝ)) ^ (1 + ε)

lemma exceptional_antitone {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    Exceptional ε₂ ⊆ Exceptional ε₁ := by
  rintro ⟨a, b⟩ ⟨ha, hb, hab, hlt⟩
  refine ⟨ha, hb, hab, lt_of_le_of_lt ?_ hlt⟩
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast one_le_rad (a * b * (a + b))) (by linarith)

lemma abcConjecture_of_abcBounded (h : abcBounded) : abcConjecture := by
  intro ε hε
  obtain ⟨K₀, hK₀⟩ := h (ε / 2) (by linarith)
  set K : ℝ := max K₀ 1 with hKdef
  have hK1 : (1 : ℝ) ≤ K := le_max_right _ _
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK1
  have hKb : ∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b →
      ((a + b : ℕ) : ℝ) ≤ K * ((rad (a * b * (a + b)) : ℝ)) ^ (1 + ε / 2) := by
    intro a b ha hb hab
    refine (hK₀ a b ha hb hab).trans ?_
    have hnn : (0 : ℝ) ≤ ((rad (a * b * (a + b)) : ℝ)) ^ (1 + ε / 2) :=
      Real.rpow_nonneg (by positivity) _
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
  set M : ℝ := K ^ (2 / ε) with hM
  have hM1 : (1 : ℝ) ≤ M := Real.one_le_rpow hK1 (by positivity)
  set B : ℝ := K ^ (2 : ℕ) * M with hB
  refine Set.Finite.subset ((Set.finite_Iic ⌈B⌉₊).prod (Set.finite_Iic ⌈B⌉₊)) ?_
  rintro ⟨a, b⟩ ⟨ha, hb, hab, hlt⟩
  have hr1 : (1 : ℝ) ≤ ((rad (a * b * (a + b)) : ℝ)) := by
    exact_mod_cast one_le_rad (a * b * (a + b))
  have hr0 : (0 : ℝ) < ((rad (a * b * (a + b)) : ℝ)) := lt_of_lt_of_le zero_lt_one hr1
  set r : ℝ := ((rad (a * b * (a + b)) : ℝ)) with hrdef
  have hbound := hKb a b ha hb hab
  -- split off the extra factor `r ^ (ε / 2)`
  have hsplit : r ^ (1 + ε) = r ^ (1 + ε / 2) * r ^ (ε / 2) := by
    rw [← Real.rpow_add hr0]
    ring_nf
  have ht0 : (0 : ℝ) < r ^ (1 + ε / 2) := Real.rpow_pos_of_pos hr0 _
  have hkey : r ^ (ε / 2) < K := by
    have h1 : r ^ (1 + ε / 2) * r ^ (ε / 2) < K * r ^ (1 + ε / 2) := by
      calc r ^ (1 + ε / 2) * r ^ (ε / 2) = r ^ (1 + ε) := hsplit.symm
        _ < ((a + b : ℕ) : ℝ) := hlt
        _ ≤ K * r ^ (1 + ε / 2) := hbound
    nlinarith [ht0, h1]
  have hrM : r < M := by
    have hpos : (0 : ℝ) < 2 / ε := by positivity
    have := Real.rpow_lt_rpow (Real.rpow_nonneg hr0.le _) hkey hpos
    rwa [← Real.rpow_mul hr0.le, div_mul_div_comm, mul_comm ε 2,
      div_self (by positivity : (2 : ℝ) * ε ≠ 0), Real.rpow_one] at this
  have hr2 : (0 : ℝ) ≤ r ^ (ε / 2) := (Real.rpow_pos_of_pos hr0 _).le
  have hnB : ((a + b : ℕ) : ℝ) ≤ B := by
    have hsplit2 : r ^ (1 + ε / 2) = r * r ^ (ε / 2) := by
      simpa using Real.rpow_add hr0 1 (ε / 2)
    have : ((a + b : ℕ) : ℝ) ≤ K * (r * r ^ (ε / 2)) := by rwa [hsplit2] at hbound
    have hstep : K * (r * r ^ (ε / 2)) ≤ K * (M * K) := by
      have := mul_le_mul hrM.le hkey.le hr2 (by linarith)
      nlinarith [hK0.le, this]
    have hBeq : K * (M * K) = B := by rw [hB]; ring
    linarith [this, hstep, hBeq.le, hBeq.ge]
  have hceil : ((a + b : ℕ) : ℝ) ≤ (⌈B⌉₊ : ℝ) := hnB.trans (Nat.le_ceil B)
  have hle : a + b ≤ ⌈B⌉₊ := by exact_mod_cast hceil
  exact ⟨Set.mem_Iic.mpr (le_trans (Nat.le_add_right a b) hle),
    Set.mem_Iic.mpr (le_trans (Nat.le_add_left b a) hle)⟩

lemma abcBounded_of_abcConjecture (h : abcConjecture) : abcBounded := by
  intro ε hε
  have hS := h ε hε
  set f : ℕ × ℕ → ℝ := fun p => ((p.1 + p.2 : ℕ) : ℝ) /
      ((rad (p.1 * p.2 * (p.1 + p.2)) : ℝ)) ^ (1 + ε) with hf
  have hfnonneg : ∀ p : ℕ × ℕ, 0 ≤ f p := by
    intro p
    exact div_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  refine ⟨1 + ∑ p ∈ hS.toFinset, f p, ?_⟩
  intro a b ha hb hab
  have hsum : 0 ≤ ∑ p ∈ hS.toFinset, f p := Finset.sum_nonneg fun p _ => hfnonneg p
  have hrpos : (0 : ℝ) < ((rad (a * b * (a + b)) : ℝ)) ^ (1 + ε) :=
    Real.rpow_pos_of_pos (by exact_mod_cast rad_pos _) _
  by_cases hmem : (a, b) ∈ Exceptional ε
  · have hle : f (a, b) ≤ ∑ p ∈ hS.toFinset, f p :=
      Finset.single_le_sum (fun p _ => hfnonneg p) (hS.mem_toFinset.mpr hmem)
    have hle2 : f (a, b) ≤ 1 + ∑ p ∈ hS.toFinset, f p := by linarith
    simp only [hf] at hle2
    exact (div_le_iff₀ hrpos).mp hle2
  · have hnot : ¬ (((rad (a * b * (a + b)) : ℝ)) ^ (1 + ε) < ((a + b : ℕ) : ℝ)) := by
      intro hlt
      exact hmem ⟨ha, hb, hab, hlt⟩
    push_neg at hnot
    nlinarith [hnot, hrpos, hsum]

/-- A Lean-checked reduction for the abc conjecture: the finiteness form of the conjecture
(finitely many exceptional coprime triples `a + b = c` with `c > rad (abc) ^ (1 + ε)`)
is equivalent to the effective form (for each `ε > 0` a uniform constant `K` with
`c ≤ K * rad (abc) ^ (1 + ε)`).  Together with the monotonicity of the exceptional sets in
`ε`, this is the standard reduction between the two usual formulations. -/
theorem abc_statement :
    (abcConjecture ↔ abcBounded) ∧
      (∀ ε₁ ε₂ : ℝ, ε₁ ≤ ε₂ → Exceptional ε₂ ⊆ Exceptional ε₁) :=
  ⟨⟨abcBounded_of_abcConjecture, abcConjecture_of_abcBounded⟩,
    fun _ _ h => exceptional_antitone h⟩

/-- The base case `ε = 0` genuinely has exceptions: `1 + 8 = 9 > 6 = rad (1 * 8 * 9)`. -/
theorem one_eight_mem_exceptional_zero : (1, 8) ∈ Exceptional (0 : ℝ) := by
  have hr : rad (1 * 8 * (1 + 8)) = 6 := by simp [rad, Nat.primeFactors]
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  simp only [hr]
  norm_num

end Frontier

