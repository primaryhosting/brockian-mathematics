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

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- The radical of `n`: the product of the distinct prime factors of `n`. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

/-- The set of `abc`-triples that violate the `abc` inequality with exponent `1 + ε`:
positive coprime `a, b` with `a + b = c` and `c > rad (a * b * c) ^ (1 + ε)`. -/
def abcExceptions (eps : ℝ) : Set (ℕ × ℕ × ℕ) :=
  {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ Nat.Coprime t.1 t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧
    ((rad (t.1 * t.2.1 * t.2.2) : ℝ) ^ (1 + eps) < (t.2.2 : ℝ))}

/-- The `abc` conjecture: for every `ε > 0` there are only finitely many coprime triples
`a + b = c` of positive integers with `c > rad (a * b * c) ^ (1 + ε)`. -/
def AbcConjecture : Prop := ∀ eps : ℝ, 0 < eps → (abcExceptions eps).Finite

/-- The uniformly bounded form of the `abc` conjecture: for every `ε > 0` the `c`-values of
the exceptional triples are bounded. -/
def AbcBounded : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ C : ℕ, ∀ t ∈ abcExceptions eps, t.2.2 ≤ C

/-- If the `c`-values of a set of `abc`-triples are bounded by `C`, then the set is finite,
since it is contained in the (finite) box `[0, C]³`. -/
theorem abcExceptions_finite_of_bounded (eps : ℝ) (C : ℕ)
    (h : ∀ t ∈ abcExceptions eps, t.2.2 ≤ C) : (abcExceptions eps).Finite := by
  apply Set.Finite.subset (Set.finite_Icc ((0 : ℕ), (0 : ℕ), (0 : ℕ)) (C, C, C))
  intro t ht
  have hC := h t ht
  obtain ⟨ha, hb, -, hsum, -⟩ := ht
  refine ⟨⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩, ?_, ?_, ?_⟩
  · show t.1 ≤ C
    omega
  · show t.2.1 ≤ C
    omega
  · show t.2.2 ≤ C
    omega

/-- If a set of `abc`-triples is finite, then the `c`-values occurring in it are bounded. -/
theorem abcExceptions_bounded_of_finite (eps : ℝ) (h : (abcExceptions eps).Finite) :
    ∃ C : ℕ, ∀ t ∈ abcExceptions eps, t.2.2 ≤ C := by
  classical
  obtain ⟨s, hs⟩ := h.exists_finset
  refine ⟨(s.image (fun t : ℕ × ℕ × ℕ => t.2.2)).sup id, ?_⟩
  intro t ht
  exact Finset.le_sup (f := id) (Finset.mem_image_of_mem _ ((hs t).2 ht))

/-- **Reduction for the `abc` conjecture.**

The `abc` conjecture (for every `ε > 0` there are only finitely many coprime triples
`a + b = c` of positive integers with `c > rad (a b c) ^ (1 + ε)`) is equivalent to the
statement that, for every `ε > 0`, the `c`-values of the exceptional triples are bounded.

(The `abc` conjecture itself is open; what is proved here is this equivalence, which reduces
a finiteness assertion to a uniform bound on `c`.) -/
theorem abc_statement : AbcConjecture ↔ AbcBounded := by
  constructor
  · intro h eps heps
    exact abcExceptions_bounded_of_finite eps (h eps heps)
  · intro h eps heps
    obtain ⟨C, hC⟩ := h eps heps
    exact abcExceptions_finite_of_bounded eps C hC

/-- The effective (`K_ε`) form of the `abc` conjecture: for every `ε > 0` there is a constant
`K` with `c ≤ K * rad (a * b * c) ^ (1 + ε)` for all coprime triples `a + b = c`. -/
def AbcEffective : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ K : ℝ, ∀ a b c : ℕ, 0 < a → 0 < b → Nat.Coprime a b → a + b = c →
    (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (1 + eps)

/-- The radical is positive. -/
theorem rad_pos (n : ℕ) : 0 < rad n := by
  refine Finset.prod_pos ?_
  intro p hp
  exact (Nat.prime_of_mem_primeFactors hp).pos

/-- `1 ≤ rad n` as a real number. -/
theorem one_le_rad_real (n : ℕ) : (1 : ℝ) ≤ (rad n : ℝ) := by
  exact_mod_cast rad_pos n

/-- Any nonnegative real power of a radical is at least `1`. -/
theorem one_le_rad_rpow (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : (1 : ℝ) ≤ (rad n : ℝ) ^ x :=
  Real.one_le_rpow (one_le_rad_real n) hx

/-- **Equivalence with the effective form of `abc`.**

The finiteness form of the `abc` conjecture is equivalent to the effective form asserting,
for each `ε > 0`, a constant `K_ε` with `c ≤ K_ε * rad (a b c) ^ (1 + ε)`. -/
theorem abc_iff_effective : AbcConjecture ↔ AbcEffective := by
  constructor
  · intro h eps heps
    obtain ⟨C, hC⟩ := abcExceptions_bounded_of_finite eps (h eps heps)
    refine ⟨(C : ℝ) + 1, ?_⟩
    intro a b c ha hb hab hsum
    have hK1 : (1 : ℝ) ≤ (C : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg C
      linarith
    have hr : (1 : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + eps) :=
      one_le_rad_rpow _ (by linarith)
    by_cases hex : ((rad (a * b * c) : ℝ) ^ (1 + eps) < (c : ℝ))
    · have hmem : ((a, b, c) : ℕ × ℕ × ℕ) ∈ abcExceptions eps := ⟨ha, hb, hab, hsum, hex⟩
      have : (c : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC _ hmem
      nlinarith
    · push_neg at hex
      nlinarith
  · intro h eps heps
    obtain ⟨K, hK⟩ := h (eps / 2) (by linarith)
    -- We may assume `K ≥ 1`.
    set K' : ℝ := max K 1 with hK'def
    have hK'1 : (1 : ℝ) ≤ K' := le_max_right _ _
    have hK'0 : (0 : ℝ) < K' := lt_of_lt_of_le one_pos hK'1
    have hK' : ∀ a b c : ℕ, 0 < a → 0 < b → Nat.Coprime a b → a + b = c →
        (c : ℝ) ≤ K' * (rad (a * b * c) : ℝ) ^ (1 + eps / 2) := by
      intro a b c ha hb hab hsum
      refine le_trans (hK a b c ha hb hab hsum) ?_
      have hr : (0 : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + eps / 2) :=
        le_trans zero_le_one (one_le_rad_rpow _ (by linarith))
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hr
    -- The bound on `c` for exceptional triples.
    set B : ℝ := K' * (K' ^ (2 / eps)) ^ (1 + eps / 2) with hBdef
    refine abcExceptions_finite_of_bounded eps ⌈B⌉₊ ?_
    rintro ⟨a, b, c⟩ ⟨ha, hb, hab, hsum, hex⟩
    simp only at ha hb hab hsum hex ⊢
    set r : ℝ := (rad (a * b * c) : ℝ) with hrdef
    have hr1 : (1 : ℝ) ≤ r := one_le_rad_real _
    have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr1
    have hbound := hK' a b c ha hb hab hsum
    have hsplit : r ^ (1 + eps) = r ^ (1 + eps / 2) * r ^ (eps / 2) := by
      rw [← Real.rpow_add hr0]
      ring_nf
    have hpos : (0 : ℝ) < r ^ (1 + eps / 2) := Real.rpow_pos_of_pos hr0 _
    have hlt : r ^ (1 + eps / 2) * r ^ (eps / 2) < K' * r ^ (1 + eps / 2) := by
      calc r ^ (1 + eps / 2) * r ^ (eps / 2) = r ^ (1 + eps) := hsplit.symm
        _ < (c : ℝ) := hex
        _ ≤ K' * r ^ (1 + eps / 2) := hbound
    have hrp : r ^ (eps / 2) < K' := by
      refine lt_of_mul_lt_mul_left (a := r ^ (1 + eps / 2)) ?_ hpos.le
      linarith [hlt]
    have hrle : r ≤ K' ^ (2 / eps) := by
      have h1 : (r ^ (eps / 2)) ^ (2 / eps) ≤ K' ^ (2 / eps) :=
        Real.rpow_le_rpow (le_of_lt (Real.rpow_pos_of_pos hr0 _)) hrp.le (by positivity)
      have h2 : (r ^ (eps / 2)) ^ (2 / eps) = r := by
        rw [← Real.rpow_mul hr0.le, show eps / 2 * (2 / eps) = 1 by field_simp, Real.rpow_one]
      rwa [h2] at h1
    have hcle : (c : ℝ) ≤ B := by
      refine le_trans hbound ?_
      have h3 : r ^ (1 + eps / 2) ≤ (K' ^ (2 / eps)) ^ (1 + eps / 2) :=
        Real.rpow_le_rpow hr0.le hrle (by linarith)
      exact mul_le_mul_of_nonneg_left h3 hK'0.le
    have : (c : ℝ) ≤ (⌈B⌉₊ : ℝ) := le_trans hcle (Nat.le_ceil B)
    exact_mod_cast this

/-- A sanity check on the radical: `rad (1 * 8 * 9) = 6`. -/
theorem rad_eight_nine : rad (1 * 8 * 9) = 6 := by
  simp [rad, Nat.primeFactors]

/-- The classical triple `1 + 8 = 9` is an exception at exponent `1` (i.e. `ε = 0`):
`9 > rad (1 * 8 * 9) = 6`. -/
theorem one_add_eight_mem_abcExceptions_zero : ((1 : ℕ), (8 : ℕ), (9 : ℕ)) ∈ abcExceptions 0 := by
  refine ⟨by norm_num, by norm_num, by decide, by norm_num, ?_⟩
  have : rad (1 * 8 * 9) = 6 := rad_eight_nine
  rw [this]
  norm_num

end Frontier

