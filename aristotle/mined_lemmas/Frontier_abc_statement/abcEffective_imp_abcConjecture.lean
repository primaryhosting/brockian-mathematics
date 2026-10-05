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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The radical `rad n` of a natural number `n`: the product of the distinct primes
dividing `n`.  By convention `rad 0 = rad 1 = 1`. -/

theorem abcEffective_imp_abcConjecture (h : ABCEffective) : ABCConjecture := by
  intro ε hε
  obtain ⟨K, hK⟩ := h (ε / 2) (by linarith)
  set K' : ℝ := max K 1 with hK'def
  have hK1 : (1:ℝ) ≤ K' := le_max_right _ _
  have hK0 : (0:ℝ) < K' := by linarith
  have hK'' : ∀ a b c : ℕ, 0 < a → 0 < b → Nat.Coprime a b → a + b = c →
      (c : ℝ) ≤ K' * (rad (a * b * c) : ℝ) ^ (1 + ε / 2) := by
    intro a b c ha hb hab habc
    have h1 := hK a b c ha hb hab habc
    have hr1 : (1 : ℝ) ≤ (rad (a * b * c) : ℝ) := by exact_mod_cast one_le_rad _
    have hrp : (0:ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε / 2) :=
      Real.rpow_nonneg (by linarith) _
    have hKK : K ≤ K' := le_max_left _ _
    nlinarith
  set M : ℝ := K' ^ (2 / ε) with hMdef
  have hM0 : (0:ℝ) < M := Real.rpow_pos_of_pos hK0 _
  set B : ℝ := K' * M ^ (1 + ε / 2) with hBdef
  set N : ℕ := ⌈B⌉₊ + 1 with hNdef
  apply Set.Finite.subset (Finset.finite_toSet
    ((Finset.range N) ×ˢ (Finset.range N) ×ˢ (Finset.range N)))
  rintro ⟨a, b, c⟩ ⟨ha, hb, hab, habc, hexc⟩
  dsimp only at ha hb hab habc hexc
  have hr1 : (1 : ℝ) ≤ (rad (a * b * c) : ℝ) := by exact_mod_cast one_le_rad _
  have hr0 : (0 : ℝ) < (rad (a * b * c) : ℝ) := by linarith
  set r : ℝ := (rad (a * b * c) : ℝ) with hrdef
  have h2 := hK'' a b c ha hb hab habc
  have hsplit : r ^ (1 + ε) = r ^ (1 + ε / 2) * r ^ (ε / 2) := by
    rw [← Real.rpow_add hr0]; ring_nf
  have hpos : (0:ℝ) < r ^ (1 + ε / 2) := Real.rpow_pos_of_pos hr0 _
  have hlt : r ^ (ε / 2) < K' := by
    have hstep : r ^ (1 + ε / 2) * r ^ (ε / 2) < K' * r ^ (1 + ε / 2) := by
      rw [← hsplit]; linarith
    nlinarith
  have hrM : r ≤ M := by
    have hstep : (r ^ (ε / 2)) ^ (2 / ε) ≤ K' ^ (2 / ε) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _) hlt.le (by positivity)
    have hid : (r ^ (ε / 2)) ^ (2 / ε) = r := by
      rw [← Real.rpow_mul (by linarith)]
      have hee : (ε / 2) * (2 / ε) = 1 := by field_simp
      rw [hee, Real.rpow_one]
    rwa [hid] at hstep
  have hcB : (c : ℝ) ≤ B := by
    have hmono : r ^ (1 + ε / 2) ≤ M ^ (1 + ε / 2) :=
      Real.rpow_le_rpow (by linarith) hrM (by linarith)
    calc (c:ℝ) ≤ K' * r ^ (1 + ε / 2) := h2
      _ ≤ K' * M ^ (1 + ε / 2) := by nlinarith
  have hcN : c < N := by
    have h1 : (c : ℝ) ≤ (⌈B⌉₊ : ℝ) := le_trans hcB (Nat.le_ceil B)
    have h2 : c ≤ ⌈B⌉₊ := by exact_mod_cast h1
    omega
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range]
  exact ⟨by omega, by omega, hcN⟩

/-! ### The exponent `1` (that is, `ε = 0`) admits infinitely many exceptions

The triples `1 + (64 ^ m - 1) = 64 ^ m` are exceptional for `ε = 0`: since `9 ∣ 64 ^ m - 1`,
the number `64 ^ m - 1` is not squarefree, so `2 * rad (64 ^ m - 1) ≤ 64 ^ m - 1`, while
`rad (1 * (64 ^ m - 1) * 64 ^ m) = 2 * rad (64 ^ m - 1)`. -/

