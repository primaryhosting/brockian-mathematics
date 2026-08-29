import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
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

namespace Math2

open Filter Topology Set Polynomial

/-- The Sato–Tate density `(2/π) sin²θ` on the interval `[0, π]`. -/

lemma cheb_span_aux : ∀ (n : ℕ) (q : ℝ[X]), q.natDegree ≤ n →
    ∃ c : ℕ → ℝ, ∀ x : ℝ,
      q.eval x = ∑ m ∈ Finset.range (n + 1), c m * (Chebyshev.U ℝ m).eval x := by
  intro n
  induction n with
  | zero =>
    intro q hq
    refine ⟨fun _ => q.coeff 0, fun x => ?_⟩
    rw [Polynomial.eq_C_of_natDegree_le_zero hq]
    simp [Chebyshev.U_zero]
  | succ n ih =>
    intro q hq
    set b : ℝ := q.coeff (n + 1) / 2 ^ (n + 1) with hb
    set r : ℝ[X] := q - C b * Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ) with hr
    have hrdeg : r.natDegree ≤ n := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hr, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt hN) with heq | hlt
      · rw [← heq, cheb_coeff_top (n + 1), hb]
        field_simp
        ring
      · have h1 : q.coeff N = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq hlt)
        have h2 : (Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ)).coeff N = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          rw [Chebyshev.natDegree_U_natCast ℝ (n + 1)]
          exact hlt
        rw [h1, h2]; ring
    obtain ⟨c, hc⟩ := ih r hrdeg
    refine ⟨Function.update c (n + 1) b, fun x => ?_⟩
    rw [Finset.sum_range_succ]
    have hsum : ∑ m ∈ Finset.range (n + 1), Function.update c (n + 1) b m * (Chebyshev.U ℝ m).eval x
        = ∑ m ∈ Finset.range (n + 1), c m * (Chebyshev.U ℝ m).eval x := by
      refine Finset.sum_congr rfl fun m hm => ?_
      have hne : m ≠ n + 1 := by simp only [Finset.mem_range] at hm; omega
      rw [Function.update_of_ne hne]
    rw [hsum, ← hc x]
    have hev : r.eval x = q.eval x - b * (Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ)).eval x := by
      rw [hr]; simp
    rw [hev, Function.update_self]
    push_cast
    ring

/-- Every real polynomial is a linear combination of Chebyshev polynomials of the second kind. -/
