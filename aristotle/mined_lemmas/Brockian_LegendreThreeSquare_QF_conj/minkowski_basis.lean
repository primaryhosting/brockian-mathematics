import Mathlib

/-!
# Legendre's three-square theorem

A natural number `n` is a sum of three squares if and only if it is not of the
form `4 ^ a * (8 * b + 7)`.

The proof is self-contained (only core `Mathlib` is used).  The hard direction
goes through the classical route:

* Minkowski's convex body theorem shows that every positive definite integral
  ternary quadratic form of determinant one represents `1`, hence (by descent)
  is of the shape `Nᵀ * N`.
* Dirichlet's theorem on primes in arithmetic progressions together with
  quadratic reciprocity produces, for every `n` with `n % 4 ≠ 0` and
  `n % 8 ≠ 7`, an integer `m > 0` with `n ∣ m + 1` and `-n` a square modulo `m`.
  Out of these data one builds an explicit positive definite integral ternary
  form of determinant one whose `(0,0)` entry is `n`.
-/

namespace Brockian.LegendreThreeSquare

open Matrix MeasureTheory
open scoped ENNReal

/-! ## Integral quadratic forms -/

/-- The value at `v` of the quadratic form attached to the integer matrix `A`. -/

theorem minkowski_basis {k : ℕ} (b : Module.Basis (Fin k) ℝ (Fin k → ℝ))
    (S : Set (Fin k → ℝ)) (hconv : Convex ℝ S) (hsymm : ∀ x ∈ S, -x ∈ S)
    (hvol : ENNReal.ofReal |(Matrix.of ⇑b).det| * 2 ^ k < volume S) :
    ∃ c : Fin k → ℤ, c ≠ 0 ∧ ∑ i, c i • b i ∈ S := by
  classical
  have hcount : Countable ↥(Submodule.span ℤ (Set.range ⇑b)).toAddSubgroup := by
    have hsur : Function.Surjective (fun c : Fin k → ℤ => (⟨∑ i, c i • b i, by
        refine Submodule.sum_mem _ fun i _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)⟩ :
        ↥(Submodule.span ℤ (Set.range ⇑b)).toAddSubgroup)) := by
      rintro ⟨x, hx⟩
      rw [Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun] at hx
      obtain ⟨c, hc⟩ := hx
      exact ⟨c, Subtype.ext (by simpa using hc)⟩
    exact Function.Surjective.countable hsur
  have hfd : IsAddFundamentalDomain (↥(Submodule.span ℤ (Set.range ⇑b)).toAddSubgroup)
      (ZSpan.fundamentalDomain b) volume := ZSpan.isAddFundamentalDomain b volume
  have hvol' : volume (ZSpan.fundamentalDomain b) = ENNReal.ofReal |(Matrix.of ⇑b).det| :=
    ZSpan.volume_fundamentalDomain b
  have hrank : Module.finrank ℝ (Fin k → ℝ) = k := by simp
  obtain ⟨x, hx0, hxS⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hfd hsymm hconv
      (by rw [hvol', hrank]; exact hvol)
  have hxmem : (x : Fin k → ℝ) ∈ Submodule.span ℤ (Set.range ⇑b) := x.2
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hxmem
  refine ⟨c, ?_, ?_⟩
  · intro h
    apply hx0
    have hx : (x : Fin k → ℝ) = 0 := by rw [← hc, h]; simp
    exact Subtype.ext hx
  · rw [hc]; exact hxS

