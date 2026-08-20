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

-- (Lean requires `import` lines to precede any module doc comment.)
import Mathlib

/-!
# Chsh Tsirelson
Category: Quantum Computing
Target: QC.chsh_tsirelson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The CHSH operator `S = A₀B₀ + A₀B₁ + A₁B₀ - A₁B₁` built from a CHSH tuple
(four ±1-valued observables, with the `A`s commuting with the `B`s) inside a
C⋆-algebra satisfies Tsirelson's bound `‖S‖ ≤ 2√2`.

The algebraic half of the argument is Mathlib's `tsirelson_inequality`
(`Mathlib/Algebra/Star/CHSH.lean`), which gives the order bound
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ √2 ^ 3 • 1`.
Applying it also to the CHSH tuple `(A₀, A₁, -B₀, -B₁)` bounds `-S` as well, and for a
self-adjoint element of a C⋆-algebra a two-sided order bound gives a norm bound.
-/

namespace QC

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A C⋆-algebra is a star module over `ℝ` (via the scalar action of `ℂ`). -/
instance instStarModuleRealOfCStarAlgebra : StarModule ℝ A where
  star_smul r a := by
    rw [← algebraMap_smul ℂ r a, star_smul, star_trivial (r : ℝ)]
    rw [show star ((algebraMap ℝ ℂ) r) = (algebraMap ℝ ℂ) r by
      simp [Complex.conj_ofReal, RCLike.star_def]]
    rw [algebraMap_smul]

omit [PartialOrder A] [StarOrderedRing A] in
/-- Negating both `B` observables of a CHSH tuple again gives a CHSH tuple. -/
theorem isCHSHTuple_neg_B {A₀ A₁ B₀ B₁ : A} (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    IsCHSHTuple A₀ A₁ (-B₀) (-B₁) where
  A₀_inv := T.A₀_inv
  A₁_inv := T.A₁_inv
  B₀_inv := by simpa using T.B₀_inv
  B₁_inv := by simpa using T.B₁_inv
  A₀_sa := T.A₀_sa
  A₁_sa := T.A₁_sa
  B₀_sa := by simp [T.B₀_sa]
  B₁_sa := by simp [T.B₁_sa]
  A₀B₀_commutes := by simp [T.A₀B₀_commutes]
  A₀B₁_commutes := by simp [T.A₀B₁_commutes]
  A₁B₀_commutes := by simp [T.A₁B₀_commutes]
  A₁B₁_commutes := by simp [T.A₁B₁_commutes]

/-- For a self-adjoint element of a C⋆-algebra, a two-sided order bound by a scalar
gives the corresponding norm bound. -/
theorem norm_le_of_le_algebraMap_of_neg_le {a : A} (ha : IsSelfAdjoint a) {r : ℝ} (hr : 0 ≤ r)
    (h₁ : a ≤ algebraMap ℝ A r) (h₂ : -a ≤ algebraMap ℝ A r) : ‖a‖ ≤ r := by
  by_cases! nontriv : Nontrivial A
  · rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum ha with h | h
    · exact (le_algebraMap_iff_spectrum_le ha).mp h₁ _ h
    · have h₂' : algebraMap ℝ A (-r) ≤ a := by
        rw [map_neg, neg_le]; exact h₂
      have := (algebraMap_le_iff_le_spectrum ha).mp h₂' _ h
      linarith
  · simpa [Subsingleton.elim a 0] using hr

/-- **Tsirelson's bound**: the CHSH operator `A₀B₀ + A₀B₁ + A₁B₀ - A₁B₁` associated with a
CHSH tuple of observables in a C⋆-algebra has operator norm at most `2√2`. -/
theorem chsh_tsirelson (A₀ A₁ B₀ B₁ : A) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖ ≤ 2 * Real.sqrt 2 := by
  set S : A := A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ with hS
  have hsqrt : Real.sqrt 2 ^ 3 • (1 : A) = algebraMap ℝ A (2 * Real.sqrt 2) := by
    have : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      rw [pow_succ, h2]
    rw [this, Algebra.algebraMap_eq_smul_one]
  have hupper : S ≤ algebraMap ℝ A (2 * Real.sqrt 2) := by
    rw [← hsqrt]; exact tsirelson_inequality A₀ A₁ B₀ B₁ T
  have hlower : -S ≤ algebraMap ℝ A (2 * Real.sqrt 2) := by
    rw [← hsqrt]
    have := tsirelson_inequality A₀ A₁ (-B₀) (-B₁) (isCHSHTuple_neg_B T)
    simpa [hS, mul_neg, sub_eq_add_neg, neg_add, add_comm, add_left_comm, add_assoc] using this
  have hsa : IsSelfAdjoint S := by
    have : star S = S := by
      simp only [hS, star_sub, star_add, star_mul, T.A₀_sa, T.A₁_sa, T.B₀_sa, T.B₁_sa,
        ← T.A₀B₀_commutes, ← T.A₀B₁_commutes, ← T.A₁B₀_commutes, ← T.A₁B₁_commutes]
    exact this
  exact norm_le_of_le_algebraMap_of_neg_le hsa (by positivity) hupper hlower

end QC

