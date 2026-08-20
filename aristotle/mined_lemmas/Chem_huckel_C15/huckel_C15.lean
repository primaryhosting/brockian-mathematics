import Mathlib

/-!
# Hückel spectrum of the cycle graph `C₁₅`

The eigenvalues of the adjacency matrix of the cycle graph `C₁₅` (the Hückel spectrum of a
15-membered annulene, in units of β above α) are exactly the numbers `2 cos (2πk/15)`
for `k = 0, …, 14`.

The proof writes the adjacency matrix as `S + S¹⁴`, where `S` is the cyclic shift permutation
matrix, identifies the spectrum of `S` with the set of 15-th roots of unity, and then applies
the polynomial spectral mapping theorem over `ℂ`.
-/

namespace Chem

open Matrix Polynomial Complex

/-- The cyclic shift permutation matrix on `Fin 15`: `shift i j = 1` iff `i - 1 = j`. -/

theorem huckel_C15 :
    spectrum ℂ ((SimpleGraph.cycleGraph 15).adjMatrix ℂ) =
      Set.range fun k : Fin 15 => ((2 * Real.cos (2 * Real.pi * k / 15) : ℝ) : ℂ) := by
  have hp : (SimpleGraph.cycleGraph 15).adjMatrix ℂ = aeval shift (X + X ^ 14 : ℂ[X]) := by
    simp [adjMatrix_eq]
  have hdeg : 0 < (X + X ^ 14 : ℂ[X]).degree := by
    have h : (X + X ^ 14 : ℂ[X]).degree = 14 := by compute_degree!
    rw [h]; decide
  rw [hp, spectrum.map_polynomial_aeval_of_degree_pos shift _ hdeg, spectrum_shift]
  have hprim := Complex.isPrimitiveRoot_exp 15 (by norm_num)
  ext μ
  constructor
  · rintro ⟨ν, hν, rfl⟩
    obtain ⟨k, hk, rfl⟩ := hprim.eq_pow_of_pow_eq_one hν
    refine ⟨⟨k, hk⟩, ?_⟩
    simpa using (add_pow_fourteen_eq_two_cos k).symm
  · rintro ⟨k, rfl⟩
    refine ⟨(Complex.exp (2 * Real.pi * Complex.I / 15)) ^ (k : ℕ), ?_, ?_⟩
    · show _ ^ 15 = 1
      rw [← pow_mul, mul_comm (k : ℕ) 15, pow_mul, exp_pow_fifteen, one_pow]
    · simpa using add_pow_fourteen_eq_two_cos (k : ℕ)

end Chem

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

