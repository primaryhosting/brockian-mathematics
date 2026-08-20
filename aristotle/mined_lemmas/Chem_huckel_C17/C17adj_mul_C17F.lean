/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- block comment; the same header is repeated below as the module docstring.)

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
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

namespace Chem

open Matrix Complex

/-- The adjacency matrix of the cycle graph `C₁₇` (the Hückel matrix of the cyclic
polyene, in units where the diagonal Coulomb integral is `0` and the resonance
integral is `1`), with vertices indexed by `ZMod 17`: `i` and `j` are adjacent iff
they differ by `1`. -/

lemma C17adj_mul_C17F : C17adj * C17F = C17F * Matrix.diagonal C17eig := by
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have hne : (i - 1 : ZMod 17) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 17) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  have hiff : ∀ j : ZMod 17,
      (i - j = 1 ∨ j - i = 1) ↔ (j ∈ ({i - 1, i + 1} : Finset (ZMod 17))) := by
    intro j
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · left; linear_combination -h
      · right; linear_combination h
    · rintro (h | h)
      · left; linear_combination -h
      · right; linear_combination h
  simp only [C17adj, C17F, hiff, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_pair hne]
  have e1 : (i - 1) * k = i * k + (-k) := by ring
  have e2 : (i + 1) * k = i * k + k := by ring
  rw [e1, e2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, ← mul_add,
    add_comm (chi (-k)) (chi k), chi_add_chi_neg]

/-- Orthogonality of the additive characters of `ZMod 17`. -/
