import Mathlib

/-!
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
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

open Matrix

/-- The adjacency matrix (over `ℝ`) of the cycle graph `C₆`, i.e. the Hückel matrix of
benzene in units where the Coulomb integral `α = 0` and the resonance integral `β = 1`. -/

lemma C6_cos_values :
    (fun k : ℕ => 2 * Real.cos (2 * Real.pi * k / 6)) '' ((Finset.range 6 : Finset ℕ) : Set ℕ)
      = ({2, 1, -1, -2} : Set ℝ) := by
  have hset : ((Finset.range 6 : Finset ℕ) : Set ℕ) = {0, 1, 2, 3, 4, 5} := by
    ext n; simp; omega
  have h0 : 2 * Real.cos (2 * Real.pi * (0 : ℕ) / 6) = 2 := by norm_num
  have h1 : 2 * Real.cos (2 * Real.pi * (1 : ℕ) / 6) = 1 := by
    have h : 2 * Real.pi * ((1 : ℕ) : ℝ) / 6 = Real.pi / 3 := by push_cast; ring
    rw [h, Real.cos_pi_div_three]; norm_num
  have h2 : 2 * Real.cos (2 * Real.pi * (2 : ℕ) / 6) = -1 := by
    have h : 2 * Real.pi * ((2 : ℕ) : ℝ) / 6 = Real.pi - Real.pi / 3 := by push_cast; ring
    rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
  have h3 : 2 * Real.cos (2 * Real.pi * (3 : ℕ) / 6) = -2 := by
    have h : 2 * Real.pi * ((3 : ℕ) : ℝ) / 6 = Real.pi := by push_cast; ring
    rw [h, Real.cos_pi]; norm_num
  have h4 : 2 * Real.cos (2 * Real.pi * (4 : ℕ) / 6) = -1 := by
    have h : 2 * Real.pi * ((4 : ℕ) : ℝ) / 6 = Real.pi + Real.pi / 3 := by push_cast; ring
    rw [h, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_three]; ring
  have h5 : 2 * Real.cos (2 * Real.pi * (5 : ℕ) / 6) = 1 := by
    have h : 2 * Real.pi * ((5 : ℕ) : ℝ) / 6 = 2 * Real.pi - Real.pi / 3 := by push_cast; ring
    rw [h, Real.cos_two_pi_sub, Real.cos_pi_div_three]; norm_num
  rw [hset]
  simp only [Set.image_insert_eq, Set.image_singleton, h0, h1, h2, h3, h4, h5]
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- **Hückel theory for benzene (C₆H₆).**
The eigenvalues of the adjacency matrix of the cycle graph `C₆` (the Hückel matrix of benzene
with `α = 0`, `β = 1`) are exactly the numbers `2 cos (2πk/6)` for `k = 0, 1, …, 5`, namely
`2, 1, 1, -1, -1, -2`. -/
