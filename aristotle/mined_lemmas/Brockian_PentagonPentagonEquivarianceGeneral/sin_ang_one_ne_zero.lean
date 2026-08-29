import Mathlib

/-!
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- The planar rotation matrix by an angle `t`. -/

lemma sin_ang_one_ne_zero {n : ℕ} (hn : 3 ≤ n) : Real.sin (ang n (1 : ZMod n)) ≠ 0 := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hval : ang n (1 : ZMod n) = 2 * Real.pi / (n : ℝ) := by
    simp [ang, ZMod.val_one]
  have hpos : 0 < ang n (1 : ZMod n) := by
    rw [hval]
    positivity
  have hlt : ang n (1 : ZMod n) < Real.pi := by
    rw [hval, div_lt_iff₀ hn0]
    have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [Real.pi_pos]
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpos hlt)

/-- **Equivariance for the standard representation of the regular `n`-gon** (`n ≥ 3`).
A real `2 × 2` matrix commutes with the whole standard representation of the dihedral
symmetry group of the regular `n`-gon if and only if it is a scalar matrix.  For `n = 5`
this is the pentagon (`D₅`) case. -/
