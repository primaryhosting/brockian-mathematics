import Mathlib

/-!
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Auxiliary: from an orthonormal pair `a, b` we build the unit vector
`(3/5) • a + (4/5) • b`, whose inner product with `a` is `3/5`. -/

lemma norm_superposition (a b : H) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : inner ℂ a b = (0 : ℂ)) :
    ‖((3 / 5 : ℂ) • a + (4 / 5 : ℂ) • b)‖ = 1 := by
  have hba : inner ℂ b a = (0 : ℂ) := by
    rw [← inner_conj_symm, hab, map_zero]
  have haa : inner ℂ a a = (1 : ℂ) := inner_self_of_unit a ha
  have hbb : inner ℂ b b = (1 : ℂ) := inner_self_of_unit b hb
  have hself : inner ℂ ((3 / 5 : ℂ) • a + (4 / 5 : ℂ) • b)
      ((3 / 5 : ℂ) • a + (4 / 5 : ℂ) • b) = (1 : ℂ) := by
    simp only [inner_add_add_self, inner_smul_left, inner_smul_right, haa, hbb, hab, hba,
      map_div₀, Complex.conj_ofNat]
    ring
  have := norm_eq_sqrt_re_inner (𝕜 := ℂ) ((3 / 5 : ℂ) • a + (4 / 5 : ℂ) • b)
  rw [this, hself]
  norm_num

