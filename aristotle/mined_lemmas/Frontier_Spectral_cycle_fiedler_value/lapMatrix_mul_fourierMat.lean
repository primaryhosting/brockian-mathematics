import Mathlib
/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
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

namespace Frontier.Spectral

open Finset Matrix SimpleGraph

/-- The angle `2π/n` for the cycle `C_n` with `n = m + 3`. -/

lemma lapMatrix_mul_fourierMat :
    (cycleGraph (m + 3)).lapMatrix ℂ * fourierMat m
      = fourierMat m * Matrix.diagonal (fun k => ((cycEigen m k : ℝ) : ℂ)) := by
  ext j k
  have hL : ((cycleGraph (m + 3)).lapMatrix ℂ * fourierMat m) j k
      = ((cycleGraph (m + 3)).lapMatrix ℂ *ᵥ (fun i => fourierMat m i k)) j := rfl
  rw [hL, lapMatrix_cycle_mulVec, Matrix.mul_diagonal]
  set b := j.val with hb
  set c := k.val with hc
  simp only [fourierMat, fin_val_add_one, fin_val_sub_one]
  have hmod1 : cycRoot m ^ (((b + (m + 2)) % (m + 3)) * c) = cycRoot m ^ ((b + (m + 2)) * c) :=
    cycRoot_pow_congr (Nat.ModEq.mul_right c (Nat.mod_modEq _ _))
  have hmod2 : cycRoot m ^ (((b + 1) % (m + 3)) * c) = cycRoot m ^ ((b + 1) * c) :=
    cycRoot_pow_congr (Nat.ModEq.mul_right c (Nat.mod_modEq _ _))
  rw [hmod1, hmod2]
  have hu : cycRoot m ^ ((b + (m + 2)) * c) * cycRoot m ^ c = cycRoot m ^ (b * c) := by
    rw [← pow_add]
    apply cycRoot_pow_congr
    have hrw : (b + (m + 2)) * c + c = b * c + (m + 3) * c := by ring
    rw [hrw]
    simp [Nat.ModEq, Nat.add_mul_mod_self_left]
  have hsplit : cycRoot m ^ ((b + 1) * c) = cycRoot m ^ (b * c) * cycRoot m ^ c := by
    rw [← pow_add]
    congr 1
    ring
  rw [hsplit]
  have hq := cycRoot_quad (m := m) c
  rw [Complex.ofReal_mul, Complex.ofReal_ofNat] at hq
  simp only [cycEigen, ← hc, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat]
  linear_combination (cycRoot m ^ c - 2 * (Real.cos ((c : ℝ) * cycAngle m) : ℂ)) * hu
    - (cycRoot m ^ ((b + (m + 2)) * c)) * hq

