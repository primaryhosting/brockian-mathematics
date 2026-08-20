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

lemma chi_sum (c : ZMod 17) : ∑ k : ZMod 17, chi (c * k) = if c = 0 then (17 : ℂ) else 0 := by
  classical
  set psi : AddChar (ZMod 17) ℂ := chi.compAddMonoidHom (AddMonoidHom.mulLeft c) with hpsi
  have hval : ∀ k : ZMod 17, psi k = chi (c * k) := by intro k; simp [hpsi]
  have hzero : psi = 0 ↔ c = 0 := by
    constructor
    · intro h
      have h1 := hval 1
      rw [h] at h1
      simp only [AddChar.zero_apply, mul_one] at h1
      have h2 : chi c = chi 0 := by rw [← h1]; simp [chi]
      exact ZMod.injective_stdAddChar (N := 17) h2
    · intro h
      ext x
      simp [hval, h, chi]
  simp only [← hval]
  rw [AddChar.sum_eq_ite]
  simp [hzero]

