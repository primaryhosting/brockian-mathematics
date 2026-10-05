import Mathlib
import RequestProject.Fock
/-!
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
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

namespace Frontier

open scoped InnerProductSpace

/-- The cyclotron frequency `ω_c = q B / m` of a particle of charge `q` and mass `m`
in a uniform magnetic field of strength `B`. -/

noncomputable def fockCore : InnerProductSpace.Core ℂ (ℕ →₀ ℂ) where
  inner := fockInner
  conj_inner_symm p q := fockInner_conj_symm p q
  re_inner_nonneg p := by
    show 0 ≤ (fockInner p p).re
    rw [fockInner_self, Complex.ofReal_re]
    exact Finset.sum_nonneg fun n _ =>
      mul_nonneg (by positivity) (Complex.normSq_nonneg _)
  add_left p q r := fockInner_add_left p q r
  smul_left p q r := fockInner_smul_left p q r
  definite p h := fockInner_definite p h

noncomputable instance : NormedAddCommGroup (ℕ →₀ ℂ) := fockCore.toNormedAddCommGroup

noncomputable instance : InnerProductSpace ℂ (ℕ →₀ ℂ) := InnerProductSpace.ofCore fockCore.toCore

