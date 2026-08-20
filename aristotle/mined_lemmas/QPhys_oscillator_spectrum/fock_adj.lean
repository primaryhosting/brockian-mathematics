import Mathlib

/-!
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
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

namespace QPhys

open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The Hamiltonian `ℏω (a† a + ½)` of a one-dimensional quantum harmonic oscillator,
expressed through the annihilation operator `a` and the creation operator `ad = a†`. -/

lemma fock_adj (x y : FockSub) : ⟪annih x, y⟫_ℂ = ⟪x, creat y⟫_ℂ := by
  show ⟪((annih x : FockSub) : Lsp), (y : Lsp)⟫_ℂ
      = ⟪(x : Lsp), ((creat y : FockSub) : Lsp)⟫_ℂ
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum,
    tsum_eq_zero_add' (f := fun n => ⟪((x : Lsp) : ℕ → ℂ) n,
        (((creat y : FockSub) : Lsp) : ℕ → ℂ) n⟫_ℂ)
      ((summable_nat_add_iff 1).2 (lp.summable_inner (x : Lsp) ((creat y : FockSub) : Lsp)))]
  rw [show ⟪((x : Lsp) : ℕ → ℂ) 0, (((creat y : FockSub) : Lsp) : ℕ → ℂ) 0⟫_ℂ = 0 by simp]
  rw [zero_add]
  refine tsum_congr fun n => ?_
  simp only [annih_apply, creat_apply_succ, RCLike.inner_apply', map_mul, Complex.conj_ofReal]
  ring

/-- The vacuum vector `e₀`. -/
