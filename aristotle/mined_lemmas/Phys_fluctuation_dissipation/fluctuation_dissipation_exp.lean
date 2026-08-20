import Mathlib

/-!
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
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

namespace Phys

open Set MeasureTheory Filter Topology

/-!
## The classical fluctuation–dissipation relation

Let `C t = ⟨A(0) A(t)⟩` be the equilibrium autocorrelation function of an observable `A`
in a system at inverse temperature `β`.  The (classical, Kubo) fluctuation–dissipation

theorem fluctuation_dissipation_exp (β A τ : ℝ) (hτ : 0 < τ) :
    ∫ t in Ioi (0 : ℝ), (β * A / τ) * Real.exp (-t / τ) = β * A := by
  set C : ℝ → ℝ := fun t => A * Real.exp (-t / τ) with hCdef
  set C' : ℝ → ℝ := fun t => (-A / τ) * Real.exp (-t / τ) with hC'def
  have hderiv : ∀ t : ℝ, HasDerivAt C (C' t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => -t / τ) (-1 / τ) t := by
      simpa using ((hasDerivAt_neg t).div_const τ)
    have h2 := (h1.exp).const_mul A
    simpa [hCdef, hC'def, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using h2
  have hint : IntegrableOn C' (Ioi (0 : ℝ)) volume := by
    have := (exp_neg_integrableOn_Ioi (0 : ℝ) (b := 1 / τ) (by positivity))
    have h2 : IntegrableOn (fun t : ℝ => (-A / τ) * Real.exp (-(1 / τ) * t))
        (Ioi (0 : ℝ)) volume := this.const_mul _
    refine h2.congr_fun ?_ measurableSet_Ioi
    intro t _
    simp [hC'def, div_eq_mul_inv, mul_comm]
  have hlim : Tendsto C atTop (𝓝 0) := by
    have h0 : Tendsto (fun t : ℝ => t / τ) atTop atTop :=
      Filter.Tendsto.atTop_div_const hτ Filter.tendsto_id
    have h1 : Tendsto (fun t : ℝ => -t / τ) atTop atBot := by
      simpa [neg_div, Function.comp_def] using Filter.tendsto_neg_atTop_atBot.comp h0
    have := (Real.tendsto_exp_atBot.comp h1)
    simpa [hCdef] using this.const_mul A
  have hkey := fluctuation_dissipation β 0 C C' (fun t => -β * C' t)
    (Continuous.continuousWithinAt (by fun_prop))
    (fun t _ => hderiv t) hint hlim (fun _ => rfl)
  have hfun : (fun t : ℝ => (β * A / τ) * Real.exp (-t / τ))
      = fun t : ℝ => -β * C' t := by
    funext t
    simp [hC'def, div_eq_mul_inv]
    ring
  rw [hfun, hkey]
  simp [hCdef]

/-!
## The static fluctuation–dissipation relation, derived from equilibrium statistics

The results above take the fluctuation–dissipation relation `χ = -β C'` as a hypothesis and
derive its integrated (sum-rule) consequences.  Here we instead *derive* the static form of
the theorem from first principles for a finite classical system in Gibbs equilibrium:
perturbing the Hamiltonian by `-f A` and differentiating the equilibrium average `⟨A⟩_f`
with respect to the conjugate field `f`, the resulting susceptibility is exactly `β` times
the equilibrium fluctuation (variance) of `A`.
-/

section Gibbs

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Boltzmann weight of the microstate `i` at inverse temperature `β`, for the Hamiltonian
`H_f = E - f • A` obtained by coupling the observable `A` to a field `f`. -/
