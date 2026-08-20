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
theorem states that the linear response function to a perturbation `-f(t) A` is

  `χ(t) = -β * dC/dt (t)`   for `t > 0`.

Everything below is stated for an arbitrary correlation function `C` with derivative `C'`,
with the fluctuation–dissipation relation `χ = -β C'` imposed as a hypothesis; the content
of the results is the *sum rule* obtained by integrating the relation, i.e. the statement
that the static (zero-frequency) susceptibility is `β` times the equal-time fluctuation.
-/

/-- **Finite-time fluctuation–dissipation sum rule.**

If the response function `χ` is related to the equilibrium autocorrelation function `C`
by the fluctuation–dissipation relation `χ t = -β * C' t` (with `C'` the derivative of `C`),
then the response integrated up to time `T` measures the decay of the correlation:

`∫_0^T χ(t) dt = β * (C 0 - C T)`. -/
theorem fluctuation_dissipation_interval
    (β T : ℝ) (C C' χ : ℝ → ℝ)
    (hC : ∀ t ∈ uIcc (0 : ℝ) T, HasDerivAt C (C' t) t)
    (hC'int : IntervalIntegrable C' volume 0 T)
    (hχ : ∀ t, χ t = -β * C' t) :
    ∫ t in (0 : ℝ)..T, χ t = β * (C 0 - C T) := by
  have h : ∫ t in (0 : ℝ)..T, χ t = ∫ t in (0 : ℝ)..T, -β * C' t := by
    simp only [hχ]
  rw [h, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hC hC'int]
  ring

/-- **Fluctuation–dissipation theorem (static susceptibility sum rule).**

Let `C` be the equilibrium autocorrelation function `C t = ⟨A(0) A(t)⟩` of an observable
of a system at inverse temperature `β`, with derivative `C'` on `(0, ∞)`, and let
`χ` be the linear response (after-effect) function, related to `C` by the classical
fluctuation–dissipation relation `χ t = -β * C' t`.

If the correlations decay to `Cinf` at large times and `C'` is integrable, then the
static susceptibility -- the total integrated response -- equals `β` times the
equilibrium fluctuation `C 0 - Cinf`:

`∫_0^∞ χ(t) dt = β * (C 0 - Cinf)`.

In particular, when the correlations decay to zero (`Cinf = 0`), the dissipative
response `∫_0^∞ χ` is `β = 1 / (k_B T)` times the equal-time fluctuation `⟨A²⟩ = C 0`. -/
theorem fluctuation_dissipation
    (β Cinf : ℝ) (C C' χ : ℝ → ℝ)
    (hC0 : ContinuousWithinAt C (Ici (0 : ℝ)) 0)
    (hC : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt C (C' t) t)
    (hC'int : IntegrableOn C' (Ioi (0 : ℝ)) volume)
    (hCinf : Tendsto C atTop (𝓝 Cinf))
    (hχ : ∀ t, χ t = -β * C' t) :
    ∫ t in Ioi (0 : ℝ), χ t = β * (C 0 - Cinf) := by
  have h : ∫ t in Ioi (0 : ℝ), χ t = ∫ t in Ioi (0 : ℝ), -β * C' t := by
    simp only [hχ]
  rw [h, integral_const_mul,
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hC0 hC hC'int hCinf]
  ring

/-- A concrete instance of the fluctuation–dissipation sum rule: for an exponentially
decaying correlation function `C t = A * exp (-t / τ)` (`τ > 0`), the response function
prescribed by the fluctuation–dissipation relation is `χ t = (β * A / τ) * exp (-t / τ)`,
and its total integral is `β * A = β * C 0`, i.e. `β` times the equal-time fluctuation. -/
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
noncomputable def gibbsWeight (β : ℝ) (E A : ι → ℝ) (f : ℝ) (i : ι) : ℝ :=
  Real.exp (-β * (E i - f * A i))

/-- The partition function `Z(f) = ∑ᵢ exp (-β (Eᵢ - f Aᵢ))`. -/
noncomputable def gibbsPartition (β : ℝ) (E A : ι → ℝ) (f : ℝ) : ℝ :=
  ∑ i, gibbsWeight β E A f i

/-- The equilibrium (Gibbs) average `⟨g⟩_f` of an observable `g` in the field `f`. -/
noncomputable def gibbsAvg (β : ℝ) (E A : ι → ℝ) (f : ℝ) (g : ι → ℝ) : ℝ :=
  (∑ i, g i * gibbsWeight β E A f i) / gibbsPartition β E A f

omit [Fintype ι] [Nonempty ι] in
lemma hasDerivAt_gibbsWeight (β : ℝ) (E A : ι → ℝ) (f : ℝ) (i : ι) :
    HasDerivAt (fun f => gibbsWeight β E A f i) (β * A i * gibbsWeight β E A f i) f := by
  have h1 : HasDerivAt (fun f : ℝ => -β * (E i - f * A i)) (β * A i) f := by
    have h := (((hasDerivAt_id f).mul_const (A i)).const_sub (E i)).const_mul (-β)
    simpa using h.congr_deriv (by ring)
  simpa [gibbsWeight, mul_comm] using h1.exp

lemma gibbsPartition_pos (β : ℝ) (E A : ι → ℝ) (f : ℝ) : 0 < gibbsPartition β E A f :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- **Static fluctuation–dissipation theorem.**  For a finite classical system in Gibbs
equilibrium at inverse temperature `β`, with the observable `A` coupled to a field `f`
(Hamiltonian `E - f A`), the susceptibility `d⟨A⟩_f / df` equals `β` times the equilibrium
fluctuation `⟨A²⟩_f - ⟨A⟩_f²` of `A`.  This is the fluctuation–dissipation relation itself,
derived rather than assumed. -/
theorem susceptibility_eq_beta_mul_variance (β : ℝ) (E A : ι → ℝ) (f : ℝ) :
    HasDerivAt (fun f => gibbsAvg β E A f A)
      (β * (gibbsAvg β E A f (fun i => A i ^ 2) - (gibbsAvg β E A f A) ^ 2)) f := by
  have hZ : HasDerivAt (gibbsPartition β E A) (∑ i, β * A i * gibbsWeight β E A f i) f := by
    have h := HasDerivAt.fun_sum
      (fun (i : ι) (_ : i ∈ (Finset.univ : Finset ι)) => hasDerivAt_gibbsWeight β E A f i)
    simpa [gibbsPartition] using h
  have hN : HasDerivAt (fun f => ∑ i, A i * gibbsWeight β E A f i)
      (∑ i, A i * (β * A i * gibbsWeight β E A f i)) f :=
    HasDerivAt.fun_sum (fun i _ => (hasDerivAt_gibbsWeight β E A f i).const_mul (A i))
  have hZne : gibbsPartition β E A f ≠ 0 := (gibbsPartition_pos β E A f).ne'
  refine (hN.div hZ hZne).congr_deriv ?_
  have e1 : ∑ i, A i * (β * A i * gibbsWeight β E A f i)
      = β * ∑ i, A i ^ 2 * gibbsWeight β E A f i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, β * A i * gibbsWeight β E A f i = β * ∑ i, A i * gibbsWeight β E A f i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  simp only [gibbsAvg, e1, e2]
  field_simp

/-- The static fluctuation–dissipation relation in `deriv` form: the zero-field static
susceptibility is `β` times the equilibrium variance of `A`. -/
theorem deriv_gibbsAvg_zero (β : ℝ) (E A : ι → ℝ) :
    deriv (fun f => gibbsAvg β E A f A) 0
      = β * (gibbsAvg β E A 0 (fun i => A i ^ 2) - (gibbsAvg β E A 0 A) ^ 2) :=
  (susceptibility_eq_beta_mul_variance β E A 0).deriv

end Gibbs

end Phys

