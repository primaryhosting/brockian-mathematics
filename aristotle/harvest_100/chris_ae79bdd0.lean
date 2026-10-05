/-
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring `/-! ... -/`, so the required
-- header appears above as a plain block comment and is repeated as a module docstring below.)

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

namespace Phys

variable {ι : Type*} [Fintype ι]

/-- Unnormalized Boltzmann weight of the microstate `i` for the canonical ensemble at inverse
temperature `β`, with unperturbed energy `E i` and the observable `A` coupled to an external
field `f` (perturbed energy `E i - f * A i`). -/
noncomputable def boltzmann (beta : ℝ) (E A : ι → ℝ) (f : ℝ) (i : ι) : ℝ :=
  Real.exp (beta * (f * A i - E i))

/-- Canonical partition function `Z(f) = ∑ i, exp (-β (E i - f * A i))`. -/
noncomputable def partition (beta : ℝ) (E A : ι → ℝ) (f : ℝ) : ℝ :=
  ∑ i, boltzmann beta E A f i

/-- Equilibrium (canonical) expectation value of an observable `O` in the field-perturbed
ensemble. -/
noncomputable def ensembleAvg (beta : ℝ) (E A : ι → ℝ) (f : ℝ) (O : ι → ℝ) : ℝ :=
  (∑ i, O i * boltzmann beta E A f i) / partition beta E A f

lemma partition_pos [Nonempty ι] (beta : ℝ) (E A : ι → ℝ) (f : ℝ) :
    0 < partition beta E A f :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

omit [Fintype ι] in
lemma hasDerivAt_boltzmann (beta : ℝ) (E A : ι → ℝ) (f : ℝ) (i : ι) :
    HasDerivAt (fun f => boltzmann beta E A f i) (beta * A i * boltzmann beta E A f i) f := by
  have h : HasDerivAt (fun f : ℝ => beta * (f * A i - E i)) (beta * A i) f := by
    simpa using (((hasDerivAt_id f).mul_const (A i)).sub_const (E i)).const_mul beta
  simpa [boltzmann, mul_comm, mul_left_comm, mul_assoc] using h.exp

lemma hasDerivAt_weighted_sum (beta : ℝ) (E A : ι → ℝ) (f : ℝ) (O : ι → ℝ) :
    HasDerivAt (fun f => ∑ i, O i * boltzmann beta E A f i)
      (beta * ∑ i, O i * A i * boltzmann beta E A f i) f := by
  have h : HasDerivAt (fun f => ∑ i, O i * boltzmann beta E A f i)
      (∑ i, O i * (beta * A i * boltzmann beta E A f i)) f :=
    by
      have h0 := HasDerivAt.sum (fun i (_ : i ∈ Finset.univ) =>
        ((hasDerivAt_boltzmann beta E A f i).const_mul (O i)))
      have hfun : (∑ i ∈ Finset.univ, fun y : ℝ => O i * boltzmann beta E A y i)
          = fun y : ℝ => ∑ i, O i * boltzmann beta E A y i := by
        funext y; simp [Finset.sum_apply]
      rwa [hfun] at h0
  refine h.congr_deriv ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- **Static fluctuation-dissipation theorem.**

For a classical system with microstates `ι`, unperturbed energies `E`, in the canonical ensemble
at inverse temperature `β`, coupled to an external field `f` through the observable `A`
(perturbed energy `E i - f * A i`), the linear response (susceptibility) of the equilibrium
average of `A` to the field equals `β` times the equilibrium variance of `A`:

`d⟨A⟩/df = β (⟨A²⟩ - ⟨A⟩²)`.

Dissipation (the response function on the left) is thus determined by the equilibrium
fluctuations (the variance on the right). -/
theorem fluctuation_dissipation [Nonempty ι] (beta : ℝ) (E A : ι → ℝ) (f : ℝ) :
    HasDerivAt (fun f => ensembleAvg beta E A f A)
      (beta * (ensembleAvg beta E A f (fun i => A i ^ 2) - (ensembleAvg beta E A f A) ^ 2)) f := by
  have hZpos := partition_pos beta E A f
  have hZ : HasDerivAt (fun f => partition beta E A f)
      (beta * ∑ i, A i * boltzmann beta E A f i) f := by
    have h := hasDerivAt_weighted_sum beta E A f (fun _ => 1)
    simpa [partition] using h
  have hN := hasDerivAt_weighted_sum beta E A f A
  have hdiv := hN.div hZ (ne_of_gt hZpos)
  refine hdiv.congr_deriv ?_
  have hsq : ∑ i, A i * A i * boltzmann beta E A f i
      = ∑ i, A i ^ 2 * boltzmann beta E A f i :=
    Finset.sum_congr rfl (fun i _ => by ring)
  rw [ensembleAvg, ensembleAvg, hsq]
  field_simp [partition]

/-- The susceptibility written with `deriv`: `d⟨A⟩/df = β (⟨A²⟩ - ⟨A⟩²)`. -/
theorem deriv_ensembleAvg [Nonempty ι] (beta : ℝ) (E A : ι → ℝ) (f : ℝ) :
    deriv (fun f => ensembleAvg beta E A f A) f
      = beta * (ensembleAvg beta E A f (fun i => A i ^ 2) - (ensembleAvg beta E A f A) ^ 2) :=
  (fluctuation_dissipation beta E A f).deriv

/-- The equilibrium variance `⟨A²⟩ - ⟨A⟩²` is nonnegative (Cauchy-Schwarz). -/
theorem ensembleVariance_nonneg [Nonempty ι] (beta : ℝ) (E A : ι → ℝ) (f : ℝ) :
    0 ≤ ensembleAvg beta E A f (fun i => A i ^ 2) - (ensembleAvg beta E A f A) ^ 2 := by
  have hZpos := partition_pos beta E A f
  have hcs : (∑ i, A i * boltzmann beta E A f i) ^ 2
      ≤ (∑ i, A i ^ 2 * boltzmann beta E A f i) * partition beta E A f :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
      (fun i _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      (fun i _ => (Real.exp_pos _).le) (fun i _ => by ring)
  have hrw : (∑ i, A i ^ 2 * boltzmann beta E A f i) / partition beta E A f
      - ((∑ i, A i * boltzmann beta E A f i) / partition beta E A f) ^ 2
      = ((∑ i, A i ^ 2 * boltzmann beta E A f i) * partition beta E A f
        - (∑ i, A i * boltzmann beta E A f i) ^ 2) / partition beta E A f ^ 2 := by
    field_simp
  rw [ensembleAvg, ensembleAvg, hrw]
  exact div_nonneg (by linarith) (by positivity)

/-- Positivity of the static response for `β ≥ 0`: the susceptibility is nonnegative. -/
theorem susceptibility_nonneg [Nonempty ι] {beta : ℝ} (hbeta : 0 ≤ beta) (E A : ι → ℝ) (f : ℝ) :
    0 ≤ deriv (fun f => ensembleAvg beta E A f A) f := by
  rw [deriv_ensembleAvg]
  exact mul_nonneg hbeta (ensembleVariance_nonneg beta E A f)

end Phys

