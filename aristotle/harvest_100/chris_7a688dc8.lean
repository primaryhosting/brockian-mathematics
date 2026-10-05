import Mathlib

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

import Mathlib

/-!
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Boltzmann weight of state `i` for the Hamiltonian `E - f • A`, at inverse
temperature `β` and external field `f`. -/
noncomputable def boltz (β : ℝ) (E A : ι → ℝ) (f : ℝ) (i : ι) : ℝ :=
  Real.exp (-β * (E i - f * A i))

/-- Partition function. -/
noncomputable def partition (β : ℝ) (E A : ι → ℝ) (f : ℝ) : ℝ :=
  ∑ i, boltz β E A f i

/-- Equilibrium (Gibbs) expectation value of an observable `g`. -/
noncomputable def expect (β : ℝ) (E A : ι → ℝ) (f : ℝ) (g : ι → ℝ) : ℝ :=
  (∑ i, g i * boltz β E A f i) / partition β E A f

omit [Fintype ι] [Nonempty ι] in
lemma boltz_pos (β : ℝ) (E A : ι → ℝ) (f : ℝ) (i : ι) : 0 < boltz β E A f i :=
  Real.exp_pos _

lemma partition_pos (β : ℝ) (E A : ι → ℝ) (f : ℝ) : 0 < partition β E A f :=
  Finset.sum_pos (fun i _ => boltz_pos β E A f i) Finset.univ_nonempty

omit [Fintype ι] [Nonempty ι] in
lemma hasDerivAt_boltz (β : ℝ) (E A : ι → ℝ) (f₀ : ℝ) (i : ι) :
    HasDerivAt (fun f => boltz β E A f i) (β * A i * boltz β E A f₀ i) f₀ := by
  have h : HasDerivAt (fun f : ℝ => -β * (E i - f * A i)) (β * A i) f₀ := by
    simpa using (((hasDerivAt_id f₀).mul_const (A i)).const_sub (E i)).const_mul (-β)
  simpa [boltz, mul_comm, mul_assoc, mul_left_comm] using h.exp

omit [Nonempty ι] in
lemma hasDerivAt_partition (β : ℝ) (E A : ι → ℝ) (f₀ : ℝ) :
    HasDerivAt (partition β E A) (∑ i, β * A i * boltz β E A f₀ i) f₀ := by
  have h : HasDerivAt (fun f => ∑ i, boltz β E A f i)
      (∑ i, β * A i * boltz β E A f₀ i) f₀ :=
    HasDerivAt.fun_sum (fun i _ => hasDerivAt_boltz β E A f₀ i)
  simpa [partition] using h

omit [Nonempty ι] in
lemma hasDerivAt_numerator (β : ℝ) (E A : ι → ℝ) (g : ι → ℝ) (f₀ : ℝ) :
    HasDerivAt (fun f => ∑ i, g i * boltz β E A f i)
      (∑ i, g i * (β * A i * boltz β E A f₀ i)) f₀ :=
  HasDerivAt.fun_sum (fun i _ => (hasDerivAt_boltz β E A f₀ i).const_mul (g i))

/-- **Fluctuation–dissipation theorem** (classical, static form).

For a finite classical system with unperturbed energies `E` and an observable `A`
coupled to an external field `f` (so the Hamiltonian is `E i - f * A i`), the
linear response of the equilibrium expectation value of `A` to the field, i.e.
the susceptibility `d⟨A⟩/df`, equals `β` times the equilibrium variance
`⟨A²⟩ - ⟨A⟩²` of `A`.  Dissipation (response) is thus determined by equilibrium
fluctuations. -/
theorem fluctuation_dissipation (β : ℝ) (E A : ι → ℝ) (f₀ : ℝ) :
    HasDerivAt (fun f => expect β E A f A)
      (β * (expect β E A f₀ (fun i => A i ^ 2) - (expect β E A f₀ A) ^ 2)) f₀ := by
  set Z := partition β E A f₀ with hZdef
  have hZ : Z ≠ 0 := ne_of_gt (partition_pos β E A f₀)
  have hnum := hasDerivAt_numerator β E A A f₀
  have hden := hasDerivAt_partition β E A f₀
  have hdiv := hnum.div hden hZ
  convert hdiv using 1
  have hsum1 : ∑ i, A i * (β * A i * boltz β E A f₀ i)
      = β * ∑ i, A i ^ 2 * boltz β E A f₀ i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
  have hsum2 : ∑ i, β * A i * boltz β E A f₀ i
      = β * ∑ i, A i * boltz β E A f₀ i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsum1, hsum2]
  simp only [expect, ← hZdef]
  field_simp

end Phys

