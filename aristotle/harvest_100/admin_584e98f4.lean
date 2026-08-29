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

/-
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Brockian.Weyl.WeylLawTarget

/-- The eigenvalue counting function attached to a sequence of eigenvalues
`lam : ℕ → ℝ`: `eigCount lam Λ` is the number of indices `n` with `lam n ≤ Λ`
(counted with multiplicity, i.e. one contribution per index).

If the sub-level set is infinite the `Set.ncard` convention returns `0`; under the
discreteness hypothesis used below the sub-level sets are always finite, so this
degenerate case never occurs. -/
noncomputable def eigCount (lam : ℕ → ℝ) (Λ : ℝ) : ℕ := {n : ℕ | lam n ≤ Λ}.ncard

/-- Discreteness of the spectrum: every sub-level set of the eigenvalue sequence is finite.
This is the abstract form of "the spectrum is discrete with finite multiplicities". -/
def DiscreteSpectrum (lam : ℕ → ℝ) : Prop := ∀ Λ : ℝ, {n : ℕ | lam n ≤ Λ}.Finite

/-- The Rayleigh–variational (min–max) hypothesis, in the form it is actually used:
the eigenvalue sequence produced by the min–max (Rayleigh variational) principle is
monotone nondecreasing in the index. -/
def RayleighVariationalMonotone (lam : ℕ → ℝ) : Prop := Monotone lam

/-- **Key step.** Under discreteness and monotonicity of the eigenvalue sequence, the
counting function dominates any prescribed integer once the energy level passes the
corresponding eigenvalue. -/
theorem le_eigCount_of_le
    (lam : ℕ → ℝ) (hdisc : DiscreteSpectrum lam) (hmono : RayleighVariationalMonotone lam)
    (k : ℕ) {Λ : ℝ} (hΛ : lam k ≤ Λ) : k ≤ eigCount lam Λ := by
  have hsub : (↑(Finset.range k) : Set ℕ) ⊆ {n : ℕ | lam n ≤ Λ} := by
    intro n hn
    simp only [Finset.coe_range, Set.mem_Iio] at hn
    exact le_trans (hmono hn.le) hΛ
  have hcard : ((↑(Finset.range k) : Set ℕ)).ncard ≤ eigCount lam Λ :=
    Set.ncard_le_ncard hsub (hdisc Λ)
  simpa [Set.ncard_coe_finset] using hcard

/-- **Target.** If the spectrum is discrete (all sub-level sets of the eigenvalue sequence
are finite) and the eigenvalues are given by the Rayleigh variational (min–max) principle,
hence nondecreasing, then the eigenvalue counting function diverges to `+∞`. -/
theorem counting_diverges_of_discrete_and_rvm
    (lam : ℕ → ℝ) (hdisc : DiscreteSpectrum lam) (hrvm : RayleighVariationalMonotone lam) :
    Filter.Tendsto (eigCount lam) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.2 fun k => ⟨lam k, fun Λ hΛ => ?_⟩
  exact le_eigCount_of_le lam hdisc hrvm k hΛ

/-- The hypotheses of the target theorem are non-vacuous: the model sequence `lam n = n`
(the archetypal discrete spectrum) satisfies both of them. -/
example : DiscreteSpectrum (fun n : ℕ => (n : ℝ)) ∧
    RayleighVariationalMonotone (fun n : ℕ => (n : ℝ)) := by
  refine ⟨fun Λ => Set.Finite.subset (Set.finite_Iic ⌈Λ⌉₊) ?_,
    fun a b hab => by simpa using (Nat.cast_le (α := ℝ)).2 hab⟩
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  have : (n : ℝ) ≤ (⌈Λ⌉₊ : ℝ) := hn.trans (Nat.le_ceil Λ)
  exact Set.mem_Iic.2 (by exact_mod_cast this)

end Brockian.Weyl.WeylLawTarget

