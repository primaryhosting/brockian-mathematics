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
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Set

namespace Brockian.Weyl.WeylLawTarget

/-- The eigenvalue counting function of a spectrum `S ⊆ ℝ`:
`counting S T` is the number of spectral points that are `≤ T`. -/
noncomputable def counting (S : Set ℝ) (T : ℝ) : ℕ := (S ∩ Set.Iic T).ncard

/-- `S` is a *discrete spectrum*: every half-line `(-∞, T]` contains only finitely many
spectral points.  (Equivalently, the spectrum has no finite accumulation point and each
eigenvalue has finite multiplicity, so that `counting S T` is a genuine natural number.) -/
def DiscreteSpectrum (S : Set ℝ) : Prop := ∀ T : ℝ, (S ∩ Set.Iic T).Finite

/-- The conclusion supplied by the Rayleigh–Ritz variational min–max ("RVM") principle:
the variational characterisation produces an *infinite* family of eigenvalues, i.e. the
spectrum `S` is an infinite set. -/
def RayleighVariationalMinMax (S : Set ℝ) : Prop := S.Infinite

/-- **Divergence of the counting function.**  If the spectrum `S` is discrete (each half-line
`(-∞, T]` meets it in a finite set) and the Rayleigh variational min–max principle yields
infinitely many eigenvalues, then the eigenvalue counting function `T ↦ #(S ∩ (-∞, T])`
tends to `+∞` as `T → +∞`.

This is the qualitative input to a Weyl law: the counting function is unbounded, so the
asymptotics of `counting S` are asymptotics of a divergent quantity.

The proof is elementary: given `k`, the infiniteness hypothesis provides `k` distinct
spectral points (`Set.Infinite.exists_subset_card_eq`); all of them lie below some bound
`M` (`Finset.exists_le`), hence `counting S T ≥ k` for every `T ≥ M`
(`Set.ncard_le_ncard`, using discreteness for finiteness of the ambient set). -/
theorem counting_diverges_of_discrete_and_rvm (S : Set ℝ)
    (hdiscrete : DiscreteSpectrum S) (hrvm : RayleighVariationalMinMax S) :
    Tendsto (counting S) atTop atTop := by
  refine tendsto_atTop.2 (fun k => ?_)
  obtain ⟨F, hFS, hFcard⟩ := hrvm.exists_subset_card_eq k
  obtain ⟨M, hM⟩ := F.exists_le
  filter_upwards [eventually_ge_atTop M] with T hT
  have hsub : (F : Set ℝ) ⊆ S ∩ Set.Iic T := fun x hx =>
    ⟨hFS hx, le_trans (hM x (by exact_mod_cast hx)) hT⟩
  have hle := Set.ncard_le_ncard hsub (hdiscrete T)
  simpa [counting, Set.ncard_coe_finset, hFcard] using hle

/-- Non-vacuity witness: the model spectrum `{0, 1, 2, …} ⊆ ℝ` is discrete. -/
theorem discreteSpectrum_range_natCast :
    DiscreteSpectrum (Set.range (fun n : ℕ => (n : ℝ))) := by
  intro T
  apply Set.Finite.subset ((Set.finite_Iic ⌊T⌋₊).image (fun n : ℕ => (n : ℝ)))
  rintro x ⟨⟨n, rfl⟩, hx⟩
  exact ⟨n, Nat.le_floor hx, rfl⟩

/-- Non-vacuity witness: the model spectrum `{0, 1, 2, …} ⊆ ℝ` is infinite, i.e. satisfies
the conclusion of the Rayleigh variational min–max principle. -/
theorem rayleighVariationalMinMax_range_natCast :
    RayleighVariationalMinMax (Set.range (fun n : ℕ => (n : ℝ))) :=
  Set.infinite_range_of_injective (fun a b h => by exact_mod_cast h)

/-- Both hypotheses of `counting_diverges_of_discrete_and_rvm` are simultaneously
satisfiable, so the theorem is not vacuous. -/
example : Tendsto (counting (Set.range (fun n : ℕ => (n : ℝ)))) atTop atTop :=
  counting_diverges_of_discrete_and_rvm _ discreteSpectrum_range_natCast
    rayleighVariationalMinMax_range_natCast

end Brockian.Weyl.WeylLawTarget

