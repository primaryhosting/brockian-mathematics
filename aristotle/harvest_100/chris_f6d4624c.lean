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
# Counting Diverges Of Exists
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Counting Diverges Of Exists
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter

namespace Brockian.Weyl.WeylLawTarget

/-- The eigenvalue counting function of a spectrum `S ⊆ ℝ`:
`countingFunction S t` is the number of points of `S` that are `≤ t`.
(As usual for `Set.ncard`, this is `0` when `S ∩ Set.Iic t` is infinite; in the Weyl-law
setting the spectrum is locally finite, so this degenerate case does not occur.) -/
noncomputable def countingFunction (S : Set ℝ) (t : ℝ) : ℕ := (S ∩ Set.Iic t).ncard

/-- **Divergence of the counting function.**

If the spectrum `S ⊆ ℝ` is locally finite (only finitely many points below any threshold)
and there *exists* an injective sequence of points of `S` — i.e. `S` is infinite — then the
eigenvalue counting function `t ↦ #{lam ∈ S | lam ≤ t}` tends to `+∞` as `t → +∞`.

This is the unconditional form of the sub-lemma: no divergence hypothesis is assumed,
only the existence of infinitely many spectral points. -/
theorem counting_diverges_of_exists (S : Set ℝ)
    (hlf : ∀ t : ℝ, (S ∩ Set.Iic t).Finite)
    (hex : ∃ f : ℕ → ℝ, Function.Injective f ∧ ∀ n, f n ∈ S) :
    Filter.Tendsto (countingFunction S) Filter.atTop Filter.atTop := by
  obtain ⟨f, hinj, hmem⟩ := hex
  rw [Filter.tendsto_atTop_atTop]
  intro M
  -- Beyond the threshold `∑_{i < M} |f i|`, all of `f 0, …, f (M-1)` lie below `t`.
  refine ⟨∑ i ∈ Finset.range M, |f i|, fun t ht => ?_⟩
  have hsub : ((Finset.range M).image f : Set ℝ) ⊆ S ∩ Set.Iic t := by
    intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨hmem i, ?_⟩
    have h1 : |f i| ≤ ∑ j ∈ Finset.range M, |f j| :=
      Finset.single_le_sum (f := fun j => |f j|) (fun j _ => abs_nonneg _)
        (Finset.mem_range.mpr hi)
    exact ((le_abs_self (f i)).trans h1).trans ht
  have hcard : ((Finset.range M).image f).card = M := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  calc M = (((Finset.range M).image f : Finset ℝ) : Set ℝ).ncard := by
          rw [Set.ncard_coe_finset, hcard]
    _ ≤ (S ∩ Set.Iic t).ncard := Set.ncard_le_ncard hsub (hlf t)

/-- Sequence form: a locally finite spectrum enumerated by an injective sequence of
eigenvalues has a counting function diverging to `+∞`. -/
theorem counting_diverges_of_injective_eigenvalues (lam : ℕ → ℝ)
    (hinj : Function.Injective lam)
    (hlf : ∀ t : ℝ, (Set.range lam ∩ Set.Iic t).Finite) :
    Filter.Tendsto (countingFunction (Set.range lam)) Filter.atTop Filter.atTop :=
  counting_diverges_of_exists _ hlf ⟨lam, hinj, fun n => Set.mem_range_self n⟩

/-- Non-vacuity check: the hypotheses of `counting_diverges_of_exists` are satisfiable,
e.g. by the model spectrum `{0, 1, 2, …} ⊆ ℝ`. -/
example : Filter.Tendsto (countingFunction (Set.range (fun n : ℕ => (n : ℝ))))
    Filter.atTop Filter.atTop := by
  refine counting_diverges_of_injective_eigenvalues _ Nat.cast_injective (fun t => ?_)
  apply Set.Finite.subset ((Set.finite_Icc 0 ⌊t⌋₊).image (fun n : ℕ => (n : ℝ)))
  rintro x ⟨⟨n, rfl⟩, hx⟩
  exact ⟨n, ⟨Nat.zero_le n, Nat.le_floor hx⟩, rfl⟩

end Brockian.Weyl.WeylLawTarget

