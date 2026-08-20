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
# Counting Diverges Of Exists
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

namespace Brockian.Weyl.WeylLawTarget

/-- The eigenvalue counting function of a spectrum `S ⊆ ℝ`:
`eigenvalueCounting S lam` is the number of points of `S` that are `≤ lam`. -/
noncomputable def eigenvalueCounting (S : Set ℝ) (lam : ℝ) : ℕ :=
  (S ∩ Set.Iic lam).ncard

/-- **Weyl-law divergence of the counting function.**
If every truncation `S ∩ (-∞, lam]` of the spectrum is finite and there exists an injectively
indexed family of eigenvalues in `S` (equivalently, `S` is infinite), then the eigenvalue counting
function tends to `+∞`. -/
theorem counting_diverges_of_exists (S : Set ℝ)
    (hfin : ∀ lam : ℝ, (S ∩ Set.Iic lam).Finite)
    (hex : ∃ mu : ℕ → ℝ, Function.Injective mu ∧ ∀ n, mu n ∈ S) :
    Filter.Tendsto (eigenvalueCounting S) Filter.atTop Filter.atTop := by
  obtain ⟨mu, hinj, hmem⟩ := hex
  rw [Filter.tendsto_atTop_atTop]
  intro m
  refine ⟨∑ i ∈ Finset.range m, |mu i|, fun lam hlam => ?_⟩
  have hsub : (((Finset.range m).image mu : Finset ℝ) : Set ℝ) ⊆ S ∩ Set.Iic lam := by
    intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨hmem i, ?_⟩
    have h1 : |mu i| ≤ ∑ j ∈ Finset.range m, |mu j| :=
      Finset.single_le_sum (f := fun j => |mu j|) (fun j _ => abs_nonneg _)
        (Finset.mem_range.mpr hi)
    exact le_trans (le_trans (le_abs_self _) h1) hlam
  have hcard : ((Finset.range m).image mu).card = m := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  calc m = ((((Finset.range m).image mu : Finset ℝ) : Set ℝ)).ncard := by
          rw [Set.ncard_coe_finset, hcard]
    _ ≤ (S ∩ Set.Iic lam).ncard := Set.ncard_le_ncard hsub (hfin lam)

/-- Corollary: for a spectrum all of whose truncations are finite, infinitude of the spectrum
already forces the counting function to diverge. -/
theorem counting_diverges_of_infinite (S : Set ℝ)
    (hfin : ∀ lam : ℝ, (S ∩ Set.Iic lam).Finite) (hinf : S.Infinite) :
    Filter.Tendsto (eigenvalueCounting S) Filter.atTop Filter.atTop := by
  set e : ℕ ↪ S := Set.Infinite.natEmbedding S hinf
  refine counting_diverges_of_exists S hfin ⟨fun n => ((e n : S) : ℝ), ?_, ?_⟩
  · intro a b hab
    exact e.injective (Subtype.ext hab)
  · exact fun n => (e n).2

end Brockian.Weyl.WeylLawTarget

