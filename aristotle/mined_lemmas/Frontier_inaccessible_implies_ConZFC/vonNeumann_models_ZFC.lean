import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

universe u

namespace Frontier

open FirstOrder Language ZFSet Ordinal Cardinal Order Set

/-! ## Cardinal arithmetic of the von Neumann hierarchy below an inaccessible -/

variable {κ : Cardinal.{u}}

/-- Below an inaccessible cardinal `κ`, all the beth-numbers are smaller than `κ`. -/

theorem vonNeumann_models_ZFC (hκ : κ.IsInaccessible) :
    (vonNeumann κ.ord : Type (u+1)) ⊨ ZFC := by
  have hA : (vonNeumann κ.ord).IsTransitive := isTransitive_vonNeumann _
  have hsep : ∀ p : ZFSet.{u} → Prop, ∀ x ∈ vonNeumann κ.ord, ZFSet.sep p x ∈ vonNeumann κ.ord :=
    fun p x hx => sep_mem_vonNeumann p hx
  have hrange : ∀ x ∈ vonNeumann κ.ord, ∀ f : ↥x → ZFSet.{u},
      (∀ i, f i ∈ vonNeumann κ.ord) → ZFSet.range f ∈ vonNeumann κ.ord :=
    fun x hx f hf => range_mem_vonNeumann hκ hx f hf
  refine (Theory.model_iff _).mpr ?_
  rintro s ((hs | ⟨⟨k, φ⟩, rfl⟩) | ⟨⟨k, φ⟩, rfl⟩)
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact models_extAx hA
    · exact models_emptyAx (empty_mem_vonNeumann hκ)
    · exact models_pairAx fun x hx y hy => pair_mem_vonNeumann hκ hx hy
    · exact models_unionAx hA fun x hx => sUnion_mem_vonNeumann hx
    · exact models_powerAx hA fun x hx => powerset_mem_vonNeumann hκ hx
    · exact models_infinityAx hA (omega_mem_vonNeumann hκ)
    · exact models_foundationAx hA
    · exact models_choiceAx hA hrange
  · exact models_sepAx hsep k φ
  · exact models_repAx (empty_mem_vonNeumann hκ) hsep hrange k φ

/-! ## Main results -/

/-- **An inaccessible cardinal yields a model of ZFC.**  If `κ` is a (strongly) inaccessible
cardinal, then the level `V_κ` of the von Neumann hierarchy is a model of the first-order theory
`ZFC`; in particular `ZFC` is consistent (satisfiable). -/
