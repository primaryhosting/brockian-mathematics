import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

/-! ## Auxiliary counting lemmas -/

/-- Parity translated into `ZMod 2`. -/

lemma spernerCells_over_door_card {J : Finset (Fin (n + 1))} {i₀ : Fin (n + 1)} (hi₀ : i₀ ∈ J)
    {τ : Finset V} (hτ : τ ∈ spernerDoors carrier T c J i₀) :
    (((spernerCells carrier T J).filter (fun σ => τ ⊆ σ)).card : ZMod 2)
      = if τ ∈ spernerRainbow carrier T c (J.erase i₀) then 1 else 0 := by
  classical
  obtain ⟨hτT, hτcard, hτcar, hτimg⟩ := Finset.mem_filter.mp hτ
  rw [hpm J τ hτT hτcard hτcar]
  -- `J.erase i₀ ⊆ τ.biUnion carrier ⊆ J`
  have hlow : J.erase i₀ ⊆ τ.biUnion carrier := by
    rw [← hτimg]
    intro j hj
    obtain ⟨v, hv, hfv⟩ := Finset.mem_image.mp hj
    exact Finset.mem_biUnion.mpr ⟨v, hv, hfv ▸ hc v⟩
  have hhigh : τ.biUnion carrier ⊆ J := by
    intro j hj
    obtain ⟨v, hv, hjv⟩ := Finset.mem_biUnion.mp hj
    exact hτcar v hv hjv
  have hmemiff : τ ∈ spernerRainbow carrier T c (J.erase i₀) ↔ τ.biUnion carrier ≠ J := by
    constructor
    · intro hmem hcon
      obtain ⟨hmc, -⟩ := Finset.mem_filter.mp hmem
      obtain ⟨-, -, hcar'⟩ := Finset.mem_filter.mp hmc
      have : i₀ ∈ τ.biUnion carrier := by rw [hcon]; exact hi₀
      obtain ⟨v, hv, hiv⟩ := Finset.mem_biUnion.mp this
      exact (Finset.notMem_erase i₀ J) (hcar' v hv hiv)
    · intro hne
      have hi₀not : i₀ ∉ τ.biUnion carrier := by
        intro hcon
        apply hne
        apply Finset.Subset.antisymm hhigh
        intro j hj
        by_cases hji : j = i₀
        · subst hji; exact hcon
        · exact hlow (Finset.mem_erase.mpr ⟨hji, hj⟩)
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hτT, ?_, ?_⟩, hτimg⟩
      · rw [Finset.card_erase_of_mem hi₀]; omega
      · intro v hv j hj
        refine Finset.mem_erase.mpr ⟨?_, hτcar v hv hj⟩
        rintro rfl
        exact hi₀not (Finset.mem_biUnion.mpr ⟨v, hv, hj⟩)
  by_cases hb : τ.biUnion carrier = J
  · rw [if_pos hb, if_neg (by rw [hmemiff]; simpa using hb)]
    decide
  · rw [if_neg hb, if_pos (hmemiff.mpr hb)]
    norm_num

include hdown hT0 hpm hc in
/-- **Key induction.** Every nonempty face of the big simplex carries an odd number of
rainbow cells. -/
