/-
A Mathlib-facing restatement of `Frontier.arrow_impossibility`, with the finiteness of the
set of voters expressed by `Fintype` instead of by a list of voters covering everything.
-/
import Mathlib
import RequestProject.ArrowImpossibility

namespace Frontier

/-- **Arrow's impossibility theorem** for three alternatives and a finite set of voters:
no social welfare function is unanimous, independent of irrelevant alternatives and
non-dictatorial. -/

theorem allDecisive_of_semiDecisive {F : (V → Ranking) → Ranking} (hU : Unanimous F)
    (hIIA : IIA F) {S : List V} {x y : Fin 3} (hxy : x ≠ y) (hSD : SemiDecisive F S x y) :
    ∀ z w : Fin 3, z ≠ w → Decisive F S z w := by
  obtain ⟨c, hcx, hcy⟩ : ∃ c : Fin 3, c ≠ x ∧ c ≠ y := exists_third x y hxy
  have hxc : x ≠ c := Ne.symm hcx
  have hyc : y ≠ c := Ne.symm hcy
  have Dxc : Decisive F S x c := expand₁ hU hIIA hxy hxc hyc hSD
  have Dcy : Decisive F S c y := expand₂ hU hIIA hxy hxc hyc hSD
  have Dyc : Decisive F S y c :=
    expand₂ hU hIIA hxc hxy hcy (semiDecisive_of_decisive Dxc)
  have Dcx : Decisive F S c x :=
    expand₁ hU hIIA hcy hcx (Ne.symm hxy) (semiDecisive_of_decisive Dcy)
  have Dxy : Decisive F S x y :=
    expand₂ hU hIIA hcy hcx (Ne.symm hxy) (semiDecisive_of_decisive Dcy)
  have Dyx : Decisive F S y x :=
    expand₂ hU hIIA hcx hcy hxy (semiDecisive_of_decisive Dcx)
  intro z w hzw
  have hz : z = x ∨ z = y ∨ z = c := fin3_trichotomy x y c z hxy hcx hcy
  have hw : w = x ∨ w = y ∨ w = c := fin3_trichotomy x y c w hxy hcx hcy
  rcases hz with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hzw
      | assumption

/-- The splitting (contraction) lemma: if the disjoint union `S₁ ++ S₂` is decisive for
`(0,1)`, then one of `S₁`, `S₂` is semi-decisive for some pair. -/
