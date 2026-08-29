/-
Models of ZFC given by suitable classes of ZFC sets.
-/
import RequestProject.SetLanguage

/-!
# Classes of sets that model ZFC

We isolate a set of closure conditions on a class `P : ZFSet.{u} → Prop`
(`Frontier.IsZFCClass`) which guarantee that the structure with domain `{x : ZFSet // P x}`
and the real membership relation is a model of the first-order theory `Frontier.ZFC`.

The conditions are: transitivity, closure under pairing, unions, power sets, the presence of
`ω`, and closure under (second-order) replacement.

The class of *all* sets satisfies these conditions, so `ZFSet.{u}` itself is a model of ZFC.
-/

universe u w

namespace Frontier

open FirstOrder Language ZFSet

/-- The `setLang`-structure on a type equipped with a binary relation. -/

theorem isZFCClass_rank_lt {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    IsZFCClass (fun x : ZFSet.{u} => x.rank < κ.ord) := by
  have hlim : Order.IsSuccLimit κ.ord := Cardinal.isSuccLimit_ord hκ.aleph0_lt.le
  have homega : Ordinal.omega0.{u} < κ.ord := by
    rw [← Cardinal.ord_aleph0]
    exact Cardinal.ord_lt_ord.2 hκ.aleph0_lt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hx hy
    exact (ZFSet.rank_lt_of_mem hy).trans hx
  · intro x y hx hy
    rw [ZFSet.rank_pair]
    exact max_lt (hlim.succ_lt hx) (hlim.succ_lt hy)
  · intro x hx
    exact (ZFSet.rank_sUnion_le x).trans_lt hx
  · intro x hx
    rw [ZFSet.rank_powerset]
    exact hlim.succ_lt hx
  · exact rank_omega_le.trans_lt homega
  · intro a f ha hf
    classical
    refine ⟨ZFSet.range (fun i : Shrink.{u} a => f ((equivShrink (α := (a : Type (u + 1)))).symm i)),
      ?_, ?_⟩
    · rw [ZFSet.rank_range]
      refine Cardinal.iSup_lt_ord_of_isRegular hκ.isRegular ?_ ?_
      · have : #(Shrink.{u} (a : Type (u + 1))) = a.card := rfl
        rw [this]
        exact card_lt_of_rank_lt hκ ha
      · intro i
        exact hlim.succ_lt (hf _ ((equivShrink (α := (a : Type (u + 1)))).symm i).2)
    · intro z
      rw [ZFSet.mem_range]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨_, ((equivShrink (α := (a : Type (u + 1)))).symm i).2, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨equivShrink _ ⟨y, hy⟩, by simp⟩

/-- The same class, described as the level `V_ κ.ord` of the von Neumann hierarchy. -/
