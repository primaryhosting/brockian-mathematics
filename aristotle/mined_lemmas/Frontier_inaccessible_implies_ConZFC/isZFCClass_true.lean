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

theorem isZFCClass_true : IsZFCClass (fun _ : ZFSet.{u} => True) where
  mem_trans := fun _ _ => trivial
  pair := fun _ _ => trivial
  sUnion := fun _ => trivial
  powerset := fun _ => trivial
  omega := trivial
  replacement := by
    intro a f _ _
    classical
    refine ⟨ZFSet.range (fun i : ↥a => f i.1), trivial, fun z => ?_⟩
    rw [ZFSet.mem_range]
    constructor
    · rintro ⟨⟨y, hy⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩

end Frontier

/-
The sets of rank below an inaccessible cardinal form a model of ZFC.
-/
import RequestProject.ZFCModel

/-!
# `V_κ` for `κ` inaccessible is a ZFC class

We show that if `κ` is a (strongly) inaccessible cardinal, then the class of sets of rank
`< κ.ord` — that is, the level `V_κ` of the von Neumann hierarchy — satisfies the closure
conditions `Frontier.IsZFCClass`, and hence gives a model of ZFC.

The two nontrivial points are:

* `Cardinal.preBeth_lt_of_isInaccessible`: `κ` being a strong limit and regular implies that
  `ℶ'_o < κ` for every `o < κ.ord`; since `ZFSet.card (V_ o) = ℶ'_o`, every set of rank `< κ.ord`
  has cardinality `< κ`;
* closure under replacement then follows from the regularity of `κ`.
-/

universe u

open Cardinal Ordinal ZFSet

namespace Frontier

/-- Reindexing a supremum along an equivalence. -/
