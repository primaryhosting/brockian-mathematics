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

def memStructure {M : Type w} (r : M → M → Prop) : setLang.{u}.Structure M where
  funMap {_} f := PEmpty.elim f
  RelMap {n} R := match n, R.down with
    | 2, memRel.mem => fun v => r (v 0) (v 1)

/-- A class of sets satisfying the closure conditions needed to model ZFC. -/
structure IsZFCClass (P : ZFSet.{u} → Prop) : Prop where
  /-- The class is transitive. -/
  mem_trans : ∀ {x y : ZFSet.{u}}, P x → y ∈ x → P y
  /-- The class is closed under unordered pairs. -/
  pair : ∀ {x y : ZFSet.{u}}, P x → P y → P {x, y}
  /-- The class is closed under unions. -/
  sUnion : ∀ {x : ZFSet.{u}}, P x → P (⋃₀ x)
  /-- The class is closed under power sets. -/
  powerset : ∀ {x : ZFSet.{u}}, P x → P x.powerset
  /-- The class contains `ω`. -/
  omega : P ZFSet.omega
  /-- The class is closed under replacement along arbitrary functions. -/
  replacement : ∀ {a : ZFSet.{u}} (f : ZFSet.{u} → ZFSet.{u}), P a → (∀ y ∈ a, P (f y)) →
    ∃ b, P b ∧ ∀ z, z ∈ b ↔ ∃ y ∈ a, f y = z

namespace IsZFCClass

variable {P : ZFSet.{u} → Prop} (h : IsZFCClass P)
include h

