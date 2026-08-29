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

theorem rank_omega_le : ZFSet.rank ZFSet.omega.{u} ≤ Ordinal.omega0.{u} := by
  rw [ZFSet.rank_le_iff]
  intro y hy
  induction y using Quotient.inductionOn with
  | _ p =>
    obtain ⟨i, hi⟩ := hy
    show PSet.rank p < Ordinal.omega0
    rw [PSet.rank_congr hi]
    exact PSet_rank_ofNat_lt_omega0 i.down

/-- For `κ` inaccessible, the sets of rank `< κ.ord` form a class satisfying the ZFC closure
conditions. -/
