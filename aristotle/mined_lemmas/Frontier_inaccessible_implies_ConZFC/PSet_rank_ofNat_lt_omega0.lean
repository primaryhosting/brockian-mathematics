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

theorem PSet_rank_ofNat_lt_omega0 (n : ℕ) : (PSet.ofNat n).rank < Ordinal.omega0 := by
  induction n with
  | zero => simp [PSet.ofNat, Ordinal.omega0_pos]
  | succ n ih =>
    rw [PSet.ofNat, PSet.rank_insert]
    exact max_lt (Order.IsSuccLimit.succ_lt Ordinal.isSuccLimit_omega0 ih) ih

/-- `ω` has rank at most `ω`. -/
