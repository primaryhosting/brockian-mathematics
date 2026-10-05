/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

/-- `Unbdd A` says that the set of naturals satisfying `A` is unbounded, i.e. infinite. -/

theorem unbdd_split (A : Nat → Prop) (f : Nat → Bool) (hA : Unbdd A) :
    ∃ k : Bool, Unbdd (fun n => A n ∧ f n = k) :=
  Classical.byContradiction fun hcon => by
    obtain ⟨N1, hN1⟩ := not_unbdd (fun h => hcon ⟨true, h⟩)
    obtain ⟨N2, hN2⟩ := not_unbdd (fun h => hcon ⟨false, h⟩)
    obtain ⟨m, hm, hAm⟩ := hA (N1 + N2)
    cases hfm : f m with
    | true => exact hN1 m (by omega) ⟨hAm, hfm⟩
    | false => exact hN2 m (by omega) ⟨hAm, hfm⟩

/-- One step of the Ramsey construction, packaged as a structure: from an unbounded set `A`
we extract a point `a ∈ A`, a colour `k`, and an unbounded set `B` of points of `A` above `a`,
all joined to `a` in colour `k`. -/
structure StepData (c : Nat → Nat → Bool) (A : Nat → Prop) where
  a : Nat
  k : Bool
  B : Nat → Prop
  mem : A a
  sub : ∀ b, B b → A b ∧ a < b
  unbdd : Unbdd B
  colour : ∀ b, B b → c a b = k

