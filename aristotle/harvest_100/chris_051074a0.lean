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

/-!
# Null Escape Iff Unowned Reachable
Category: Proof-Carrying Apps
Target: PCA.Isolation.null_escape_iff_unowned_reachable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

universe u

namespace PCA.Isolation

/-- Reflexive-transitive closure of a relation, used for heap reachability:
`ReachGen r a b` holds when `b` is reached from `a` by finitely many `r`-steps. -/
inductive ReachGen {V : Type u} (r : V → V → Prop) (a : V) : V → Prop
  /-- Zero steps. -/
  | refl : ReachGen r a a
  /-- One more step at the end of a path. -/
  | tail {b c : V} : ReachGen r a b → r b c → ReachGen r a c

/-- A model of the isolation engine's view of a heap: a points-to relation `edge`
on locations, a predicate `owned` marking the locations owned by the isolated
region, and a distinguished entry point `root` (the reference handed out at the
region boundary). -/
structure IsoModel (V : Type u) where
  /-- `edge a b` means location `a` holds a reference to location `b`. -/
  edge : V → V → Prop
  /-- `owned v` means location `v` belongs to the isolated region. -/
  owned : V → Prop
  /-- The entry point of the traversal. -/
  root : V

variable {V : Type u} (M : IsoModel V)

/-- `Reach M v`: `v` is reachable from the root along points-to edges. -/
def Reach (v : V) : Prop := ReachGen M.edge M.root v

/-- `OwnedReach M v`: `v` is reachable from the root along points-to edges that
stay entirely inside the owned region (the set the engine actually explores). -/
def OwnedReach (v : V) : Prop :=
  ReachGen (fun a b => M.edge a b ∧ M.owned a ∧ M.owned b) M.root v

/-- The escape condition flagged by the isolation engine: either the root itself
is not owned, or the owned closure of the root has an edge crossing out of the
owned region. -/
def NullEscape : Prop :=
  ¬ M.owned M.root ∨ ∃ a b, OwnedReach M a ∧ M.edge a b ∧ ¬ M.owned b

variable {M}

/-- Everything in the owned closure is reachable. -/
theorem reach_of_ownedReach {v : V} (h : OwnedReach M v) : Reach M v := by
  induction h with
  | refl => exact ReachGen.refl
  | tail _ hstep ih => exact ih.tail hstep.1

/-- If the root is owned, then everything in the owned closure is owned. -/
theorem owned_of_ownedReach {v : V} (hroot : M.owned M.root) (h : OwnedReach M v) :
    M.owned v := by
  induction h with
  | refl => exact hroot
  | tail _ hstep _ => exact hstep.2.2

/-- Key step: every reachable location either lies in the owned closure, or the
engine has already flagged an escape. -/
theorem ownedReach_or_nullEscape {v : V} (h : Reach M v) :
    NullEscape M ∨ OwnedReach M v := by
  by_cases hroot : M.owned M.root
  · induction h with
    | refl => exact Or.inr ReachGen.refl
    | @tail b c hb hstep ih =>
        rcases ih with hesc | hb'
        · exact Or.inl hesc
        · have hbown : M.owned b := owned_of_ownedReach hroot hb'
          by_cases hc : M.owned c
          · exact Or.inr (hb'.tail ⟨hstep, hbown, hc⟩)
          · exact Or.inl (Or.inr ⟨b, c, hb', hstep, hc⟩)
  · exact Or.inl (Or.inl hroot)

/-- **Soundness and completeness of the isolation engine's escape check.**
The engine reports a null escape exactly when some location outside the isolated
region is reachable from the root. -/
theorem null_escape_iff_unowned_reachable :
    NullEscape M ↔ ∃ v : V, Reach M v ∧ ¬ M.owned v := by
  constructor
  · rintro (hroot | ⟨a, b, ha, hab, hb⟩)
    · exact ⟨M.root, ReachGen.refl, hroot⟩
    · exact ⟨b, (reach_of_ownedReach ha).tail hab, hb⟩
  · rintro ⟨v, hv, hvo⟩
    rcases ownedReach_or_nullEscape hv with hesc | hown
    · exact hesc
    · by_cases hroot : M.owned M.root
      · exact absurd (owned_of_ownedReach hroot hown) hvo
      · exact Or.inl hroot

end PCA.Isolation

