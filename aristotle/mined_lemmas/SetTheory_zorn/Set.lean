import Mathlib

/-!
# Zorn (Mathlib formulation)

Companion to `RequestProject/SetTheoryZorn.lean`.  That file is self-contained (it proves Zorn's

def Set (α : Type u) : Type u := α → Prop

namespace Set

instance : Membership α (Set α) := ⟨fun s a => s a⟩

