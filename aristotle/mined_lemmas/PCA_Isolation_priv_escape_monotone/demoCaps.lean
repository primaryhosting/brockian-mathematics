/-!
# Priv Escape Monotone
Category: Proof-Carrying Apps
Target: PCA.Isolation.priv_escape_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: Lean 4 does not permit any command (including a module docstring) to precede
the `import` block, so in order for this file to *begin* with the header comment above it is
kept import-free.  Everything below is therefore developed from scratch on top of core Lean 4
(the file compiles unchanged inside this Mathlib project, and uses no axioms beyond
`propext`, `Classical.choice`, `Quot.sound`).
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA
namespace Isolation

/-! ## The isolation engine's model

Privilege levels are natural numbers, higher meaning more privileged.  An app runs inside an
isolation boundary `bound : Nat` and holds a set `avail` of capabilities.  Exercising a
capability requires a privilege level and confers one. -/

/-- A set of capabilities, represented as a predicate on capability names. -/

def demoCaps : Caps := fun c => c = 1

/-- An unprivileged app with capability `1` escapes the boundary `3`. -/
example : Escapes demoPolicy demoCaps 3 0 :=
  ⟨max 0 (demoPolicy.gain 1), Reach.single ⟨1, rfl, Nat.le_refl 0, rfl⟩, by decide⟩

/-- Hence, by monotonicity, it escapes the tighter boundary `2` from privilege `4` with the
larger capability set of all capabilities. -/
example : Escapes demoPolicy (fun _ => True) 2 4 :=
  priv_escape_monotone (avail := demoCaps) (bound := 3) (p := 0)
    (fun _ _ => trivial) (by decide) (by decide)
    ⟨max 0 (demoPolicy.gain 1), Reach.single ⟨1, rfl, Nat.le_refl 0, rfl⟩, by decide⟩

/-- The same configuration is not certified at boundary `3`. -/
example : ¬ Certified demoPolicy demoCaps 3 := fun h => by
  have := h 1 rfl (by decide)
  simp only [demoPolicy] at this
  omega

/-- But it is certified — hence escape free — at boundary `5`. -/
example : Certified demoPolicy demoCaps 5 := fun _ _ _ => Nat.le_refl 5

#print axioms priv_escape_monotone
#print axioms certified_iff_no_escape
#print axioms not_escapes_of_certified
#print axioms escapes_of_not_certified

end Isolation
end PCA

