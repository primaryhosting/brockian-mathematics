/-!
# Disjunction Split Preserves Semantics
Category: Proof-Carrying Apps
Target: PCA.Isolation.disjunction_split_preserves_semantics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace PCA
namespace Isolation

/-- Guard formulas of the isolation engine's policy language: propositional
formulas over atomic capability checks indexed by natural numbers. -/
inductive Guard : Type
  | tt : Guard
  | ff : Guard
  | atom : Nat → Guard
  | neg : Guard → Guard
  | conj : Guard → Guard → Guard
  | disj : Guard → Guard → Guard
  deriving DecidableEq, Repr

namespace Guard

/-- Semantics of a guard relative to an environment assigning a truth value to
each atomic capability check. -/

def eval (env : Nat → Bool) : Guard → Bool
  | tt => true
  | ff => false
  | atom i => env i
  | neg g => !(g.eval env)
  | conj g₁ g₂ => (g₁.eval env) && (g₂.eval env)
  | disj g₁ g₂ => (g₁.eval env) || (g₂.eval env)

/-- The isolation engine's disjunction split: a guard is decomposed into the
list of its top-level disjuncts, each of which is analysed in isolation. -/

def split : Guard → List Guard
  | disj g₁ g₂ => g₁.split ++ g₂.split
  | g => [g]

@[simp] theorem split_disj (g₁ g₂ : Guard) :
    (disj g₁ g₂).split = g₁.split ++ g₂.split := rfl

/-- The split is never empty: every guard has at least one branch. -/

theorem disjunction_split_preserves_semantics (env : Nat → Bool) (g : Guard) :
    g.eval env = true ↔ ∃ b ∈ g.split, b.eval env = true := by
  induction g with
  | disj g₁ g₂ ih₁ ih₂ =>
      simp only [Guard.eval, Guard.split_disj, List.mem_append, Bool.or_eq_true]
      constructor
      · rintro (h | h)
        · obtain ⟨b, hb, hb'⟩ := ih₁.mp h
          exact ⟨b, Or.inl hb, hb'⟩
        · obtain ⟨b, hb, hb'⟩ := ih₂.mp h
          exact ⟨b, Or.inr hb, hb'⟩
      · rintro ⟨b, hb | hb, hb'⟩
        · exact Or.inl (ih₁.mpr ⟨b, hb, hb'⟩)
        · exact Or.inr (ih₂.mpr ⟨b, hb, hb'⟩)
  | _ => simp [Guard.split]

/-- Soundness direction: if some branch of the split holds, the original guard
holds. -/
