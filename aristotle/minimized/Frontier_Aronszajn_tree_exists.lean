import Mathlib
-- (Lean 4 requires `import` commands to precede any module docstring, so the required
-- header comment is reproduced verbatim immediately below.)

/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Ordinal Set Cardinal
open scoped Ordinal

namespace Aronszajn

/-! ## Countable ordinals -/

/-- An ordinal is countable (i.e. its set of predecessors is countable) iff it is `< ω₁`. -/

noncomputable def cs (α : Ordinal.{0}) : ℕ → Ordinal.{0} :=
  open Classical in
  if h : ∃ g : ℕ → Ordinal.{0}, ∀ ξ < α, ∃ n, ξ ≤ g n ∧ g n < α then h.choose else fun _ => 0

/-- `Good α ξ n` says that stage `cs α n` is below `α` and reaches at least `ξ`. -/

def Good (α ξ : Ordinal.{0}) (n : ℕ) : Prop := ξ ≤ cs α n ∧ cs α n < α

noncomputable def kk (α ξ : Ordinal.{0}) : ℕ :=
  open Classical in
  if h : ∃ n, Good α ξ n then Nat.find h else 0

lemma kk_spec {α ξ : Ordinal.{0}} (h : ∃ n, Good α ξ n) : Good α ξ (kk α ξ) := by
  classical
  rw [kk, dif_pos h]; exact Nat.find_spec h

noncomputable def ee : Ordinal.{0} → Ordinal.{0} → ℕ
  | α => fun ξ =>
    open Classical in
    if _h : ∃ n : ℕ, Good α ξ n then max (ee (cs α (kk α ξ)) ξ) (kk α ξ) else 0
  termination_by α => α
  decreasing_by exact (kk_spec _h).2

noncomputable def rest (x : Ordinal.{0} → ℕ) (γ : Ordinal.{0}) : Ordinal.{0} → ℕ :=
  fun ξ => if ξ < γ then x ξ else 0

def Nice (β : Ordinal.{0}) (x : Ordinal.{0} → ℕ) : Prop :=
  β < ω₁ ∧ (∀ ξ, β ≤ ξ → x ξ = 0) ∧ ∃ α, β ≤ α ∧ α < ω₁ ∧ ∀ ξ < β, x ξ = ee α ξ

/-- The Aronszajn tree. -/

def Tree : Type 1 := {p : Ordinal.{0} × (Ordinal.{0} → ℕ) // Nice p.1 p.2}

namespace Tree

/-- The level of a node. -/

def lvl (a : Tree) : Ordinal.{0} := a.1.1

/-- The function attached to a node. -/

lemma exists_lvl_eq {β : Ordinal.{0}} (hβ : β < ω₁) : ∃ a : Tree, lvl a = β := by
  refine ⟨⟨(β, rest (ee β) β), hβ, fun ξ hξ => if_neg (not_lt.2 hξ), β, le_rfl, hβ,
    fun ξ hξ => if_pos hξ⟩, rfl⟩
