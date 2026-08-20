import Mathlib

/-!
# Robertson Seymour
Category: Frontier Math
Target: Math2.robertson_seymour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
NOTE ON THE HEADER: Lean 4 requires `import` to be the first command of a file, so the
module docstring above is placed directly after `import Mathlib` (a `/-! ... -/` block
before the import is a parse error).
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Math2

universe u v w

open SimpleGraph

/-! ## The minor relation -/

/-- `IsMinor H G` says that `H` is a minor of `G`: there is a family of pairwise disjoint,
nonempty, connected *branch sets* `B w ⊆ V(G)`, indexed by the vertices `w` of `H`, such
that adjacent vertices of `H` have an edge of `G` between their branch sets. -/

theorem exists_strictMono_of_sublistForall₂ {α : Type*} {R : α → α → Prop} {d : α}
    {l₁ l₂ : List α} (h : List.SublistForall₂ R l₁ l₂) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ i, i < l₁.length → σ i < l₂.length ∧ R (l₁.getD i d) (l₂.getD (σ i) d) := by
  induction h with
  | nil => exact ⟨id, strictMono_id, by simp⟩
  | @cons a b l₁ l₂ hab _ ih =>
    obtain ⟨σ, hmono, hσ⟩ := ih
    refine ⟨fun i => Nat.casesOn i 0 (fun j => σ j + 1), ?_, ?_⟩
    · apply strictMono_nat_of_lt_succ
      intro n
      cases n with
      | zero => simp
      | succ m => simpa using hmono (Nat.lt_succ_self m)
    · intro i hi
      cases i with
      | zero => simpa using hab
      | succ m =>
        simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
        obtain ⟨h1, h2⟩ := hσ m hi
        simpa [List.getD_cons_succ] using ⟨h1, h2⟩
  | @cons_right b l₁ l₂ _ ih =>
    obtain ⟨σ, hmono, hσ⟩ := ih
    refine ⟨fun i => σ i + 1, fun a b hab => by simpa using hmono hab, ?_⟩
    intro i hi
    obtain ⟨h1, h2⟩ := hσ i hi
    simpa [List.getD_cons_succ] using ⟨h1, h2⟩

/-! ## Isomorphism invariance of the minor relation -/

/-- An isomorphism is in particular a subgraph embedding. -/
