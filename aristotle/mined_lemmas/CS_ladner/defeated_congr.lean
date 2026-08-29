/-!
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained: the required header comment
above is a module docstring, and Lean only accepts a module docstring at the
very beginning of a file when the file has no `import` commands.  Everything
below therefore uses only the Lean 4 core library.
-/

namespace CS

open Classical

/-- A language: a set of (encoded) strings, i.e. a predicate on `Nat`. -/
abbrev Lang := Nat → Prop

/-! ## Classical helpers -/


theorem defeated_congr {g h : Nat → Nat} {n : Nat} (hcl : clock n ≤ n)
    (H : ∀ k, k ≤ n → g k = h k) :
    defeated dec red K clock g n ↔ defeated dec red K clock h n := by
  have hn : g n = h n := H n (Nat.le_refl n)
  unfold defeated
  rw [hn]
  constructor
  · rintro (⟨he, z, hz, hw⟩ | ⟨he, z, hz, hred, hw⟩)
    · exact Or.inl ⟨he, z, hz, by rw [H z (Nat.le_trans hz hcl)] at hw; exact hw⟩
    · exact Or.inr ⟨he, z, hz, hred, by rw [H _ (Nat.le_trans hred hcl)] at hw; exact hw⟩
  · rintro (⟨he, z, hz, hw⟩ | ⟨he, z, hz, hred, hw⟩)
    · exact Or.inl ⟨he, z, hz, by rw [H z (Nat.le_trans hz hcl)]; exact hw⟩
    · exact Or.inr ⟨he, z, hz, hred, by rw [H _ (Nat.le_trans hred hcl)]; exact hw⟩

