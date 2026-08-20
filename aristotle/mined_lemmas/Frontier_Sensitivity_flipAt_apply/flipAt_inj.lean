import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

lemma flipAt_inj {n : ℕ} {k l : Fin n} {u : Q n} (h : flipAt k u = flipAt l u) : k = l := by
  by_contra hkl
  have h2 := congrFun h k
  simp only [flipAt_apply, if_neg hkl] at h2
  cases hu : u k <;> rw [hu] at h2 <;> simp at h2

/-! #### Basic properties of `eps` -/

