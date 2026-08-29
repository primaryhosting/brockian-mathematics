/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# The Knill–Laflamme theorem

A quantum code (given by the orthogonal projector `P` onto the code space) corrects an
error set `E : ι → Matrix n n ℂ` **iff** the Knill–Laflamme conditions
`P * (E i)ᴴ * (E j) * P = c i j • P` hold for some matrix of scalars `c`.
-/

namespace QI

open Matrix Finset

variable {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- The standard inner product on `n → ℂ`, conjugate linear in the first argument. -/

theorem corrects_of {P : Matrix n n ℂ} {E : ι → Matrix n n ℂ} {κ : Type} [Fintype κ]
    (R : κ → Matrix n n ℂ) (h1 : ∑ k, (R k)ᴴ * R k = 1)
    (h2 : ∀ v : n → ℂ, P *ᵥ v = v → ip v v = 1 →
      ∑ k, ∑ i, outer ((R k * E i) *ᵥ v)
        = (∑ i, ip (E i *ᵥ v) (E i *ᵥ v)) • outer v) : Corrects P E := by
  classical
  refine ⟨Fintype.card κ, fun k => R ((Fintype.equivFin κ).symm k), ?_, ?_⟩
  · rw [Equiv.sum_comp (Fintype.equivFin κ).symm (fun k => (R k)ᴴ * R k)]; exact h1
  · intro v hv hn
    rw [Equiv.sum_comp (Fintype.equivFin κ).symm
      (fun k => ∑ i, outer ((R k * E i) *ᵥ v))]
    exact h2 v hv hn

omit [DecidableEq n] in
