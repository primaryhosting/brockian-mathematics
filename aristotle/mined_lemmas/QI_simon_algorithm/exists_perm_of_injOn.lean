/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The requested header is reproduced above as a plain block comment: Lean 4 does not allow a
-- module docstring `/-! ... -/` to precede the `import` lines.)

import Mathlib

/-!
## Simon's problem

Simon's problem: a function `f` on `n`-bit strings is promised to be two-to-one with
`f x = f y ↔ y = x ∨ y = x + s` for a hidden nonzero secret `s`; the task is to find `s`.

This file formalises the two information-theoretic facts behind the statement
"Simon's problem takes `O(n)` quantum queries but `Ω(2^(n/2))` classical queries":

* **Quantum side.** Each run of Simon's quantum subroutine returns a uniformly random
  vector `y` in the hyperplane `s^⊥`. We show that `n` such vectors always suffice:
  for every nonzero `s` there is a set `Y` of at most `n` vectors orthogonal to `s`
  such that `s` is the unique nonzero vector orthogonal to all of `Y`. Hence `O(n)`
  quantum queries pin down the secret.

* **Classical side.** A classical algorithm only learns something about `s` when two of
  its queries collide. We show that a query set `Q` that is guaranteed to contain a
  collision for *every* possible secret must satisfy `2 ^ n ≤ Q.card ^ 2`, i.e.
  `Q.card ≥ 2 ^ (n / 2)`. Moreover, if `Q.card ^ 2 + 3 ≤ 2 ^ n`, then there are two
  *different* secrets whose Simon functions agree on `Q` up to a global relabelling of
  the output values, so no classical algorithm making those queries can tell them apart.
-/

namespace QI

open Finset

/-- `n`-bit strings, viewed as vectors over the field with two elements. -/
abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- The mod-2 inner product of two bit strings. -/

theorem exists_perm_of_injOn {α : Type*} [DecidableEq α] [Fintype α] (Q : Finset α)
    (f g : α → α) (hf : Set.InjOn f Q) (hg : Set.InjOn g Q) :
    ∃ π : α ≃ α, ∀ x ∈ Q, π (f x) = g x := by
  classical
  have hbij : ∀ (h : α → α), Set.InjOn h Q →
      Function.Bijective (fun x : {x // x ∈ Q} =>
        (⟨h x.1, Finset.mem_image_of_mem h x.2⟩ : {a // a ∈ Q.image h})) := by
    intro h hh
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      simp only [Subtype.mk.injEq] at hxy
      exact Subtype.ext (hh (by simpa using hx) (by simpa using hy) hxy)
    · rintro ⟨a, ha⟩
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
      exact ⟨⟨x, hx⟩, rfl⟩
  let F := Equiv.ofBijective _ (hbij f hf)
  let G := Equiv.ofBijective _ (hbij g hg)
  refine ⟨(F.symm.trans G).extendSubtype, ?_⟩
  intro x hx
  have hfx : f x ∈ Q.image f := Finset.mem_image_of_mem f hx
  rw [Equiv.extendSubtype_apply_of_mem _ _ hfx]
  have hsymm : F.symm ⟨f x, hfx⟩ = ⟨x, hx⟩ := by
    apply F.injective
    simp only [Equiv.apply_symm_apply, F, Equiv.ofBijective_apply]
  simp [Equiv.trans_apply, hsymm, G, Equiv.ofBijective_apply]

/-- Classical indistinguishability: if the query set `Q` satisfies `Q.card ^ 2 + 3 ≤ 2 ^ n`,
then there are two distinct nonzero secrets whose Simon functions agree on `Q` after a global
relabelling `π` of the output values. A classical algorithm making the queries in `Q` therefore
cannot determine the secret. -/
