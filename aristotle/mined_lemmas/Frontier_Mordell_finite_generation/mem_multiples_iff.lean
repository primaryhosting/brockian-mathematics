import Mathlib

/-!
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open scoped Classical

/-- Multiplication by `m : ℕ` on an additive commutative group, as a group homomorphism. -/

lemma mem_multiples_iff {A : Type*} [AddCommGroup A] {m : ℕ} {a : A} :
    a ∈ multiples A m ↔ ∃ b : A, m • b = a := Iff.rfl

/-! ## Coset representatives coming from finiteness of `A / mA` -/

/-- If `A / mA` is finite, then there is a finite set of coset representatives: every `P ∈ A` can
be written as `P = m • P' + Q` with `Q` in a fixed finite set. -/
