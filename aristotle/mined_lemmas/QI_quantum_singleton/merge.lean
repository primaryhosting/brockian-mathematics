/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Statement: Quantum Singleton bound: an [[n,k,d]] code obeys n−k ≥ 2(d−1).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Statement: Quantum Singleton bound: an [[n,k,d]] code obeys n−k ≥ 2(d−1).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Kronecker ComplexOrder
open Matrix Module

namespace QI

section LinearAlgebra

variable {X W : Type*} [Fintype X] [Fintype W] [DecidableEq X] [DecidableEq W]

/-- Rank factorization: every matrix `F` factors as `U * L * F = F` with `U` having
`F.rank` columns. -/

def merge (S : Finset (Fin n)) (x : {i // i ∈ S} → Fin q) (z : {i // i ∉ S} → Fin q) :
    Fin n → Fin q :=
  fun i => if h : i ∈ S then x ⟨i, h⟩ else z ⟨i, h⟩

/-- `IsQECC n q d K ψ` says that the `K` orthonormal vectors `ψ` span a `K`-dimensional
quantum code on `n` qudits of local dimension `q` with (minimum) distance at least `d`:
the Knill–Laflamme error-correction conditions hold for every set `S` of at most `d - 1`
erased qudits, i.e. the partial trace of `|ψ i⟩⟨ψ j|` over the complement of `S`
equals `δ i j • ρ` for a fixed operator `ρ` on `S`. -/
