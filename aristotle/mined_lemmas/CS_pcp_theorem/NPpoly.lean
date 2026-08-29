/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

This file formalises the statement `NP = PCP(log n, 1)` — the PCP theorem — in a
concrete non-uniform (Boolean circuit) model of computation.  The development is
self-contained and uses no imports.

* `CS.Circuit` : Boolean circuits over an arbitrary type of input variables.
* `CS.NPVerifier` / `CS.NPpoly` : the class of languages possessing a
  polynomial-size verifier reading a polynomially long witness (the non-uniform
  version of `NP`).
* `CS.PCPVerifier` / `CS.PCPlogConst` : probabilistically checkable proof systems
  with logarithmic randomness (equivalently, polynomially many random strings),
  polynomially long proofs, perfect completeness, soundness error `1/2`, and a
  prescribed bound on the number of proof bits inspected.  `PCPlogConst` is the
  class `PCP(log n, O(1))`, where the query bound is a constant independent of
  the input length.

Proved here:

* `CS.pcp_subset_np` : `PCP(log n, q) ⊆ NP` for every query bound (the "easy"
  inclusion; it is proved by taking the conjunction of the verifier's decision
  circuits over all of the polynomially many random strings).
* `CS.np_subset_pcp_polyQueries` : every `NP` language has a PCP system with
  logarithmic randomness and *polynomially many* queries (so the model is not
  degenerate, and the whole content of the PCP theorem is the reduction of the
  number of queries to a constant).
* `CS.ppoly_subset_pcplogconst` : every language decidable by polynomial-size
  circuits lies in `PCP(log n, O(1))` (with zero queries), so the latter class
  is non-empty.
* `CS.pcp_theorem` : the PCP theorem, `NP = PCP(log n, O(1))`.  The hard
  inclusion `NP ⊆ PCP(log n, O(1))` (Arora–Safra, Arora–Lund–Motwani–Sudan–Szegedy)
  is *not* proved here; it enters as an explicit hypothesis `hard` of the
  theorem, while the easy inclusion is supplied by `CS.pcp_subset_np`.
-/

namespace CS

/-! ## Polynomially bounded functions -/

/-- `PolyBdd f` : the function `f : ℕ → ℕ` is bounded by a polynomial. -/

def NPpoly (L : Language) : Prop := Nonempty (NPVerifier L)

/-! ## Probabilistically checkable proofs -/

/-- A PCP system for `L` with logarithmic randomness — i.e. polynomially many
random strings — polynomially long proofs, perfect completeness, soundness error
`1/2`, and at most `qb n` proof bits inspected on inputs of length `n`.

For each input length `n` and each random string `r` the verifier is a
polynomial-size Boolean circuit taking the input and the whole proof, subject to
the requirement (`hquery`) that its value depends on at most `qb n` bits of the
proof: this is exactly the requirement that the verifier makes at most `qb n`
queries to the proof oracle. -/
structure PCPVerifier (L : Language) (qb : Nat → Nat) where
  /-- Proof length. -/
  plen : Nat → Nat
  /-- The proof length is polynomially bounded. -/
  hplen : PolyBdd plen
  /-- The number of random strings; polynomially many, i.e. `O(log n)` random bits. -/
  rand : Nat → Nat
  /-- Polynomially many random strings. -/
  hrand : PolyBdd rand
  /-- There is at least one random string. -/
  hrandpos : ∀ n, 0 < rand n
  /-- The decision circuit associated with each random string. -/
  circ : (n : Nat) → Fin (rand n) → Circuit (Fin n ⊕ Fin (plen n))
  /-- A bound on the size of the decision circuits. -/
  szBound : Nat → Nat
  /-- The size bound is polynomial. -/
  hszBound : PolyBdd szBound
  /-- The decision circuits obey the size bound. -/
  hsize : ∀ n r, (circ n r).size ≤ szBound n
  /-- For every input and random string, the decision depends on at most `qb n`
  bits of the proof: the verifier makes at most `qb n` queries. -/
  hquery : ∀ (n : Nat) (r : Fin (rand n)) (x : Fin n → Bool),
    ∃ S : List (Fin (plen n)), S.length ≤ qb n ∧
      ∀ π π' : Fin (plen n) → Bool, (∀ i ∈ S, π i = π' i) →
        (circ n r).eval (Sum.elim x π) = (circ n r).eval (Sum.elim x π')
  /-- Perfect completeness: inputs in the language have a proof that is accepted
  for every random string. -/
  completeness : ∀ (n : Nat) (x : Fin n → Bool), L n x →
    ∃ π : Fin (plen n) → Bool, ∀ r, (circ n r).eval (Sum.elim x π) = true
  /-- Soundness with error `1/2`: for inputs outside the language, every claimed
  proof is accepted for at most half of the random strings. -/
  soundness : ∀ (n : Nat) (x : Fin n → Bool), ¬ L n x →
    ∀ π : Fin (plen n) → Bool,
      2 * ((List.finRange (rand n)).countP
            (fun r => (circ n r).eval (Sum.elim x π))) ≤ rand n

/-- The class `PCP(log n, O(1))`: languages having a PCP system with logarithmic
randomness and a constant number of queries. -/
