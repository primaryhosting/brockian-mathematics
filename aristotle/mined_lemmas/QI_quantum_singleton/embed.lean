/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 does not allow a `/-! ... -/` module docstring to precede `import`, so the
-- required header comment is reproduced verbatim immediately after the import below.)

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true

set_option grind.warning false

/-!
## Overview

We prove the **quantum Singleton bound** (Knill–Laflamme–Rains): an `[[n, k, d]]_q`
quantum error-correcting code satisfies `k + 2 * (d - 1) ≤ n`, i.e. `n - k ≥ 2 (d - 1)`.

The proof given here is a purely linear-algebraic ("Rényi-0"/rank) version of the usual
entropic no-cloning argument.  Writing the code space as a tensor `T` with a reference
index `R` (of size `q ^ k`) and three groups of sites `A`, `B`, `C`, the Knill–Laflamme
conditions for the two disjoint site sets `A` and `B` say that the Gram matrices of the
code vectors, partially traced onto `A` (resp. `B`), are proportional to the identity in
the reference index.  Passing to ranks:

* `rank ρ_{RA} = |R| · rank ρ_A` and `rank ρ_{RB} = |R| · rank ρ_B`  (Kronecker structure);
* `rank ρ_{BC} ≤ rank ρ_B · rank ρ_C`  (rank submultiplicativity across a tensor cut);
* `rank ρ_{RA} = rank ρ_{BC}` and `rank ρ_{RB} = rank ρ_{AC}` (purity).

Multiplying the two resulting inequalities `|R| · a ≤ b · c` and `|R| · b ≤ a · c` and
cancelling `a·b > 0` gives `|R| ≤ c ≤ q ^ |C|`, which is the bound.

No Mathlib lemma proves this statement (Mathlib contains no quantum coding theory), so the
required linear algebra — in particular a rank factorization of a matrix with one-sided
inverses, the rank of `1 ⊗ₖ S`, and submultiplicativity of the rank across a tensor cut —
is developed here from scratch.
-/

open Matrix Module Kronecker
open scoped ComplexOrder

namespace QI

/-! ### General linear algebra: rank tools -/

/-- **Rank factorization.**  Any matrix `N` factors as `N = F * G` where `F` has `rank N`
columns and a left inverse, and `G` has `rank N` rows and a right inverse. -/

def embed {n q : ℕ} (A : Finset (Fin n))
    (E : Matrix ({i // i ∈ A} → Fin q) ({i // i ∈ A} → Fin q) ℂ) :
    Matrix (Sites n q) (Sites n q) ℂ :=
  Matrix.of fun x y => if ∀ i, i ∉ A → x i = y i then E (fun i => x i.1) (fun i => y i.1) else 0

/-- An `[[n, k, d]]_q` quantum error-correcting code: an orthonormal family of `q ^ k`
states of `n` qudits of local dimension `q` (an orthonormal basis of the code space)
satisfying the Knill–Laflamme error-correction conditions for every set of at most
`d - 1` sites, i.e. the code corrects the erasure of any `d - 1` qudits, which is the
standard characterisation of having minimum distance at least `d`. -/
structure Code (n k d q : ℕ) where
  /-- An orthonormal basis of the code space. -/
  state : Fin (q ^ k) → Sites n q → ℂ
  /-- The basis is orthonormal. -/
  orthonormal : ∀ i j, ∑ x, (starRingEnd ℂ) (state i x) * state j x = if i = j then 1 else 0
  /-- Knill–Laflamme conditions: for every operator `E` supported on at most `d - 1`
  sites, `P E P = c(E) P` on the code space. -/
  knill_laflamme : ∀ (S : Finset (Fin n)), S.card ≤ d - 1 →
      ∀ E, ∃ c : ℂ, ∀ i j,
        ∑ x, ∑ y, (starRingEnd ℂ) (state i x) * embed S E x y * state j y = if i = j then c else 0

section Split

variable {n q : ℕ} (A B Cs : Finset (Fin n))
  (hmem : ∀ i : Fin n, (i ∈ A ∧ i ∉ B ∧ i ∉ Cs) ∨ (i ∉ A ∧ i ∈ B ∧ i ∉ Cs)
      ∨ (i ∉ A ∧ i ∉ B ∧ i ∈ Cs))
  (hcard : A.card + B.card + Cs.card = n)

/-- The identification of a configuration of `n` qudits with the triple of its
restrictions to a partition of the sites into three groups `A`, `B`, `Cs`. -/
