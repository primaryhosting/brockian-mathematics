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

lemma embed_split (E : Matrix ({i // i ∈ A} → Fin q) ({i // i ∈ A} → Fin q) ℂ)
    (a a' : {i // i ∈ A} → Fin q) (b b' : {i // i ∈ B} → Fin q)
    (c c' : {i // i ∈ Cs} → Fin q) :
    embed A E ((splitEquiv A B Cs hmem hcard).symm (a, b, c))
        ((splitEquiv A B Cs hmem hcard).symm (a', b', c'))
      = if b = b' ∧ c = c' then E a a' else 0 := by
  classical
  set e := splitEquiv (q := q) A B Cs hmem hcard with he
  have hA1 : (fun (i : {i // i ∈ A}) => (e.symm (a, b, c)) i.1) = a := by
    funext i; exact splitEquiv_symm_A A B Cs hmem hcard _ i.1 i.2
  have hA2 : (fun (i : {i // i ∈ A}) => (e.symm (a', b', c')) i.1) = a' := by
    funext i; exact splitEquiv_symm_A A B Cs hmem hcard _ i.1 i.2
  have hcond : (∀ i, i ∉ A → (e.symm (a, b, c)) i = (e.symm (a', b', c')) i)
      ↔ (b = b' ∧ c = c') := by
    constructor
    · intro h
      constructor
      · funext i
        have hiA : i.1 ∉ A := by
          rcases hmem i.1 with ⟨-, hb, -⟩ | ⟨ha, -, -⟩ | ⟨-, hb, -⟩
          · exact absurd i.2 hb
          · exact ha
          · exact absurd i.2 hb
        have h2 := h i.1 hiA
        rwa [splitEquiv_symm_B A B Cs hmem hcard _ i.1 i.2,
          splitEquiv_symm_B A B Cs hmem hcard _ i.1 i.2] at h2
      · funext i
        have hiA : i.1 ∉ A := by
          rcases hmem i.1 with ⟨-, -, hc⟩ | ⟨-, -, hc⟩ | ⟨ha, -, -⟩
          · exact absurd i.2 hc
          · exact absurd i.2 hc
          · exact ha
        have h2 := h i.1 hiA
        rwa [splitEquiv_symm_C A B Cs hmem hcard _ i.1 i.2,
          splitEquiv_symm_C A B Cs hmem hcard _ i.1 i.2] at h2
    · rintro ⟨rfl, rfl⟩ i hi
      rcases hmem i with ⟨hia, -, -⟩ | ⟨-, hib, -⟩ | ⟨-, -, hic⟩
      · exact absurd hia hi
      · rw [splitEquiv_symm_B A B Cs hmem hcard _ i hib,
          splitEquiv_symm_B A B Cs hmem hcard _ i hib]
      · rw [splitEquiv_symm_C A B Cs hmem hcard _ i hic,
          splitEquiv_symm_C A B Cs hmem hcard _ i hic]
  simp only [embed, Matrix.of_apply, hA1, hA2]
  by_cases h : b = b' ∧ c = c'
  · rw [if_pos (hcond.mpr h), if_pos h]
  · rw [if_neg (fun hh => h (hcond.mp hh)), if_neg h]

/-- The Knill–Laflamme matrix element for a matrix unit supported on `A`, expressed in
split coordinates: it is the partial Gram matrix of the code states over `B × Cs`. -/
