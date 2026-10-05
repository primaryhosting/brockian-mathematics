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

lemma kl_sum {k d : ℕ} (Q : Code n k d q) (a a' : {i // i ∈ A} → Fin q) (i j : Fin (q ^ k)) :
    ∑ x, ∑ y, (starRingEnd ℂ) (Q.state i x) * embed A (Matrix.single a a' 1) x y * Q.state j y
      = ∑ b, ∑ c, (starRingEnd ℂ) (Q.state i ((splitEquiv A B Cs hmem hcard).symm (a, b, c)))
          * Q.state j ((splitEquiv A B Cs hmem hcard).symm (a', b, c)) := by
  classical
  set e := splitEquiv (q := q) A B Cs hmem hcard with he
  rw [← Equiv.sum_comp e.symm (fun x => ∑ y, (starRingEnd ℂ) (Q.state i x)
      * embed A (Matrix.single a a' 1) x y * Q.state j y)]
  have h1 : ∀ p, (∑ y, (starRingEnd ℂ) (Q.state i (e.symm p))
        * embed A (Matrix.single a a' 1) (e.symm p) y * Q.state j y)
      = ∑ p', (starRingEnd ℂ) (Q.state i (e.symm p))
        * embed A (Matrix.single a a' 1) (e.symm p) (e.symm p') * Q.state j (e.symm p') := by
    intro p
    rw [← Equiv.sum_comp e.symm (fun y => (starRingEnd ℂ) (Q.state i (e.symm p))
      * embed A (Matrix.single a a' 1) (e.symm p) y * Q.state j y)]
  rw [Finset.sum_congr rfl (fun p _ => h1 p)]
  simp only [Fintype.sum_prod_type, he, embed_split A B Cs hmem hcard, Matrix.single_apply,
    ite_and, mul_ite, ite_mul, mul_zero, zero_mul, mul_one]
  simp [Finset.sum_ite_eq]

end Split

/-! ### The quantum Singleton bound -/

/-- **Key step.**  If `A` and `B` are disjoint sets of at most `d - 1` sites each, then the
dimension `q ^ k` of the code space is at most `q ^ |Cs|`, where `Cs` is the set of the
remaining `n - |A| - |B|` sites. -/
