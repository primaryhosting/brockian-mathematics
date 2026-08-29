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

theorem exists_rank_factorization {K m n : Type} [Field K] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (N : Matrix m n K) :
    ∃ (r : ℕ) (F : Matrix m (Fin r) K) (G : Matrix (Fin r) n K)
      (L : Matrix (Fin r) m K) (M : Matrix n (Fin r) K),
      r = N.rank ∧ N = F * G ∧ L * F = 1 ∧ G * M = 1 := by
  classical
  set f := N.mulVecLin with hf
  have hr : Module.finrank K (LinearMap.range f) = N.rank := rfl
  let bW : Basis (Fin N.rank) K (LinearMap.range f) := Module.finBasisOfFinrankEq K _ hr
  let phi : (Fin N.rank → K) →ₗ[K] (m → K) :=
    (LinearMap.range f).subtype ∘ₗ (bW.equivFun.symm : (Fin N.rank → K) →ₗ[K] (LinearMap.range f))
  let psi : (n → K) →ₗ[K] (Fin N.rank → K) :=
    (bW.equivFun : (LinearMap.range f) →ₗ[K] (Fin N.rank → K)) ∘ₗ f.rangeRestrict
  have hcomp : phi ∘ₗ psi = f := by ext v i; simp [phi, psi]
  have hphiinj : LinearMap.ker phi = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact (Submodule.injective_subtype _).comp bW.equivFun.symm.injective
  have hpsisurj : LinearMap.range psi = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact bW.equivFun.surjective.comp f.surjective_rangeRestrict
  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective phi hphiinj
  obtain ⟨rr, hrr⟩ := LinearMap.exists_rightInverse_of_surjective psi hpsisurj
  refine ⟨N.rank, LinearMap.toMatrix' phi, LinearMap.toMatrix' psi, LinearMap.toMatrix' l,
    LinearMap.toMatrix' rr, rfl, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hcomp, hf]
    exact (LinearEquiv.symm_apply_eq LinearMap.toMatrix').mp rfl
  · rw [← LinearMap.toMatrix'_comp, hl]; simp
  · rw [← LinearMap.toMatrix'_comp, hrr]; simp

/-- The rank of `1 ⊗ₖ S` is at least `|R| * rank S` (in fact equal, but only `≥` is
needed below). -/
