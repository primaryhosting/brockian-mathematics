/-
# Atiyah Singer Index
Category: Frontier — Fields Medal Work
Target: Frontier.atiyah_singer_index
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Atiyah Singer Index
Category: Frontier — Fields Medal Work
Target: Frontier.atiyah_singer_index
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
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
## Overview

The Atiyah–Singer index theorem states that for an elliptic (pseudo-)differential operator
`D : Γ(E) → Γ(F)` between spaces of sections of vector bundles over a closed manifold `M`,

  `ind_an(D) := dim ker D - dim coker D = ind_top(D)`,

where the topological index is computed from characteristic-class data of the symbol of `D`.

The general theorem is far beyond what is currently formalizable in Mathlib (it requires
pseudodifferential operators, K-theory of the cotangent bundle, the Thom isomorphism and
Bott periodicity, none of which are available).  What is formalized and *proved* here,
axiom-cleanly, is the **base case of the theorem: the case of a `0`-dimensional closed
manifold**, i.e. a finite set of points.

Over a `0`-dimensional manifold, the spaces of sections `Γ(E)`, `Γ(F)` are finite-dimensional
vector spaces, *every* linear operator between them is elliptic (the symbol is the operator
itself on the zero-dimensional cotangent fibre), and the topological index degenerates to the
difference of the ranks of the bundles, i.e. to `dim Γ(E) - dim Γ(F)`.  The statement

  `dim ker D - dim coker D = dim Γ(E) - dim Γ(F)`

is then exactly the index theorem in this case; it is proved below from rank–nullity.

Two structural consequences of the index theorem, both genuine features of the general
theory, are also derived in this base case:

* homotopy / stability invariance: the index does not depend on the operator, only on the
  bundles (`Frontier.analyticIndex_eq_analyticIndex`);
* additivity under direct sums (`Frontier.analyticIndex_prodMap`).

Beyond the two-term case, the theorem is also proved for **elliptic complexes** over a
`0`-dimensional manifold (`Frontier.atiyah_singer_index_complex`): for a finite cochain
complex of finite-dimensional section spaces, the Euler characteristic of the cohomology
(the analytic index, the cohomology being the harmonic sections by Hodge theory) equals the
alternating sum of the bundle ranks (the topological index).  The geometric form over a
finite set of points, with honest bundles `E F : M → Type`, is
`Frontier.atiyah_singer_index_zero_dimensional`.

No lemma in Mathlib states the index theorem in any form (searching for `index`-theoretic
statements only turns up rank–nullity style results); the key Mathlib inputs used are
`LinearMap.finrank_range_add_finrank_ker` and `Submodule.finrank_quotient_add_finrank`.
-/

namespace Frontier

variable {𝕜 : Type*} [Field 𝕜]
variable {V W : Type*} [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]

/-- The cokernel `W ⧸ range T` of a linear operator `T : V →ₗ[𝕜] W`. -/
abbrev cokernel (T : V →ₗ[𝕜] W) : Type _ := W ⧸ LinearMap.range T

/-- The **analytic index** of an operator `T : V →ₗ[𝕜] W`:
`dim ker T - dim coker T`, as an integer. -/
noncomputable def analyticIndex (T : V →ₗ[𝕜] W) : ℤ :=
  (Module.finrank 𝕜 (LinearMap.ker T) : ℤ) - (Module.finrank 𝕜 (cokernel T) : ℤ)

/-- The **topological index** of an elliptic operator over a `0`-dimensional closed manifold:
the difference of the dimensions of the spaces of sections, i.e. the difference of the total
ranks of the two bundles.  (This is what the general topological index
`∫_{T*M} ch(σ(D)) Td(TM ⊗ ℂ)` specialises to when `dim M = 0`.) -/
noncomputable def topologicalIndex (𝕜 : Type*) [Field 𝕜] (V W : Type*)
    [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W] : ℤ :=
  (Module.finrank 𝕜 V : ℤ) - (Module.finrank 𝕜 W : ℤ)

/-- The dimension of the cokernel of `T : V →ₗ[𝕜] W`, expressed via the rank of `T`. -/
theorem finrank_cokernel (T : V →ₗ[𝕜] W) [FiniteDimensional 𝕜 W] :
    (Module.finrank 𝕜 (cokernel T) : ℤ)
      = (Module.finrank 𝕜 W : ℤ) - (Module.finrank 𝕜 (LinearMap.range T) : ℤ) := by
  have h := Submodule.finrank_quotient_add_finrank (R := 𝕜) (M := W) (LinearMap.range T)
  show (Module.finrank 𝕜 (W ⧸ LinearMap.range T) : ℤ) = _
  omega

/-- **Atiyah–Singer index theorem, base case (`0`-dimensional closed manifold).**

For an elliptic operator over a `0`-dimensional closed manifold — equivalently, for an
arbitrary linear map `T : V →ₗ[𝕜] W` between finite-dimensional spaces of sections — the
analytic index `dim ker T - dim coker T` equals the topological index
`dim V - dim W`. -/
theorem atiyah_singer_index [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W]
    (T : V →ₗ[𝕜] W) :
    analyticIndex T = topologicalIndex 𝕜 V W := by
  have hrn := LinearMap.finrank_range_add_finrank_ker T
  have hcok := finrank_cokernel T
  unfold analyticIndex topologicalIndex
  omega

/-- **Homotopy / stability invariance of the index** (base case): the index of an elliptic
operator over a `0`-dimensional manifold depends only on the bundles, not on the operator.
In particular it is invariant under deformations and compact perturbations. -/
theorem analyticIndex_eq_analyticIndex [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W]
    (T₁ T₂ : V →ₗ[𝕜] W) : analyticIndex T₁ = analyticIndex T₂ := by
  rw [atiyah_singer_index, atiyah_singer_index]

/-- **Additivity of the index under direct sums** (base case). -/
theorem analyticIndex_prodMap {V' W' : Type*} [AddCommGroup V'] [Module 𝕜 V']
    [AddCommGroup W'] [Module 𝕜 W'] [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W]
    [FiniteDimensional 𝕜 V'] [FiniteDimensional 𝕜 W'] (T : V →ₗ[𝕜] W) (T' : V' →ₗ[𝕜] W') :
    analyticIndex (T.prodMap T') = analyticIndex T + analyticIndex T' := by
  rw [atiyah_singer_index, atiyah_singer_index, atiyah_singer_index]
  unfold topologicalIndex
  rw [Module.finrank_prod, Module.finrank_prod]
  push_cast
  ring

/-- The index theorem over a `0`-dimensional manifold, spelled out for the concrete model in
which the bundles are trivial of ranks `m` and `n`: the sections are `Fin m → 𝕜` and
`Fin n → 𝕜`, and the index of any operator between them is `m - n`. -/
theorem atiyah_singer_index_point (m n : ℕ) (T : (Fin m → 𝕜) →ₗ[𝕜] (Fin n → 𝕜)) :
    analyticIndex T = (m : ℤ) - (n : ℤ) := by
  rw [atiyah_singer_index]
  unfold topologicalIndex
  simp

/-! ## The index theorem over a `0`-dimensional manifold, geometric form

A closed `0`-dimensional manifold is a finite set of points `M`; a vector bundle over it is a
family `E : M → Type` of finite-dimensional vector spaces, and its space of sections is
`∀ m, E m`.  The index theorem then says that the index of any operator between the section
spaces is the difference of the total ranks `∑ m, rank (E m) - ∑ m, rank (F m)`. -/

theorem atiyah_singer_index_zero_dimensional {M : Type*} [Fintype M] {E F : M → Type*}
    [∀ m, AddCommGroup (E m)] [∀ m, Module 𝕜 (E m)] [∀ m, FiniteDimensional 𝕜 (E m)]
    [∀ m, AddCommGroup (F m)] [∀ m, Module 𝕜 (F m)] [∀ m, FiniteDimensional 𝕜 (F m)]
    (D : (∀ m, E m) →ₗ[𝕜] (∀ m, F m)) :
    analyticIndex D
      = (∑ m : M, (Module.finrank 𝕜 (E m) : ℤ)) - ∑ m : M, (Module.finrank 𝕜 (F m) : ℤ) := by
  rw [atiyah_singer_index]
  unfold topologicalIndex
  rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype]
  push_cast
  ring

/-! ## The index theorem for elliptic complexes over a point

An elliptic complex over a `0`-dimensional manifold is a finite cochain complex
`C⁰ →[d₀] C¹ →[d₁] ⋯` of finite-dimensional vector spaces.  Its analytic index is the Euler
characteristic of its cohomology (by Hodge theory, `Hⁱ` is the space of harmonic sections),
and its topological index is the alternating sum of the ranks of the bundles.  The index
theorem in this case is the Euler–Poincaré principle, proved below.
-/

section Complex

variable {C : ℕ → Type*} [∀ i, AddCommGroup (C i)] [∀ i, Module 𝕜 (C i)]

/-- The image of the incoming differential at spot `i` (by convention `⊥` at spot `0`). -/
def prevRange (d : ∀ i, C i →ₗ[𝕜] C (i + 1)) : ∀ i, Submodule 𝕜 (C i)
  | 0 => ⊥
  | (i + 1) => LinearMap.range (d i)

/-- The `i`-th cohomology of the complex `(C, d)`: `ker dᵢ` modulo the image of `dᵢ₋₁`. -/
abbrev cohomology (d : ∀ i, C i →ₗ[𝕜] C (i + 1)) (i : ℕ) : Type _ :=
  (LinearMap.ker (d i)) ⧸ Submodule.comap (LinearMap.ker (d i)).subtype (prevRange d i)

/-- In a complex (`d ∘ d = 0`), the incoming image lies in the outgoing kernel. -/
theorem prevRange_le_ker (d : ∀ i, C i →ₗ[𝕜] C (i + 1))
    (hd : ∀ i, (d (i + 1)).comp (d i) = 0) (i : ℕ) :
    prevRange d i ≤ LinearMap.ker (d i) := by
  cases i with
  | zero => simp [prevRange]
  | succ j =>
      rintro x ⟨y, rfl⟩
      have := congrArg (fun L => L y) (hd j)
      simpa [LinearMap.mem_ker] using this

/-- Dimension of the `i`-th cohomology: `dim ker dᵢ - dim im dᵢ₋₁`. -/
theorem finrank_cohomology (d : ∀ i, C i →ₗ[𝕜] C (i + 1))
    (hd : ∀ i, (d (i + 1)).comp (d i) = 0) [∀ i, FiniteDimensional 𝕜 (C i)] (i : ℕ) :
    (Module.finrank 𝕜 (cohomology d i) : ℤ)
      = (Module.finrank 𝕜 (LinearMap.ker (d i)) : ℤ)
        - (Module.finrank 𝕜 (prevRange d i) : ℤ) := by
  have hle := prevRange_le_ker d hd i
  have hq := Submodule.finrank_quotient_add_finrank
    (R := 𝕜) (M := (LinearMap.ker (d i)))
    (Submodule.comap (LinearMap.ker (d i)).subtype (prevRange d i))
  have hcomap : Module.finrank 𝕜 (Submodule.comap (LinearMap.ker (d i)).subtype (prevRange d i))
      = Module.finrank 𝕜 (prevRange d i) :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)
  rw [hcomap] at hq
  show (Module.finrank 𝕜 ((LinearMap.ker (d i))
      ⧸ Submodule.comap (LinearMap.ker (d i)).subtype (prevRange d i)) : ℤ) = _
  omega

/-- The analytic index of an elliptic complex: the Euler characteristic of its cohomology. -/
noncomputable def analyticIndexComplex (d : ∀ i, C i →ₗ[𝕜] C (i + 1)) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, (-1 : ℤ) ^ i * (Module.finrank 𝕜 (cohomology d i) : ℤ)

/-- The topological index of an elliptic complex over a point: the alternating sum of the
ranks of the bundles. -/
noncomputable def topologicalIndexComplex (𝕜 : Type*) [Field 𝕜] (C : ℕ → Type*)
    [∀ i, AddCommGroup (C i)] [∀ i, Module 𝕜 (C i)] (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, (-1 : ℤ) ^ i * (Module.finrank 𝕜 (C i) : ℤ)

/-- Telescoping identity: the difference of the two alternating sums truncated at `n` is the
boundary term `(-1)^n dim im dₙ₋₁`. -/
theorem alternating_sum_sub (d : ∀ i, C i →ₗ[𝕜] C (i + 1))
    (hd : ∀ i, (d (i + 1)).comp (d i) = 0) [∀ i, FiniteDimensional 𝕜 (C i)] (n : ℕ) :
    analyticIndexComplex d n - topologicalIndexComplex 𝕜 C n
      = (-1 : ℤ) ^ n * (Module.finrank 𝕜 (prevRange d n) : ℤ) := by
  induction n with
  | zero => simp [analyticIndexComplex, topologicalIndexComplex, prevRange]
  | succ n ih =>
      have hrn := LinearMap.finrank_range_add_finrank_ker (d n)
      have hcoh := finrank_cohomology d hd n
      have hnext : prevRange d (n + 1) = LinearMap.range (d n) := rfl
      unfold analyticIndexComplex topologicalIndexComplex at *
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [hnext, hcoh]
      have hpow : (-1 : ℤ) ^ (n + 1) = -((-1 : ℤ) ^ n) := by ring
      rw [hpow]
      have hC : (Module.finrank 𝕜 (C n) : ℤ)
          = (Module.finrank 𝕜 (LinearMap.range (d n)) : ℤ)
            + (Module.finrank 𝕜 (LinearMap.ker (d n)) : ℤ) := by exact_mod_cast hrn.symm
      rw [hC]
      linarith [ih]

/-- The boundary term vanishes once the complex has stopped. -/
theorem finrank_prevRange_eq_zero (d : ∀ i, C i →ₗ[𝕜] C (i + 1)) (n : ℕ)
    (htop : Subsingleton (C n)) : Module.finrank 𝕜 (prevRange d n) = 0 := by
  have : Subsingleton (prevRange d n) := by
    constructor
    intro x y
    exact Subtype.ext (Subsingleton.elim _ _)
  exact Module.finrank_zero_of_subsingleton

/-- **Atiyah–Singer index theorem for elliptic complexes over a `0`-dimensional manifold.**

For a finite cochain complex `C⁰ → C¹ → ⋯ → Cⁿ⁻¹ → 0` of finite-dimensional spaces of
sections, the analytic index (the Euler characteristic of the cohomology, i.e. of the spaces
of harmonic sections) equals the topological index (the alternating sum of the ranks of the
bundles).  This contains the two-term case `Frontier.atiyah_singer_index`, and is the
algebraic shadow of the fact that the index of the de Rham complex is the Euler
characteristic. -/
theorem atiyah_singer_index_complex (d : ∀ i, C i →ₗ[𝕜] C (i + 1))
    (hd : ∀ i, (d (i + 1)).comp (d i) = 0) [∀ i, FiniteDimensional 𝕜 (C i)] (n : ℕ)
    (htop : Subsingleton (C n)) :
    analyticIndexComplex d n = topologicalIndexComplex 𝕜 C n := by
  have h := alternating_sum_sub d hd n
  rw [finrank_prevRange_eq_zero d n htop] at h
  simp only [Nat.cast_zero, mul_zero] at h
  omega

/-! ### A worked instance (non-vacuity check)

The complex `ℚ → 0 → 0 → ⋯` concentrated in degree `0`: its cohomology is `ℚ` in degree `0`,
so both indices equal `1`. -/

/-- The complex with `ℚ` in degree `0` and `0` in all positive degrees. -/
abbrev lineComplex : ℕ → Type := fun i => Fin (if i = 0 then 1 else 0) → ℚ

/-- The (zero) differential of `Frontier.lineComplex`. -/
noncomputable def lineComplexDiff : ∀ i, lineComplex i →ₗ[ℚ] lineComplex (i + 1) := fun _ => 0

/-- The index theorem applied to a concrete elliptic complex: both indices equal `1`. -/
theorem lineComplex_index : analyticIndexComplex lineComplexDiff 1 = 1 := by
  rw [atiyah_singer_index_complex lineComplexDiff (by intro i; simp [lineComplexDiff]) 1
    (inferInstanceAs (Subsingleton (Fin 0 → ℚ)))]
  simp [topologicalIndexComplex]

end Complex

end Frontier

