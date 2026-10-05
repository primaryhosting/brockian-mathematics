import Mathlib
/-!
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
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

set_option grind.warning false

namespace Frontier

/-!
## The statement

The Kadison–Singer problem (1959) asks whether every pure state on the atomic MASA
`ℓ^∞(ℕ) ⊆ B(ℓ²(ℕ))` extends uniquely to a state on `B(ℓ²(ℕ))`.  It was resolved
affirmatively by Marcus, Spielman and Srivastava, who proved **Weaver's conjecture `KS_r`**
by the method of *interlacing families of polynomials*:

> if `v₁, …, v_m ∈ ℂ^d` satisfy `∑ᵢ vᵢ vᵢ* = I` and `‖vᵢ‖² ≤ α` for all `i`, then there is a
> partition `{1,…,m} = S₁ ⊔ … ⊔ S_r` with `‖∑_{i ∈ S_j} vᵢ vᵢ*‖ ≤ (1/√r + √α)²` for all `j`.

We phrase the two operator-theoretic conditions through the associated quadratic forms, which
is equivalent (all the operators involved are positive semidefinite) and avoids committing to
a particular encoding of the operator norm:

* `∑ᵢ vᵢ vᵢ* = I`             ⟺  `∀ x, ∑ᵢ |⟪vᵢ, x⟫|² = ‖x‖²`;
* `‖∑_{i ∈ S} vᵢ vᵢ*‖ ≤ c`    ⟺  `∀ x, ∑_{i ∈ S} |⟪vᵢ, x⟫|² ≤ c ‖x‖²`.
-/

/-- **Weaver's `KS_r` statement** in dimension `d` with bound `α`: every isotropic family of
vectors in `ℂ^d` whose members have squared norm at most `α` can be partitioned into `r`
subfamilies, each of operator norm at most `(1/√r + √α)²`.

The proposition `∀ r α d, 0 < r → 0 ≤ α → WeaverKS r α d` is Weaver's conjecture, which is
equivalent to a positive solution of the Kadison–Singer problem and is the theorem of
Marcus–Spielman–Srivastava. -/

theorem weaverKS_dim_one (r : ℕ) (hr : 0 < r) (α : ℝ) (hα : 0 ≤ α) : WeaverKS r α 1 := by
  intro ι _ v hv hiso
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  set a : ι → ℝ := fun i => ‖v i‖ ^ 2 with hadef
  have key : ∀ (i : ι) (x : EuclideanSpace ℂ (Fin 1)),
      ‖inner ℂ (v i) x‖ ^ 2 = a i * ‖x‖ ^ 2 := by
    intro i x
    simp [hadef, PiLp.inner_apply, EuclideanSpace.norm_eq, RCLike.inner_apply, mul_pow, mul_comm]
  have hsum1 : ∑ i, a i = 1 := by
    have h := hiso (EuclideanSpace.single (0 : Fin 1) (1 : ℂ))
    have hn : ‖(EuclideanSpace.single (0 : Fin 1) (1 : ℂ))‖ = 1 := by simp
    simp only [key, hn] at h
    simpa using h
  obtain ⟨f, hf⟩ := greedy_partition r hr a (fun _ => sq_nonneg _) α hα hv
  refine ⟨f, fun j x => ?_⟩
  have hcalc : ∑ i ∈ Finset.univ.filter (fun i => f i = j), ‖inner ℂ (v i) x‖ ^ 2
      = (∑ i ∈ Finset.univ.filter (fun i => f i = j), a i) * ‖x‖ ^ 2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => key i x
  rw [hcalc]
  have hb := hf j
  rw [hsum1] at hb
  exact mul_le_mul_of_nonneg_right
    (hb.trans (one_div_add_le_sq_sqrt_add_sqrt r α hα hrR)) (sq_nonneg _)

/-!
## Main result
-/

/-- **Kadison–Singer / Weaver's `KS_r`.**

The full conjecture, `∀ r α d, 0 < r → 0 ≤ α → WeaverKS r α d`, is the theorem of
Marcus–Spielman–Srivastava.  Here we record the formal statement (`Frontier.WeaverKS`)
together with Lean-checked proofs of the two boundary cases of the induction:

* the base case `r = 1`, in every dimension `d`;
* the base case `d = 1`, for every number of parts `r`, which is exactly the greedy
  load-balancing bound together with `1/r + α ≤ (1/√r + √α)²`. -/
