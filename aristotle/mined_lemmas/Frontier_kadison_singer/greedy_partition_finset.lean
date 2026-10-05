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

theorem greedy_partition_finset {ι : Type} [DecidableEq ι] (r : ℕ) (hr : 0 < r) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (α : ℝ) (hα0 : 0 ≤ α) (hα : ∀ i, a i ≤ α) (s : Finset ι) :
    ∃ f : ι → Fin r, ∀ j : Fin r,
      ∑ i ∈ s.filter (fun i => f i = j), a i ≤ (∑ i ∈ s, a i) / r + α := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => ⟨0, hr⟩, fun j => by simp [hα0]⟩
  | insert x s hx ih =>
      obtain ⟨f, hf⟩ := ih
      set L : Fin r → ℝ := fun j => ∑ i ∈ s.filter (fun i => f i = j), a i with hL
      obtain ⟨j₀, -, hj₀⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin r)) L
        ⟨⟨0, hr⟩, Finset.mem_univ _⟩
      have hsum : ∑ j, L j = ∑ i ∈ s, a i := Finset.sum_fiberwise s f a
      -- a least-loaded bin carries at most the average load
      have hmin : L j₀ ≤ (∑ i ∈ s, a i) / r := by
        have h1 := Finset.card_nsmul_le_sum (Finset.univ : Finset (Fin r)) L (L j₀)
          (fun j _ => hj₀ j (Finset.mem_univ j))
        rw [hsum] at h1
        simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
        rw [le_div_iff₀ hrR]
        linarith
      refine ⟨Function.update f x j₀, fun j => ?_⟩
      have hupd : ∀ i ∈ s, Function.update f x j₀ i = f i := fun i hi =>
        Function.update_of_ne (by rintro rfl; exact hx hi) _ _
      have hax : 0 ≤ a x := ha x
      have hstep : (∑ i ∈ s, a i) / r ≤ (∑ i ∈ insert x s, a i) / r := by
        rw [Finset.sum_insert hx]; gcongr; linarith
      have hfil :
          s.filter (fun i => Function.update f x j₀ i = j) = s.filter (fun i => f i = j) :=
        Finset.filter_congr fun i hi => by rw [hupd i hi]
      rw [Finset.filter_insert]
      by_cases hj : j₀ = j
      · subst hj
        rw [if_pos (Function.update_self x j₀ f), hfil,
          Finset.sum_insert fun h => hx (Finset.mem_of_mem_filter _ h)]
        have hle : L j₀ ≤ (∑ i ∈ insert x s, a i) / r := hmin.trans hstep
        simp only [hL] at hle
        linarith [hα x]
      · rw [if_neg (by simpa [Function.update_self] using hj), hfil]
        linarith [hf j]

/-- Greedy load balancing over a fintype. -/
