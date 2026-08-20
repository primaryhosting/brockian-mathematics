import Mathlib

/-!
# Abstract machinery for paradoxical decompositions

This file develops the general theory needed for the Banach–Tarski paradox, on top of
Mathlib's `Equidecomp` (equidecompositions for a group action).
-/

open Set Function Pointwise

namespace BT

variable {X G H : Type*} [Nonempty X] [Group G] [MulAction G X]

/-- Build an equidecomposition out of a function which is a bijection from `A` to `B` and
moves every point of `A` by an element of a fixed finite set of group elements. -/

lemma ball_paradoxical : Paradoxical Isom (closedBall (0 : E) 1) := by
  have hbase : Paradoxical Isom (closedBall (0 : E) 1 \ {0}) :=
    punctured_ball_paradoxical.map O3.toIsom O3.toIsom_smul
  have hneg : ∀ (N : O3) (y : E), N • (-y) = -(N • y) := by
    intro N y
    have h := O3.smul_smul_real N (-1 : ℝ) y
    simp only [neg_smul, one_smul] at h
    exact h
  set p : E := (1/2 : ℝ) • e2 with hp
  have hnp : ‖p‖ = 1/2 := by
    rw [hp, norm_smul, norm_e2]; norm_num
  set M : O3 := Phi (FreeGroup.of 0) with hM
  set ρ : Isom := (IsometryEquiv.addLeft p) * (O3.toIsom M) * (IsometryEquiv.addLeft (-p)) with hρ
  have hρapp : ∀ x : E, ρ • x = p + M • (x - p) := by
    intro x
    rw [Isom.smul_def, hρ, IsometryEquiv.mul_apply, IsometryEquiv.mul_apply]
    show p + M • (-p + x) = p + M • (x - p)
    rw [neg_add_eq_sub]
  have hpow : ∀ (n : ℕ) (x : E), (ρ ^ n) • x = p + (M ^ n) • (x - p) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ m ih =>
        intro x
        rw [pow_succ', SemigroupAction.mul_smul, ih x, hρapp, pow_succ',
          SemigroupAction.mul_smul]
        simp
  have horb : ∀ n : ℕ, (ρ ^ n) • (0 : E) = p - (M ^ n) • p := by
    intro n
    rw [hpow n 0, zero_sub, hneg]
    abel
  have hball : ∀ n : ℕ, (ρ ^ n) • (0 : E) ∈ closedBall (0 : E) 1 := by
    intro n
    rw [mem_closedBall, dist_zero_right, horb n]
    calc ‖p - (M ^ n) • p‖ ≤ ‖p‖ + ‖(M ^ n) • p‖ := norm_sub_le _ _
      _ = 1 := by rw [O3.norm_smul, hnp]; norm_num
  have hne0 : ∀ n : ℕ, 1 ≤ n → (ρ ^ n) • (0 : E) ≠ 0 := by
    intro n hn hc
    rw [horb n, sub_eq_zero] at hc
    have hword : (FreeGroup.of (0 : Fin 2)) ^ n ≠ 1 := by
      intro h
      have h2 := congrArg
        (FreeGroup.lift (fun i : Fin 2 => if i = 0 then (Multiplicative.ofAdd (1 : ℤ)) else 1)) h
      simp [map_pow] at h2
      omega
    refine Phi_smul_e2_ne _ hword ?_
    rw [map_pow, ← hM]
    have h3 : (M ^ n) • ((1/2 : ℝ) • e2) = (1/2 : ℝ) • ((M ^ n) • e2) :=
      O3.smul_smul_real _ _ _
    rw [hp, h3] at hc
    exact smul_right_injective E (by norm_num : (1/2 : ℝ) ≠ 0) hc.symm
  have hsub : ∀ n : ℕ, (ρ ^ n) • ({0} : Set E) ⊆ closedBall (0 : E) 1 := by
    intro n
    rw [Set.smul_set_singleton]
    simpa using hball n
  have hdisj : ∀ n : ℕ, 1 ≤ n → Disjoint ((ρ ^ n) • ({0} : Set E)) ({0} : Set E) := by
    intro n hn
    rw [Set.smul_set_singleton]
    simpa using hne0 n hn
  obtain ⟨e, hes, het⟩ :=
    exists_equidecomp_sdiff (A := closedBall (0 : E) 1) (D := ({0} : Set E)) ρ hsub hdisj
  exact Paradoxical.of_equidecomp e.symm het hes hbase

end BT

/-- **The Banach–Tarski paradox.** The closed unit ball of `ℝ³` admits a paradoxical
decomposition: it contains two disjoint subsets, each of which can be cut into finitely many
pieces which, after moving each piece by an isometry of `ℝ³`, reassemble to the whole ball.

Here `Equidecomp E Isom` is Mathlib's notion of an equidecomposition for the action of the
isometry group of `E = ℝ³`: a partial bijection of `E` whose source is cut into finitely many
pieces, each of which is moved by a single isometry onto the corresponding piece of the target.
-/
