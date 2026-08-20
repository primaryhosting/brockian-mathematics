/-
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace CS

/-! ## Boolean circuits

We use a term representation of Boolean circuits, but we measure their size in the
*DAG* sense: the size of a circuit is the number of distinct subcircuits occurring in
it (equivalently, the number of gates when identical subcircuits are shared). -/

/-- Boolean circuits on `n` input variables. -/
inductive Circ (n : ℕ) where
  | var : Fin n → Circ n
  | const : Bool → Circ n
  | not : Circ n → Circ n
  | and : Circ n → Circ n → Circ n
  | or : Circ n → Circ n → Circ n
  deriving DecidableEq

namespace Circ

/-- The Boolean function computed by a circuit. -/

lemma nw_hybrid_step {ℓ d m α s : ℕ} {ε : ℝ}
    (e : Fin m → (Fin ℓ ↪ Fin d))
    (hdesign : ∀ i j : Fin m, i ≠ j →
      ((Finset.univ.image (e i)) ∩ (Finset.univ.image (e j))).card ≤ α)
    (f : (Fin ℓ → Bool) → Bool)
    (hhard : ∀ C : Circ ℓ, C.size ≤ s →
      ((Finset.univ.filter (fun x : Fin ℓ → Bool => C.eval x = f x)).card : ℝ)
        ≤ (1 / 2 + ε / m) * 2 ^ ℓ)
    (D : Circ m) (hD : D.size + m * (7 * 2 ^ α) + 1 ≤ s) (i : Fin m) :
    |hybAcc e f D ((i : ℕ) + 1) - hybAcc e f D (i : ℕ)| ≤ ε / m := by
  classical
  set SB : (Fin d → Bool) → (Fin ℓ → Bool) → (Fin d → Bool) := setBlock (e i) with hSB
  set Aval : (Fin d → Bool) → (Fin m → Bool) → Bool → Bool :=
    fun z y b => D.eval (nwStr e f i z y b) with hAval
  set dfun : (Fin d → Bool) → (Fin m → Bool) → ℝ :=
    fun z y => b2r (Aval z y (f (z ∘ e i))) - b2r (Aval z y (y i)) with hdfun
  set Δ : ℝ := hybAcc e f D ((i : ℕ) + 1) - hybAcc e f D (i : ℕ) with hΔ
  have hpow : (0:ℝ) < 2 ^ d * 2 ^ m := by positivity
  have hΔeq : (∑ z : Fin d → Bool, ∑ y : Fin m → Bool, dfun z y) = (2 ^ d * 2 ^ m) * Δ := by
    rw [hΔ, hybAcc_succ_sub e f D i, hdfun, hAval]
    field_simp
  set flipAt : (Fin m → Bool) → (Fin m → Bool) := fun y => Function.update y i (!(y i))
    with hflipAt
  have hflip_i : ∀ y : Fin m → Bool, flipAt y i = !(y i) := by
    intro y; simp [hflipAt]
  have hflip_ne : ∀ (y : Fin m → Bool) (j : Fin m), j ≠ i → flipAt y j = y j := by
    intro y j hj; simp [hflipAt, Function.update_of_ne hj]
  have hflipinv : Function.Involutive flipAt := by
    intro y
    funext j
    by_cases hj : j = i
    · subst hj; simp [hflip_i]
    · rw [hflip_ne _ _ hj, hflip_ne _ _ hj]
  have hAflip : ∀ (z : Fin d → Bool) (y : Fin m → Bool) (b : Bool),
      Aval z (flipAt y) b = Aval z y b := by
    intro z y b
    have hs : nwStr e f i z (flipAt y) b = nwStr e f i z y b := by
      funext j
      by_cases hj : (j : ℕ) < (i : ℕ)
      · simp [nwStr, hj]
      · by_cases hji : j = i
        · simp [nwStr, hji]
        · simp [nwStr, hj, hji, hflip_ne y j hji]
    simp only [hAval, hs]
  have main : ∀ neg : Bool, (if neg then -Δ else Δ) ≤ ε / m := by
    intro neg
    set sgn : ℝ := if neg then -1 else 1 with hsgn
    set Fcorr : (Fin d → Bool) → (Fin ℓ → Bool) → (Fin m → Bool) → ℝ :=
      fun z x y => agree (xor neg ((Aval (SB z x) y (y i)) == y i)) (f x) with hFcorr
    -- averaging over the random bit in position `i`
    have hS1 : ∀ (z : Fin d → Bool) (x : Fin ℓ → Bool),
        ∑ y : Fin m → Bool, Fcorr z x y
          = ∑ y : Fin m → Bool, (1 / 2 + sgn * dfun (SB z x) y) := by
      intro z x
      refine sum_eq_of_pair flipAt hflipinv _ _ ?_
      intro y
      have hfx : f (SB z x ∘ e i) = f x := by rw [hSB, setBlock_comp]
      have hcond : ∀ b : Bool,
          cond b (Aval (SB z x) y true) (Aval (SB z x) y false) = Aval (SB z x) y b := by
        intro b; cases b <;> rfl
      have e1 : Fcorr z x y
          = agree (xor neg ((cond (y i) (Aval (SB z x) y true) (Aval (SB z x) y false)) == y i))
              (f x) := by
        simp only [hFcorr, hcond]
      have e2 : Fcorr z x (flipAt y)
          = agree (xor neg
              ((cond (!(y i)) (Aval (SB z x) y true) (Aval (SB z x) y false)) == !(y i)))
              (f x) := by
        simp only [hFcorr, hflip_i, hAflip, hcond]
      have e3 : dfun (SB z x) y
          = b2r (cond (f x) (Aval (SB z x) y true) (Aval (SB z x) y false))
            - b2r (cond (y i) (Aval (SB z x) y true) (Aval (SB z x) y false)) := by
        simp only [hdfun, hfx, hcond]
      have e4 : dfun (SB z x) (flipAt y)
          = b2r (cond (f x) (Aval (SB z x) y true) (Aval (SB z x) y false))
            - b2r (cond (!(y i)) (Aval (SB z x) y true) (Aval (SB z x) y false)) := by
        simp only [hdfun, hfx, hflip_i, hAflip, hcond]
      rw [e1, e2, e3, e4, hsgn]
      linear_combination nw_pair_identity (Aval (SB z x) y false) (Aval (SB z x) y true)
        (y i) (f x) neg
    -- summing over the fixed part of the seed and the remaining random bits
    have hstep1 : ∀ (z : Fin d → Bool) (x : Fin ℓ → Bool),
        ∑ y : Fin m → Bool, Fcorr z x y
          = 2 ^ m * (1 / 2) + sgn * (∑ y : Fin m → Bool, dfun (SB z x) y) := by
      intro z x
      rw [hS1 z x, Finset.sum_add_distrib, ← Finset.mul_sum]
      congr 1
      have hcm : ((Fintype.card (Fin m → Bool) : ℕ) : ℝ) = 2 ^ m := by simp
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcm]
    have hK : ∑ z : Fin d → Bool, ∑ x : Fin ℓ → Bool, ∑ y : Fin m → Bool, Fcorr z x y
        = 2 ^ d * 2 ^ ℓ * 2 ^ m * (1 / 2) + sgn * (2 ^ ℓ * ((2 ^ d * 2 ^ m) * Δ)) := by
      have hc1 : ∑ z : Fin d → Bool, ∑ x : Fin ℓ → Bool, ∑ y : Fin m → Bool, Fcorr z x y
          = ∑ z : Fin d → Bool, ∑ x : Fin ℓ → Bool,
              (2 ^ m * (1 / 2) + sgn * (∑ y : Fin m → Bool, dfun (SB z x) y)) :=
        Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (fun x _ => hstep1 z x))
      rw [hc1]
      have hc2 : ∑ z : Fin d → Bool, ∑ x : Fin ℓ → Bool,
            (2 ^ m * (1 / 2) + sgn * (∑ y : Fin m → Bool, dfun (SB z x) y))
          = (∑ _z : Fin d → Bool, ∑ _x : Fin ℓ → Bool, (2:ℝ) ^ m * (1 / 2))
            + sgn * (∑ z : Fin d → Bool, ∑ x : Fin ℓ → Bool,
                (∑ y : Fin m → Bool, dfun (SB z x) y)) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hc2]
      have hc3 : (∑ z : Fin d → Bool, ∑ x : Fin ℓ → Bool,
            (∑ y : Fin m → Bool, dfun (SB z x) y))
          = 2 ^ ℓ * ((2 ^ d * 2 ^ m) * Δ) := by
        rw [hSB]
        rw [sum_setBlock (e i) (fun z' => ∑ y : Fin m → Bool, dfun z' y), hΔeq]
      rw [hc3]
      congr 1
      have hcd : ((Fintype.card (Fin d → Bool) : ℕ) : ℝ) = 2 ^ d := by simp
      have hcl : ((Fintype.card (Fin ℓ → Bool) : ℕ) : ℝ) = 2 ^ ℓ := by simp
      rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
        nsmul_eq_mul, nsmul_eq_mul, hcd, hcl]
      ring
    -- an averaging argument fixes the seed outside block `i` and the remaining random bits
    have hpig : ∃ (z₀ : Fin d → Bool) (y₀ : Fin m → Bool),
        2 ^ ℓ * (1 / 2 + sgn * Δ) ≤ ∑ x : Fin ℓ → Bool, Fcorr z₀ x y₀ := by
      by_contra hcon
      push_neg at hcon
      have hlt : ∑ z : Fin d → Bool, ∑ y : Fin m → Bool, ∑ x : Fin ℓ → Bool, Fcorr z x y
          < ∑ _z : Fin d → Bool, ∑ _y : Fin m → Bool, (2:ℝ) ^ ℓ * (1 / 2 + sgn * Δ) := by
        refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun z _ => ?_)
        exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun y _ => hcon z y)
      have hswap : ∑ z : Fin d → Bool, ∑ y : Fin m → Bool, ∑ x : Fin ℓ → Bool, Fcorr z x y
          = ∑ z : Fin d → Bool, ∑ x : Fin ℓ → Bool, ∑ y : Fin m → Bool, Fcorr z x y :=
        Finset.sum_congr rfl (fun z _ => Finset.sum_comm)
      have hrhs : (∑ _z : Fin d → Bool, ∑ _y : Fin m → Bool, (2:ℝ) ^ ℓ * (1 / 2 + sgn * Δ))
          = 2 ^ d * 2 ^ ℓ * 2 ^ m * (1 / 2) + sgn * (2 ^ ℓ * ((2 ^ d * 2 ^ m) * Δ)) := by
        have hcd : ((Fintype.card (Fin d → Bool) : ℕ) : ℝ) = 2 ^ d := by simp
        have hcm : ((Fintype.card (Fin m → Bool) : ℕ) : ℝ) = 2 ^ m := by simp
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
          nsmul_eq_mul, nsmul_eq_mul, hcd, hcm]
        ring
      rw [hswap, hK, hrhs] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨z₀, y₀, hz⟩ := hpig
    obtain ⟨C, hCsize, hCeval⟩ := nw_predictor_circuit e hdesign f D i z₀ y₀ neg
    have hcard : ∑ x : Fin ℓ → Bool, Fcorr z₀ x y₀
        = ((Finset.univ.filter (fun x : Fin ℓ → Bool => C.eval x = f x)).card : ℝ) := by
      rw [← Finset.sum_boole]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [hCeval x]
      simp only [hFcorr, agree, hAval, hSB]
    have hle : ∑ x : Fin ℓ → Bool, Fcorr z₀ x y₀ ≤ (1 / 2 + ε / m) * 2 ^ ℓ := by
      rw [hcard]
      exact hhard C (by omega)
    have hfin : 2 ^ ℓ * (1 / 2 + sgn * Δ) ≤ (1 / 2 + ε / m) * 2 ^ ℓ := le_trans hz hle
    have h2l : (0:ℝ) < 2 ^ ℓ := by positivity
    rw [mul_comm ((2:ℝ) ^ ℓ)] at hfin
    have h3 : (1 / 2 + sgn * Δ) ≤ (1 / 2 + ε / m) := le_of_mul_le_mul_right hfin h2l
    have h4 : sgn * Δ ≤ ε / m := by linarith
    rw [hsgn] at h4
    cases neg
    · norm_num at h4 ⊢
      linarith
    · norm_num at h4 ⊢
      linarith
  rw [abs_le]
  constructor
  · have h := main true
    norm_num at h
    linarith
  · have h := main false
    norm_num at h
    linarith

/-- **The Nisan-Wigderson pseudorandom generator.**

Let `e 0, …, e (m-1)` be a combinatorial design: `m` blocks of `ℓ` coordinates inside a seed of
`d` coordinates, any two of which intersect in at most `α` positions.  Let `f` be a Boolean
function on `ℓ` bits which is average-case hard, in the sense that no circuit of size at most
`s` agrees with `f` on more than a `1/2 + ε/m` fraction of the inputs.

Then the Nisan-Wigderson generator `z ↦ (f (z ∘ e 0), …, f (z ∘ e (m-1)))`, stretching `d`
random bits to `m` bits, fools every circuit `D` of size at most `s - m · 7 · 2 ^ α - 1`: the
acceptance probabilities of `D` on the output of the generator and on a uniformly random
`m`-bit string differ by at most `ε`. -/
