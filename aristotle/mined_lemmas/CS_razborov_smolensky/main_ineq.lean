import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem main_ineq {p q d c : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hfam : ∀ n : ℕ, ∃ C : Circuit, C.depth ≤ d ∧ C.size ≤ (n + 2) ^ c ∧ Computes q n C (MOD p n))
    (m : ℕ) :
    3 * 4 ^ m ≤ 8 * (((tval p c m * (q - 1)) ^ d + 1) * ((2 * m).choose m)) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  set F := AlgebraicClosure (ZMod q) with hFdef
  set n := 2 * m with hn
  set t := tval p c m with htdef
  set D := (t * (q - 1)) ^ d with hDdef
  have hq2 : 2 ≤ q := hq.two_le
  have ht : 1 ≤ t := one_le_tval p c m
  have hbase : 1 ≤ t * (q - 1) := by
    have := Nat.mul_le_mul ht (show 1 ≤ q - 1 by omega)
    simpa using this
  -- a `p`-th root of unity in an algebraically closed field of characteristic `q`
  have hpF : ((p : F)) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F q p]
    intro hdvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 hdvd).symm
  obtain ⟨ζ, hζp, hζ1⟩ := exists_root_of_unity F p hp hpF
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, zero_pow hp.pos.ne'] at hζp
    exact zero_ne_one hζp
  -- approximating polynomials for the `p` shifted `MOD p` functions
  set S := (n + p + 2) ^ c with hS
  have hchoice : ∀ a : Fin p, ∃ P : Cube n → F, P ∈ Deg F n D ∧
      2 ^ t * #(errSet P (fun x => decide ((wt x + (a : ℕ)) % p = 0))) ≤ S * 2 ^ n := by
    intro a
    obtain ⟨C, hCd, hCs, hCc⟩ := hfam (n + (a : ℕ))
    obtain ⟨P, hP, hPe⟩ := circuit_approx (F := F) (q := q) (n := n)
        (β := fun i => decide (i < n + (a : ℕ))) t ht C
    have hev : (fun x : Cube n => C.eval q (ext (fun i => decide (i < n + (a : ℕ))) x))
        = (fun x => decide ((wt x + (a : ℕ)) % p = 0)) := by
      funext x
      rw [hCc _ (supported_ext _ x)]
      unfold CS.MOD
      rw [popCount_ext]
    refine ⟨P, mem_Deg_of_le hP (Nat.pow_le_pow_right hbase hCd), ?_⟩
    rw [← hev]
    refine le_trans hPe (Nat.mul_le_mul_right _ (le_trans hCs ?_))
    exact Nat.pow_le_pow_left (by have := a.2; omega) c
  choose Pf hPf1 hPf2 using hchoice
  set bad := univ.biUnion
    (fun a : Fin p => errSet (Pf a) (fun x => decide ((wt x + (a : ℕ)) % p = 0))) with hbad
  set A := (univ : Finset (Cube n)) \ bad with hAdef
  -- the total error is small
  have hcube : #(univ : Finset (Cube n)) = 2 ^ n := card_cube n
  have hstep : 2 ^ t * #bad ≤ p * (S * 2 ^ n) := by
    have h1 : #bad ≤ ∑ a : Fin p,
        #(errSet (Pf a) (fun x => decide ((wt x + (a : ℕ)) % p = 0))) := Finset.card_biUnion_le
    calc 2 ^ t * #bad ≤ 2 ^ t * ∑ a : Fin p,
          #(errSet (Pf a) (fun x => decide ((wt x + (a : ℕ)) % p = 0))) :=
            Nat.mul_le_mul_left _ h1
      _ = ∑ a : Fin p, 2 ^ t *
            #(errSet (Pf a) (fun x => decide ((wt x + (a : ℕ)) % p = 0))) := Finset.mul_sum _ _ _
      _ ≤ ∑ _a : Fin p, S * 2 ^ n := Finset.sum_le_sum fun a _ => hPf2 a
      _ = p * (S * 2 ^ n) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
  have h8bad : 8 * #bad ≤ 2 ^ n := by
    have hpow : 0 < 2 ^ t := Nat.two_pow_pos t
    refine Nat.le_of_mul_le_mul_left ?_ hpow
    calc 2 ^ t * (8 * #bad) = 8 * (2 ^ t * #bad) := by ring
      _ ≤ 8 * (p * (S * 2 ^ n)) := Nat.mul_le_mul_left _ hstep
      _ = (8 * p * S) * 2 ^ n := by ring
      _ ≤ 2 ^ t * 2 ^ n := Nat.mul_le_mul_right _ (eight_mul_le_two_pow_tval p c m)
  have hAcard : 7 * 2 ^ n ≤ 8 * #A := by
    have hsub : bad ⊆ (univ : Finset (Cube n)) := Finset.subset_univ _
    have hcs : #A + #bad = 2 ^ n := by
      rw [hAdef, Finset.card_sdiff_add_card_eq_card hsub, hcube]
    omega
  -- the interpolating polynomial
  have hPcomb : (∑ a : Fin p, ζ ^ (p - (a : ℕ)) • Pf a) ∈ Deg F n D :=
    Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hPf1 a)
  have hAval : ∀ x ∈ A, UU ζ univ x = (∑ a : Fin p, ζ ^ (p - (a : ℕ)) • Pf a) x := by
    intro x hxA
    have hx : ∀ a : Fin p, Pf a x = bitv F (decide ((wt x + (a : ℕ)) % p = 0)) := by
      intro a
      by_contra hc
      exact (Finset.mem_sdiff.1 hxA).2
        (Finset.mem_biUnion.2 ⟨a, Finset.mem_univ a, mem_errSet.2 hc⟩)
    rw [UU_univ_apply, Finset.sum_apply, ← sum_zeta_eq hp.pos hζp (wt x)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, hx a]
    congr 1
    by_cases h : (wt x + (a : ℕ)) % p = 0 <;> simp [h, bitv]
  have hsmol := smolensky_dim (F := F) (n := n) (m := m) (D := D) hn hζ0 hζ1 A _ hPcomb hAval
  -- combine with the binomial estimate
  have hbin := two_mul_sum_choose_le m D
  have hbin' : 2 * (∑ i ∈ Finset.range (m + D + 1), (2 * m).choose i)
      ≤ 4 ^ m + 2 * ((D + 1) * ((2 * m).choose m)) := by
    calc 2 * (∑ i ∈ Finset.range (m + D + 1), (2 * m).choose i)
        ≤ 4 ^ m + 2 * (D + 1) * ((2 * m).choose m) := hbin
      _ = 4 ^ m + 2 * ((D + 1) * ((2 * m).choose m)) := by ring
  have h2n : (2 : ℕ) ^ n = 4 ^ m := by
    rw [hn, pow_mul]
    norm_num
  rw [h2n] at hAcard
  rw [← hn] at hbin'
  omega

/-! ### Sanity check: the class is nonempty and contains `MOD q` -/

