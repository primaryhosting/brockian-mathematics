import Mathlib

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We formalise the finite-volume Lieb-Schultz-Mattis theorem for a periodic spin-`1/2`
(hence half-integer spin) chain of `L` sites.

The Hilbert space is the space of functions on spin configurations `Cfg L = ZMod L → Bool`
(each site carries two states, `S^z_j = ±1/2`).  A Hamiltonian is given by its matrix
elements `H : Cfg L → Cfg L → ℂ`.  The physical hypotheses are:

* `hherm`  : `H` is Hermitian;
* `htrans` : `H` is invariant under the lattice translation `shiftCfg`;
* `hloc`   : off-diagonal matrix elements only connect configurations that differ by an
  exchange of the two spins on a nearest-neighbour bond (locality together with conservation
  of the total magnetisation);
* `hbdd`   : matrix elements are bounded by `M`.

`ψ0` is a normalised ground state (`hmin`) lying in the zero-magnetisation sector (`hsector`,
i.e. exactly half of the spins are up; this is where the half-integer value of the spin enters,
producing the momentum shift by `π` of the twisted state).

The conclusion is the LSM alternative: either the ground state is degenerate, or there is a
state orthogonal to `ψ0` whose energy lies within `2π²M/L` of the ground state energy, i.e.
the gap closes at least as fast as `O(1/L)` as the chain grows: the chain is gapless or
degenerate.

The proof is the classical Lieb-Schultz-Mattis twist argument: the twist operator
`U = exp (2πi/L ∑ j j n_j)` produces a variational state of energy `E0 + O(1/L)` (using the
average of `U` and `U*` so that the first order term cancels), and, in the half-filled sector,
`U` shifts the momentum by `π`, so `Uψ0` is orthogonal to `ψ0` whenever `ψ0` is a translation
eigenvector, which it is when the ground state is unique.
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Phys

/-! ## The spin-1/2 periodic chain -/

/-- Spin configurations of a periodic spin-`1/2` chain with `L` sites: each site carries a
two-dimensional spin space (`S = 1/2`, i.e. half-integer spin), encoded by a `Bool`. -/
abbrev Cfg (L : ℕ) := ZMod L → Bool

variable {L : ℕ} [NeZero L]

/-- The lattice translation acting on configurations. -/
def shiftCfg (σ : Cfg L) : Cfg L := fun k => σ (k + 1)

/-- Exchange of the spins on the bond `(j, j+1)`. -/
def swapCfg (j : ZMod L) (σ : Cfg L) : Cfg L :=
  fun k => if k = j then σ (j + 1) else if k = j + 1 then σ j else σ k

/-- The number of up spins in a configuration. -/
def occ (σ : Cfg L) : ℕ := ∑ k : ZMod L, (if σ k then 1 else 0)

/-- Phase of the Lieb-Schultz-Mattis twist operator `U = exp (2πi/L * ∑ j, j * n j)`
on a configuration. -/
noncomputable def twistPhase (σ : Cfg L) : ℝ :=
  (2 * Real.pi / L) * ∑ k : ZMod L, (if σ k then (k.val : ℝ) else 0)

/-- The (diagonal) Lieb-Schultz-Mattis twist operator. -/
noncomputable def twist (σ : Cfg L) : ℂ := Complex.exp ((twistPhase σ : ℂ) * Complex.I)

/-- Energy expectation value `⟪ψ, H ψ⟫`. -/
noncomputable def energy (H : Cfg L → Cfg L → ℂ) (ψ : Cfg L → ℂ) : ℝ :=
  (∑ σ : Cfg L, ∑ σ' : Cfg L, (starRingEnd ℂ) (ψ σ) * H σ σ' * ψ σ').re

/-- Squared norm of a state. -/
noncomputable def sqNorm (ψ : Cfg L → ℂ) : ℝ := ∑ σ : Cfg L, ‖ψ σ‖ ^ 2

/-- Hermitian inner product of two states. -/
noncomputable def ip (ψ φ : Cfg L → ℂ) : ℂ := ∑ σ : Cfg L, (starRingEnd ℂ) (ψ σ) * φ σ

/-! ## Basic combinatorics of the chain -/

omit [NeZero L] in
lemma shiftCfg_bijective : Function.Bijective (shiftCfg : Cfg L → Cfg L) := by
  refine ⟨fun σ τ h => ?_, fun τ => ⟨fun k => τ (k - 1), ?_⟩⟩
  · funext k
    have := congrFun h (k - 1)
    simpa [shiftCfg] using this
  · funext k; simp [shiftCfg]

lemma occ_shiftCfg (σ : Cfg L) : occ (shiftCfg σ) = occ σ :=
  Fintype.sum_equiv (Equiv.addRight (1 : ZMod L)) _ _ (fun _ => rfl)

omit [NeZero L] in
lemma one_ne_zero_zmod (hL : 2 ≤ L) : (1 : ZMod L) ≠ 0 := by
  intro h
  have := ZMod.val_cast_of_lt (a := 1) (n := L) (by omega)
  rw [Nat.cast_one] at this
  rw [h] at this
  simp at this

omit [NeZero L] in
lemma zmod_succ_ne_self (hL : 2 ≤ L) (j : ZMod L) : j + 1 ≠ j := by
  intro h
  exact one_ne_zero_zmod hL (by simpa using congrArg (fun x => x - j) h)

lemma val_sub_one (m : ZMod L) :
    (((m - 1).val : ℝ)) = (m.val : ℝ) - 1 + (L : ℝ) * (if m = 0 then 1 else 0) := by
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  by_cases hm : m = 0
  · subst hm
    have h1 : ((L - 1 : ℕ) : ZMod L) = (0 : ZMod L) - 1 := by
      push_cast [Nat.cast_sub hL]
      simp
    have h2 : ((0 : ZMod L) - 1).val = L - 1 := by
      rw [← h1, ZMod.val_cast_of_lt (by omega)]
    rw [h2]
    simp
    push_cast [Nat.cast_sub hL]
    ring
  · have hv : 1 ≤ m.val := by
      rcases Nat.eq_zero_or_pos m.val with h | h
      · exact absurd ((ZMod.val_eq_zero m).mp h) hm
      · omega
    have hlt : m.val < L := ZMod.val_lt m
    have h1 : ((m.val - 1 : ℕ) : ZMod L) = m - 1 := by
      push_cast [Nat.cast_sub hv]
      simp [ZMod.natCast_val, ZMod.cast_id]
    have h2 : (m - 1).val = m.val - 1 := by
      rw [← h1, ZMod.val_cast_of_lt (by omega)]
    rw [h2, Nat.cast_sub hv]
    simp [hm]

/-! ## The twist operator -/

lemma twistPhase_shiftCfg (σ : Cfg L) :
    twistPhase (shiftCfg σ) =
      twistPhase σ - (2 * Real.pi / L) * (occ σ : ℝ) + 2 * Real.pi * (if σ 0 then 1 else 0) := by
  have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  have step1 : (∑ k : ZMod L, (if shiftCfg σ k then (k.val : ℝ) else 0))
      = ∑ m : ZMod L, (if σ m then (((m - 1).val : ℕ) : ℝ) else 0) :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod L)) _ _ (by intro k; simp [shiftCfg])
  have step2 : (∑ m : ZMod L, (if σ m then (((m - 1).val : ℕ) : ℝ) else 0))
      = (∑ m : ZMod L, (if σ m then (m.val : ℝ) else 0))
        - (∑ m : ZMod L, (if σ m then (1:ℝ) else 0))
        + (∑ m : ZMod L, (if σ m then (L : ℝ) * (if m = 0 then 1 else 0) else 0)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro m _
    rw [val_sub_one]
    by_cases h : σ m <;> simp [h]
  have step3 : (∑ m : ZMod L, (if σ m then (1:ℝ) else 0)) = (occ σ : ℝ) := by
    simp only [occ, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have step4 : (∑ m : ZMod L, (if σ m then (L : ℝ) * (if m = 0 then 1 else 0) else 0))
      = (L : ℝ) * (if σ 0 then 1 else 0) := by
    rw [Finset.sum_eq_single (0 : ZMod L)]
    · by_cases h : σ 0 <;> simp [h]
    · intro b _ hb; by_cases h : σ b <;> simp [h, hb]
    · intro h; simp at h
  rw [twistPhase, twistPhase, step1, step2, step3, step4]
  field_simp

lemma norm_twist (σ : Cfg L) : ‖twist σ‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma twist_shiftCfg {σ : Cfg L} (h : 2 * occ σ = L) : twist (shiftCfg σ) = - twist σ := by
  have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  have hoccR : (2 : ℝ) * (occ σ : ℝ) = (L : ℝ) := by exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h
  have hocc : (2 * Real.pi / L) * (occ σ : ℝ) = Real.pi := by
    field_simp
    linarith [hoccR]
  rw [twist, twist, twistPhase_shiftCfg, hocc]
  by_cases h0 : σ 0
  · simp only [h0, if_true]
    push_cast
    rw [show ((twistPhase σ : ℂ) - Real.pi + 2 * Real.pi * 1) * Complex.I
        = (twistPhase σ : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I by ring,
      Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  · simp only [h0]
    push_cast
    rw [show ((twistPhase σ : ℂ) - Real.pi + 2 * Real.pi * 0) * Complex.I
        = (twistPhase σ : ℂ) * Complex.I + (-((Real.pi : ℂ) * Complex.I)) by ring,
      Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num

lemma twistPhase_swap (hL : 2 ≤ L) (j : ZMod L) (σ : Cfg L) :
    twistPhase (swapCfg j σ) - twistPhase σ =
      (2 * Real.pi / L) *
        (((if σ (j+1) then (j.val : ℝ) else 0) + (if σ j then (((j+1).val : ℕ) : ℝ) else 0))
          - ((if σ j then (j.val : ℝ) else 0)
              + (if σ (j+1) then (((j+1).val : ℕ) : ℝ) else 0))) := by
  have hne : j + 1 ≠ j := zmod_succ_ne_self hL j
  rw [twistPhase, twistPhase, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  have hsub : ({j, j+1} : Finset (ZMod L)) ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_subset hsub (by
    intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    have : swapCfg j σ k = σ k := by simp [swapCfg, hk.1, hk.2]
    rw [this]; ring)]
  rw [Finset.sum_pair (Ne.symm hne)]
  simp only [swapCfg, if_neg hne]
  by_cases h1 : σ j <;> by_cases h2 : σ (j+1) <;> simp [h1, h2] <;> ring

lemma val_succ_sub (j : ZMod L) :
    (((j+1).val : ℝ)) - (j.val : ℝ) = 1 - (L:ℝ) * (if j + 1 = 0 then 1 else 0) := by
  have h := val_sub_one (j + 1)
  simp only [add_sub_cancel_right] at h
  linarith

lemma cos_phase_eq (j : ZMod L) :
    Real.cos ((2*Real.pi/L) * (((j+1).val : ℝ) - (j.val:ℝ))) = Real.cos (2*Real.pi/L) := by
  have hL0 : (L:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  rw [val_succ_sub]
  by_cases h : j + 1 = 0
  · rw [if_pos h]
    have : (2*Real.pi/(L:ℝ)) * (1 - (L:ℝ)*1) = 2*Real.pi/(L:ℝ) - 2*Real.pi := by field_simp
    rw [this, Real.cos_sub_two_pi]
  · rw [if_neg h]; norm_num

lemma one_sub_cos_twist_swap_le (hL : 2 ≤ L) (j : ZMod L) (σ : Cfg L) :
    1 - Real.cos (twistPhase (swapCfg j σ) - twistPhase σ) ≤ 2 * Real.pi ^ 2 / (L : ℝ) ^ 2 := by
  have hL0 : (0:ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hbase : 1 - Real.cos (2*Real.pi/L) ≤ 2 * Real.pi ^ 2 / (L : ℝ) ^ 2 := by
    have hx : (2*Real.pi/(L:ℝ)) ≠ 0 := by positivity
    have h1 := Real.one_sub_sq_div_two_lt_cos hx
    have h2 : (2*Real.pi/(L:ℝ))^2/2 = 2 * Real.pi ^ 2 / (L : ℝ) ^ 2 := by field_simp
    linarith
  have hpos : (0:ℝ) ≤ 2 * Real.pi ^ 2 / (L : ℝ) ^ 2 := by positivity
  set A : ℝ := ((j+1).val : ℝ) - (j.val : ℝ) with hA
  have hcases :
      (((if σ (j+1) then (j.val : ℝ) else 0) + (if σ j then (((j+1).val : ℕ) : ℝ) else 0))
          - ((if σ j then (j.val : ℝ) else 0)
              + (if σ (j+1) then (((j+1).val : ℕ) : ℝ) else 0))) = 0
      ∨ (((if σ (j+1) then (j.val : ℝ) else 0) + (if σ j then (((j+1).val : ℕ) : ℝ) else 0))
          - ((if σ j then (j.val : ℝ) else 0)
              + (if σ (j+1) then (((j+1).val : ℕ) : ℝ) else 0))) = A
      ∨ (((if σ (j+1) then (j.val : ℝ) else 0) + (if σ j then (((j+1).val : ℕ) : ℝ) else 0))
          - ((if σ j then (j.val : ℝ) else 0)
              + (if σ (j+1) then (((j+1).val : ℕ) : ℝ) else 0))) = -A := by
    by_cases h1 : σ j <;> by_cases h2 : σ (j+1)
    · exact Or.inl (by simp [h1, h2])
    · exact Or.inr (Or.inl (by simp [h1, h2, hA]))
    · exact Or.inr (Or.inr (by simp [h1, h2, hA]))
    · exact Or.inl (by simp [h1, h2])
  rw [twistPhase_swap hL]
  rcases hcases with h | h | h <;> rw [h]
  · simpa using hpos
  · rw [cos_phase_eq]; exact hbase
  · rw [mul_neg, Real.cos_neg, cos_phase_eq]; exact hbase

/-! ## Invariance properties -/

lemma sqNorm_comp_shift (ψ : Cfg L → ℂ) : sqNorm (fun σ => ψ (shiftCfg σ)) = sqNorm ψ :=
  Fintype.sum_bijective shiftCfg shiftCfg_bijective _ _ (fun _ => rfl)

lemma energy_comp_shift {H : Cfg L → Cfg L → ℂ}
    (htrans : ∀ σ σ', H (shiftCfg σ) (shiftCfg σ') = H σ σ') (ψ : Cfg L → ℂ) :
    energy H (fun σ => ψ (shiftCfg σ)) = energy H ψ := by
  unfold energy
  congr 1
  have h : ∀ σ σ' : Cfg L, (starRingEnd ℂ) (ψ (shiftCfg σ)) * H σ σ' * ψ (shiftCfg σ')
      = (starRingEnd ℂ) (ψ (shiftCfg σ)) * H (shiftCfg σ) (shiftCfg σ') * ψ (shiftCfg σ') := by
    intro σ σ'; rw [htrans]
  rw [Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun σ' _ => h σ σ'))]
  refine Fintype.sum_bijective shiftCfg shiftCfg_bijective _ _ (fun σ => ?_)
  exact Fintype.sum_bijective shiftCfg shiftCfg_bijective _ _ (fun _ => rfl)

lemma sqNorm_mul_unit (ψ v : Cfg L → ℂ) (hv : ∀ σ, ‖v σ‖ = 1) :
    sqNorm (fun σ => v σ * ψ σ) = sqNorm ψ :=
  Finset.sum_congr rfl fun σ _ => by rw [norm_mul, hv, one_mul]

/-! ## Orthogonality of the twisted state (momentum shift by π) -/

lemma ip_eq_zero_of_anti (v ψ0 : Cfg L → ℂ)
    (hv : ∀ σ, 2 * occ σ = L → v (shiftCfg σ) = - v σ)
    (hsector : ∀ σ, ψ0 σ ≠ 0 → 2 * occ σ = L)
    (lam : ℂ) (hlam : ∀ σ, ψ0 (shiftCfg σ) = lam * ψ0 σ) (hlam1 : ‖lam‖ = 1) :
    ip ψ0 (fun σ => v σ * ψ0 σ) = 0 := by
  have hll : (starRingEnd ℂ) lam * lam = 1 := by
    rw [mul_comm, Complex.mul_conj', hlam1]; norm_num
  have key : ∀ σ : Cfg L,
      (starRingEnd ℂ) (ψ0 (shiftCfg σ)) * (v (shiftCfg σ) * ψ0 (shiftCfg σ))
        = -((starRingEnd ℂ) (ψ0 σ) * (v σ * ψ0 σ)) := by
    intro σ
    by_cases h : ψ0 σ = 0
    · rw [hlam σ, h]; simp
    · rw [hlam σ, hv σ (hsector σ h), map_mul]
      linear_combination (-((starRingEnd ℂ) (ψ0 σ) * v σ * ψ0 σ)) * hll
  have hsum : ip ψ0 (fun σ => v σ * ψ0 σ) = - ip ψ0 (fun σ => v σ * ψ0 σ) := by
    unfold ip
    calc ∑ σ : Cfg L, (starRingEnd ℂ) (ψ0 σ) * (v σ * ψ0 σ)
        = ∑ σ : Cfg L, (starRingEnd ℂ) (ψ0 (shiftCfg σ)) * (v (shiftCfg σ) * ψ0 (shiftCfg σ)) :=
          (Fintype.sum_bijective shiftCfg shiftCfg_bijective _ _ (fun _ => rfl)).symm
      _ = ∑ σ : Cfg L, -((starRingEnd ℂ) (ψ0 σ) * (v σ * ψ0 σ)) :=
          Finset.sum_congr rfl fun σ _ => key σ
      _ = - ∑ σ : Cfg L, (starRingEnd ℂ) (ψ0 σ) * (v σ * ψ0 σ) := by rw [Finset.sum_neg_distrib]
  linear_combination hsum / 2

/-! ## The variational energy estimate -/

lemma energy_mul (H : Cfg L → Cfg L → ℂ) (ψ v : Cfg L → ℂ) :
    energy H (fun σ => v σ * ψ σ)
      = (∑ σ : Cfg L, ∑ σ' : Cfg L,
          ((starRingEnd ℂ) (ψ σ) * H σ σ' * ψ σ') * ((starRingEnd ℂ) (v σ) * v σ')).re := by
  unfold energy
  congr 1
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun σ' _ => ?_
  simp only [map_mul]
  ring

lemma twist_pair (a b : ℝ) :
    (starRingEnd ℂ) (Complex.exp ((a:ℂ)*Complex.I)) * Complex.exp ((b:ℂ)*Complex.I)
      + Complex.exp ((a:ℂ)*Complex.I) * (starRingEnd ℂ) (Complex.exp ((b:ℂ)*Complex.I))
      = 2 * ((Real.cos (b - a) : ℝ) : ℂ) := by
  have ha : Complex.exp ((a:ℂ)*Complex.I) = (Real.cos a : ℂ) + (Real.sin a : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have hb : Complex.exp ((b:ℂ)*Complex.I) = (Real.cos b : ℂ) + (Real.sin b : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [ha, hb, Real.cos_sub]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

lemma row_card (H : Cfg L → Cfg L → ℂ)
    (hloc : ∀ σ σ', H σ σ' ≠ 0 → σ' = σ ∨ ∃ j, σ' = swapCfg j σ) (σ : Cfg L) :
    (Finset.univ.filter (fun σ' => H σ σ' ≠ 0 ∧ σ' ≠ σ)).card ≤ L := by
  have hsub : (Finset.univ.filter (fun σ' => H σ σ' ≠ 0 ∧ σ' ≠ σ))
      ⊆ Finset.image (fun j : ZMod L => swapCfg j σ) Finset.univ := by
    intro τ hτ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
    rcases hloc σ τ hτ.1 with h | ⟨j, hj⟩
    · exact absurd h hτ.2
    · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj.symm⟩
  calc (Finset.univ.filter (fun σ' => H σ σ' ≠ 0 ∧ σ' ≠ σ)).card
      ≤ (Finset.image (fun j : ZMod L => swapCfg j σ) Finset.univ).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (ZMod L)).card := Finset.card_image_le
    _ = L := by simp [ZMod.card]

lemma col_card (H : Cfg L → Cfg L → ℂ)
    (hherm : ∀ σ σ', H σ' σ = (starRingEnd ℂ) (H σ σ'))
    (hloc : ∀ σ σ', H σ σ' ≠ 0 → σ' = σ ∨ ∃ j, σ' = swapCfg j σ) (τ : Cfg L) :
    (Finset.univ.filter (fun σ => H σ τ ≠ 0 ∧ τ ≠ σ)).card ≤ L := by
  have hsub : (Finset.univ.filter (fun σ => H σ τ ≠ 0 ∧ τ ≠ σ))
      ⊆ Finset.image (fun j : ZMod L => swapCfg j τ) Finset.univ := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    have hτσ : H τ σ ≠ 0 := by
      intro h0
      exact hσ.1 (by rw [hherm τ σ, h0, map_zero])
    rcases hloc τ σ hτσ with h | ⟨j, hj⟩
    · exact absurd h.symm hσ.2
    · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj.symm⟩
  calc (Finset.univ.filter (fun σ => H σ τ ≠ 0 ∧ τ ≠ σ)).card
      ≤ (Finset.image (fun j : ZMod L => swapCfg j τ) Finset.univ).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (ZMod L)).card := Finset.card_image_le
    _ = L := by simp [ZMod.card]

lemma nbr_sum_bound (H : Cfg L → Cfg L → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hherm : ∀ σ σ', H σ' σ = (starRingEnd ℂ) (H σ σ'))
    (hloc : ∀ σ σ', H σ σ' ≠ 0 → σ' = σ ∨ ∃ j, σ' = swapCfg j σ)
    (ψ : Cfg L → ℂ) (hnorm : sqNorm ψ = 1) :
    ∑ σ : Cfg L, ∑ σ' : Cfg L, (if H σ σ' ≠ 0 ∧ σ' ≠ σ then M * (‖ψ σ‖ * ‖ψ σ'‖) else 0)
      ≤ M * L := by
  have hrow := row_card H hloc
  have hcol := col_card H hherm hloc
  have step1 : ∀ σ σ' : Cfg L,
      (if H σ σ' ≠ 0 ∧ σ' ≠ σ then M * (‖ψ σ‖ * ‖ψ σ'‖) else 0)
        ≤ (if H σ σ' ≠ 0 ∧ σ' ≠ σ then M * (‖ψ σ‖^2/2) else 0)
          + (if H σ σ' ≠ 0 ∧ σ' ≠ σ then M * (‖ψ σ'‖^2/2) else 0) := by
    intro σ σ'
    by_cases h : H σ σ' ≠ 0 ∧ σ' ≠ σ
    · simp only [if_pos h, ← mul_add]
      have : ‖ψ σ‖ * ‖ψ σ'‖ ≤ ‖ψ σ‖^2/2 + ‖ψ σ'‖^2/2 := by nlinarith [sq_nonneg (‖ψ σ‖ - ‖ψ σ'‖)]
      exact mul_le_mul_of_nonneg_left this hM
    · simp [if_neg h]
  have rowsum : ∀ σ : Cfg L,
      (∑ σ' : Cfg L, (if H σ σ' ≠ 0 ∧ σ' ≠ σ then M * (‖ψ σ‖^2/2) else 0))
        ≤ (L : ℝ) * (M * (‖ψ σ‖^2/2)) := by
    intro σ
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have h1 : ((Finset.univ.filter (fun σ' => H σ σ' ≠ 0 ∧ σ' ≠ σ)).card : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast hrow σ
    have h2 : (0:ℝ) ≤ M * (‖ψ σ‖^2/2) := by positivity
    exact mul_le_mul_of_nonneg_right h1 h2
  have colsum : ∀ τ : Cfg L,
      (∑ σ : Cfg L, (if H σ τ ≠ 0 ∧ τ ≠ σ then M * (‖ψ τ‖^2/2) else 0))
        ≤ (L : ℝ) * (M * (‖ψ τ‖^2/2)) := by
    intro τ
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have h1 : ((Finset.univ.filter (fun σ => H σ τ ≠ 0 ∧ τ ≠ σ)).card : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast hcol τ
    have h2 : (0:ℝ) ≤ M * (‖ψ τ‖^2/2) := by positivity
    exact mul_le_mul_of_nonneg_right h1 h2
  calc ∑ σ : Cfg L, ∑ σ' : Cfg L, (if H σ σ' ≠ 0 ∧ σ' ≠ σ then M * (‖ψ σ‖ * ‖ψ σ'‖) else 0)
      ≤ ∑ σ : Cfg L, ∑ σ' : Cfg L,
          ((if H σ σ' ≠ 0 ∧ σ' ≠ σ then M * (‖ψ σ‖^2/2) else 0)
            + (if H σ σ' ≠ 0 ∧ σ' ≠ σ then M * (‖ψ σ'‖^2/2) else 0)) :=
        Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun σ' _ => step1 σ σ'
    _ = (∑ σ : Cfg L, ∑ σ' : Cfg L, (if H σ σ' ≠ 0 ∧ σ' ≠ σ then M * (‖ψ σ‖^2/2) else 0))
          + (∑ σ : Cfg L, ∑ σ' : Cfg L,
              (if H σ σ' ≠ 0 ∧ σ' ≠ σ then M * (‖ψ σ'‖^2/2) else 0)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun σ _ => Finset.sum_add_distrib
    _ ≤ (∑ σ : Cfg L, (L:ℝ) * (M * (‖ψ σ‖^2/2))) + (∑ τ : Cfg L, (L:ℝ) * (M * (‖ψ τ‖^2/2))) := by
        refine add_le_add (Finset.sum_le_sum fun σ _ => rowsum σ) ?_
        rw [Finset.sum_comm]
        exact Finset.sum_le_sum fun τ _ => colsum τ
    _ = M * L := by
        simp only [← Finset.mul_sum]
        have h : ∑ i : Cfg L, ‖ψ i‖^2/2 = 1/2 := by
          rw [← Finset.sum_div, show (∑ σ : Cfg L, ‖ψ σ‖^2) = sqNorm ψ from rfl, hnorm]
        rw [h]; ring

lemma twist_energy_bound (hL : 2 ≤ L) (H : Cfg L → Cfg L → ℂ) (M : ℝ)
    (hherm : ∀ σ σ', H σ' σ = (starRingEnd ℂ) (H σ σ'))
    (hloc : ∀ σ σ', H σ σ' ≠ 0 → σ' = σ ∨ ∃ j, σ' = swapCfg j σ)
    (hbdd : ∀ σ σ', ‖H σ σ'‖ ≤ M)
    (ψ : Cfg L → ℂ) (hnorm : sqNorm ψ = 1) :
    energy H (fun σ => twist σ * ψ σ) + energy H (fun σ => (starRingEnd ℂ) (twist σ) * ψ σ)
      ≤ 2 * energy H ψ + 4 * Real.pi ^ 2 * M / L := by
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hbdd (fun _ => false) (fun _ => false))
  have hL0 : (0:ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  -- rewrite the difference of energies as a single sum
  have hcomb : ∀ (f g h : Cfg L → Cfg L → ℂ),
      (∑ σ : Cfg L, ∑ σ', f σ σ') + (∑ σ : Cfg L, ∑ σ', g σ σ') - 2 * (∑ σ : Cfg L, ∑ σ', h σ σ')
        = ∑ σ : Cfg L, ∑ σ', (f σ σ' + g σ σ' - 2 * h σ σ') := by
    intro f g h
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  have hdiff : energy H (fun σ => twist σ * ψ σ)
        + energy H (fun σ => (starRingEnd ℂ) (twist σ) * ψ σ) - 2 * energy H ψ
      = (∑ σ : Cfg L, ∑ σ' : Cfg L,
          ((starRingEnd ℂ) (ψ σ) * H σ σ' * ψ σ')
            * (2 * ((Real.cos (twistPhase σ' - twistPhase σ) : ℝ) : ℂ) - 2)).re := by
    rw [energy_mul, energy_mul, energy]
    rw [show ∀ (X Y Z : ℂ), X.re + Y.re - 2 * Z.re = (X + Y - 2*Z).re from by
      intro X Y Z; simp [Complex.add_re, Complex.sub_re]]
    congr 1
    rw [hcomb]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun σ' _ => ?_
    simp only [twist, Complex.conj_conj]
    linear_combination ((starRingEnd ℂ) (ψ σ) * H σ σ' * ψ σ')
      * twist_pair (twistPhase σ) (twistPhase σ')
  -- estimate the sum
  have hkey : ∀ σ σ' : Cfg L,
      ‖((starRingEnd ℂ) (ψ σ) * H σ σ' * ψ σ')
          * (2 * ((Real.cos (twistPhase σ' - twistPhase σ) : ℝ) : ℂ) - 2)‖
        ≤ (4*Real.pi^2/(L:ℝ)^2)
            * (if H σ σ' ≠ 0 ∧ σ' ≠ σ then M * (‖ψ σ‖ * ‖ψ σ'‖) else 0) := by
    intro σ σ'
    by_cases hH : H σ σ' = 0
    · simp [hH]
    by_cases heq : σ' = σ
    · subst heq; simp
    · rw [if_pos ⟨hH, heq⟩]
      obtain ⟨j, hj⟩ := (hloc σ σ' hH).resolve_left heq
      have hcos : 2 - 2 * Real.cos (twistPhase σ' - twistPhase σ) ≤ 4*Real.pi^2/(L:ℝ)^2 := by
        have h := one_sub_cos_twist_swap_le hL j σ
        rw [← hj] at h
        have h2 : 4*Real.pi^2/(L:ℝ)^2 = 2*(2*Real.pi^2/(L:ℝ)^2) := by ring
        rw [h2]; linarith
      have hnormc : ‖(starRingEnd ℂ) (ψ σ) * H σ σ' * ψ σ'‖ ≤ M * (‖ψ σ‖ * ‖ψ σ'‖) := by
        rw [norm_mul, norm_mul, RCLike.norm_conj]
        calc ‖ψ σ‖ * ‖H σ σ'‖ * ‖ψ σ'‖ ≤ ‖ψ σ‖ * M * ‖ψ σ'‖ := by
              gcongr
              exact hbdd σ σ'
          _ = M * (‖ψ σ‖ * ‖ψ σ'‖) := by ring
      have hfac : ‖2 * ((Real.cos (twistPhase σ' - twistPhase σ) : ℝ) : ℂ) - 2‖
          = 2 - 2 * Real.cos (twistPhase σ' - twistPhase σ) := by
        have h1 : (2 * ((Real.cos (twistPhase σ' - twistPhase σ) : ℝ) : ℂ) - 2)
            = (((2 * Real.cos (twistPhase σ' - twistPhase σ) - 2 : ℝ)) : ℂ) := by push_cast; ring
        rw [h1, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonpos (by linarith [Real.cos_le_one (twistPhase σ' - twistPhase σ)])]
        ring
      rw [norm_mul, hfac, mul_comm (4*Real.pi^2/(L:ℝ)^2)]
      exact mul_le_mul hnormc hcos
        (by linarith [Real.cos_le_one (twistPhase σ' - twistPhase σ)]) (by positivity)
  have hbound : (∑ σ : Cfg L, ∑ σ' : Cfg L,
          ((starRingEnd ℂ) (ψ σ) * H σ σ' * ψ σ')
            * (2 * ((Real.cos (twistPhase σ' - twistPhase σ) : ℝ) : ℂ) - 2)).re
      ≤ 4 * Real.pi ^ 2 * M / L := by
    calc (∑ σ : Cfg L, ∑ σ' : Cfg L,
            ((starRingEnd ℂ) (ψ σ) * H σ σ' * ψ σ')
              * (2 * ((Real.cos (twistPhase σ' - twistPhase σ) : ℝ) : ℂ) - 2)).re
        ≤ ‖∑ σ : Cfg L, ∑ σ' : Cfg L,
            ((starRingEnd ℂ) (ψ σ) * H σ σ' * ψ σ')
              * (2 * ((Real.cos (twistPhase σ' - twistPhase σ) : ℝ) : ℂ) - 2)‖ :=
          Complex.re_le_norm _
      _ ≤ ∑ σ : Cfg L, ∑ σ' : Cfg L,
            ‖((starRingEnd ℂ) (ψ σ) * H σ σ' * ψ σ')
              * (2 * ((Real.cos (twistPhase σ' - twistPhase σ) : ℝ) : ℂ) - 2)‖ :=
          le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun σ _ => norm_sum_le _ _)
      _ ≤ ∑ σ : Cfg L, ∑ σ' : Cfg L, (4*Real.pi^2/(L:ℝ)^2)
              * (if H σ σ' ≠ 0 ∧ σ' ≠ σ then M * (‖ψ σ‖ * ‖ψ σ'‖) else 0) :=
          Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun σ' _ => hkey σ σ'
      _ = (4*Real.pi^2/(L:ℝ)^2) * ∑ σ : Cfg L, ∑ σ' : Cfg L,
              (if H σ σ' ≠ 0 ∧ σ' ≠ σ then M * (‖ψ σ‖ * ‖ψ σ'‖) else 0) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun σ _ => (Finset.mul_sum _ _ _).symm
      _ ≤ (4*Real.pi^2/(L:ℝ)^2) * (M * L) :=
          mul_le_mul_of_nonneg_left (nbr_sum_bound H M hM hherm hloc ψ hnorm) (by positivity)
      _ = 4 * Real.pi ^ 2 * M / L := by field_simp
  linarith [hdiff ▸ hbound]

/-! ## Main theorem -/

/-- **Lieb-Schultz-Mattis theorem** (finite-volume form) for a periodic spin-`1/2` chain,
i.e. a translation invariant chain with half-integer spin per site.

`H` is a Hermitian, translation invariant Hamiltonian whose off-diagonal matrix elements only
connect configurations differing by an exchange on a nearest-neighbour bond (locality together
with conservation of the total magnetisation), with matrix elements bounded by `M`.  `ψ0` is a
normalised ground state lying in the zero-magnetisation sector.  Then either the ground state is
degenerate, or there is a state orthogonal to `ψ0` whose energy exceeds the ground state energy
by at most `2π²M/L` (and at least the ground state energy): the spectral gap above the ground
state closes at least as fast as `O(1/L)`.  So a half-integer-spin translation invariant chain
is gapless or degenerate. -/
theorem lieb_schultz_mattis
    {L : ℕ} [NeZero L] (H : Cfg L → Cfg L → ℂ) (M : ℝ)
    (hherm : ∀ σ σ', H σ' σ = (starRingEnd ℂ) (H σ σ'))
    (htrans : ∀ σ σ', H (shiftCfg σ) (shiftCfg σ') = H σ σ')
    (hloc : ∀ σ σ', H σ σ' ≠ 0 → σ' = σ ∨ ∃ j, σ' = swapCfg j σ)
    (hbdd : ∀ σ σ', ‖H σ σ'‖ ≤ M)
    (ψ0 : Cfg L → ℂ) (hnorm : sqNorm ψ0 = 1)
    (E0 : ℝ) (hE0 : energy H ψ0 = E0)
    (hmin : ∀ ψ : Cfg L → ℂ, sqNorm ψ = 1 → E0 ≤ energy H ψ)
    (hsector : ∀ σ, ψ0 σ ≠ 0 → 2 * occ σ = L) :
    (∃ φ : Cfg L → ℂ, sqNorm φ = 1 ∧ energy H φ = E0 ∧ ∀ c : ℂ, φ ≠ c • ψ0) ∨
    (∃ φ : Cfg L → ℂ, sqNorm φ = 1 ∧ ip ψ0 φ = 0 ∧
        E0 ≤ energy H φ ∧ energy H φ ≤ E0 + 2 * Real.pi ^ 2 * M / (L : ℝ)) := by
  by_cases hdeg : ∃ φ : Cfg L → ℂ, sqNorm φ = 1 ∧ energy H φ = E0 ∧ ∀ c : ℂ, φ ≠ c • ψ0
  · exact Or.inl hdeg
  right
  push_neg at hdeg
  -- the chain has at least two sites
  have hex : ∃ σ : Cfg L, ψ0 σ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h0 : sqNorm ψ0 = 0 := by simp [sqNorm, hcon]
    rw [hnorm] at h0
    norm_num at h0
  obtain ⟨σ0, hσ0⟩ := hex
  have hoccL := hsector σ0 hσ0
  have hL : 2 ≤ L := by
    rcases Nat.eq_zero_or_pos (occ σ0) with h | h
    · rw [h] at hoccL
      exact absurd hoccL.symm (NeZero.ne L)
    · omega
  -- the ground state is a translation eigenvector
  have hTnorm : sqNorm (fun σ => ψ0 (shiftCfg σ)) = 1 := by rw [sqNorm_comp_shift, hnorm]
  have hTen : energy H (fun σ => ψ0 (shiftCfg σ)) = E0 := by rw [energy_comp_shift htrans, hE0]
  obtain ⟨lam, hlamfun⟩ := hdeg _ hTnorm hTen
  have hlam : ∀ σ, ψ0 (shiftCfg σ) = lam * ψ0 σ := fun σ => by
    simpa using congrFun hlamfun σ
  have hlam1 : ‖lam‖ = 1 := by
    have h : sqNorm (fun σ => ψ0 (shiftCfg σ)) = ‖lam‖^2 * sqNorm ψ0 := by
      simp only [sqNorm, Finset.mul_sum]
      exact Finset.sum_congr rfl fun σ _ => by rw [hlam σ, norm_mul, mul_pow]
    rw [hTnorm, hnorm, mul_one] at h
    nlinarith [norm_nonneg lam]
  -- the two twisted states are orthogonal to the ground state and have low energy
  have horth1 : ip ψ0 (fun σ => twist σ * ψ0 σ) = 0 :=
    ip_eq_zero_of_anti twist ψ0 (fun _ h => twist_shiftCfg h) hsector lam hlam hlam1
  have horth2 : ip ψ0 (fun σ => (starRingEnd ℂ) (twist σ) * ψ0 σ) = 0 :=
    ip_eq_zero_of_anti _ ψ0 (fun _ h => by rw [twist_shiftCfg h, map_neg]) hsector lam hlam hlam1
  have hn1 : sqNorm (fun σ => twist σ * ψ0 σ) = 1 := by
    rw [sqNorm_mul_unit _ _ norm_twist, hnorm]
  have hn2 : sqNorm (fun σ => (starRingEnd ℂ) (twist σ) * ψ0 σ) = 1 := by
    rw [sqNorm_mul_unit _ _ (fun σ => by rw [RCLike.norm_conj]; exact norm_twist σ), hnorm]
  have hEsum := twist_energy_bound hL H M hherm hloc hbdd ψ0 hnorm
  rw [hE0] at hEsum
  rcases le_total (energy H (fun σ => twist σ * ψ0 σ))
      (energy H (fun σ => (starRingEnd ℂ) (twist σ) * ψ0 σ)) with h | h
  · refine ⟨_, hn1, horth1, hmin _ hn1, ?_⟩
    calc energy H (fun σ => twist σ * ψ0 σ)
        ≤ (2 * E0 + 4 * Real.pi ^ 2 * M / (L:ℝ)) / 2 := by linarith
      _ = E0 + 2 * Real.pi ^ 2 * M / (L:ℝ) := by ring
  · refine ⟨_, hn2, horth2, hmin _ hn2, ?_⟩
    calc energy H (fun σ => (starRingEnd ℂ) (twist σ) * ψ0 σ)
        ≤ (2 * E0 + 4 * Real.pi ^ 2 * M / (L:ℝ)) / 2 := by linarith
      _ = E0 + 2 * Real.pi ^ 2 * M / (L:ℝ) := by ring

/-- Sanity check: the hypotheses of `lieb_schultz_mattis` are simultaneously satisfiable, so the
theorem is not vacuous.  (Witness: the two-site chain with vanishing Hamiltonian and a
half-filled basis state as ground state.) -/
theorem lsm_hypotheses_satisfiable :
    ∃ (H : Cfg 2 → Cfg 2 → ℂ) (M : ℝ) (ψ0 : Cfg 2 → ℂ) (E0 : ℝ),
      (∀ σ σ', H σ' σ = (starRingEnd ℂ) (H σ σ')) ∧
      (∀ σ σ', H (shiftCfg σ) (shiftCfg σ') = H σ σ') ∧
      (∀ σ σ', H σ σ' ≠ 0 → σ' = σ ∨ ∃ j, σ' = swapCfg j σ) ∧
      (∀ σ σ', ‖H σ σ'‖ ≤ M) ∧ sqNorm ψ0 = 1 ∧ energy H ψ0 = E0 ∧
      (∀ ψ : Cfg 2 → ℂ, sqNorm ψ = 1 → E0 ≤ energy H ψ) ∧
      (∀ σ, ψ0 σ ≠ 0 → 2 * occ σ = 2) := by
  refine ⟨fun _ _ => 0, 0, fun σ => if σ = (fun k => decide (k = 0)) then 1 else 0, 0,
    by simp, by simp, by simp, by simp, ?_, by simp [energy], by simp [energy], ?_⟩
  · simp [sqNorm, apply_ite (fun z : ℂ => ‖z‖^2), Finset.sum_ite_eq']
  · intro σ hσ
    have h : σ = (fun k => decide (k = 0)) := by
      by_contra h
      simp [h] at hσ
    subst h
    decide

end Phys

