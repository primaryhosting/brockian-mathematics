import Mathlib
/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

This file sets up a self-contained, fully formal framework for probabilistically checkable
proofs, in the non-uniform (Boolean circuit) model of computation, and states the PCP theorem
`NP = PCP(log n, O(1))` in it (`CS.PCPCharacterization`).

* `CS.Circuit` is the type of Boolean circuits, with `Circuit.eval` and `Circuit.size`.
* `CS.NPVerifier` is a polynomial-size circuit family verifying polynomially long witnesses,
  and `CS.InNP` / `CS.NPClass` is the resulting class `NP` (non-uniform, i.e. `NP/poly`).
* `CS.PCPVerifier r q` is a verifier that, on inputs of length `n`, tosses `r n` coins, computes
  the positions of `q n` (non-adaptive) queries into a proof `pi : ℕ → Bool` by polynomial-size
  circuits, and decides by a polynomial-size circuit.  `CS.PCPVerifier.Decides` requires perfect
  completeness and soundness error at most `1/2`.
* `CS.InPCPLogConst` / `CS.PCPLogConstClass` is `PCP(log n, O(1))`.

The main results proved here are:

* `CS.pcp_subset_np`: any language with a PCP verifier using polynomially many random strings
  and polynomially many queries is in `NP`.  In particular `PCP(log n, O(1)) ⊆ NP`
  (`CS.pcp_log_const_subset_np`).
* `CS.np_subset_pcp` and `CS.np_iff_pcp_poly`: conversely every `NP` language has a PCP verifier
  reading the whole (polynomially long) proof, so `NP = PCP(log n, poly n)`.
* `CS.pcp_theorem`: the PCP characterization `NP = PCP(log n, O(1))` holds if and only if the
  inclusion `NP ⊆ PCP(log n, O(1))` holds; the reverse inclusion is unconditional.

The hard inclusion `NP ⊆ PCP(log n, O(1))` (Arora–Safra, Arora–Lund–Motwani–Sudan–Szegedy) is
*not* formalized here; only the statement and the unconditional half of the equality are.
-/

set_option maxHeartbeats 1000000

namespace CS

/-! ## Polynomially bounded functions -/

/-- A function `f : ℕ → ℕ` is polynomially bounded. -/

theorem pcp_subset_np {L : Language} {r q : ℕ → ℕ}
    (hr : PolyBounded fun n => 2 ^ r n) (hq : PolyBounded q) (h : InPCP L r q) : InNP L := by
  classical
  obtain ⟨V, hV⟩ := h
  obtain ⟨cp, kp, hpos⟩ := V.pos_size_poly
  have hSp : PolyBounded fun n => cp * (n + 1) ^ kp := ⟨cp, kp, fun _ => le_rfl⟩
  refine ⟨⟨fun n => 2 ^ r n * q n, fun n => npC (V.pos n) (V.dec n), hr.mul hq, ?_⟩, ?_⟩
  · refine PolyBounded.mono (g := fun n => 1 + (2 ^ r n + 2 ^ r n * q n * (2 ^ r n * q n)) *
      ((V.dec n).size + V.posLen n * (4 * (cp * (n + 1) ^ kp) + 6) + 13)) ?_ ?_
    · exact (polyBounded_const 1).add ((hr.add ((hr.mul hq).mul (hr.mul hq))).mul
        ((V.dec_size_poly.add (V.posLen_poly.mul
          (((polyBounded_const 4).mul hSp).add (polyBounded_const 6)))).add (polyBounded_const 13)))
    · intro n
      exact size_npC_le (V.pos n) (V.dec n) (cp * (n + 1) ^ kp) fun i j => hpos n i j
  · intro n x
    dsimp only
    set e := randEq (r n) with he
    constructor
    · intro hx
      obtain ⟨pi, hpi⟩ := (hV n x).1 hx
      refine ⟨fun t => pi (V.query n x (e.symm (kOf t)) (iOf t)), ?_⟩
      rw [eval_npC]
      refine ⟨fun k => ?_, fun t t' hj => ?_⟩
      · have hk := hpi (e.symm k)
        rw [PCPVerifier.accepts] at hk
        simpa using hk
      · have hquery : V.query n x (e.symm (kOf t)) (iOf t)
            = V.query n x (e.symm (kOf t')) (iOf t') := by
          unfold PCPVerifier.query
          exact congrArg bitsToNat (funext hj)
        simp only [hquery]
    · rintro ⟨w, hw⟩
      rw [eval_npC] at hw
      obtain ⟨hacc, hcons⟩ := hw
      by_contra hx
      set pi : ℕ → Bool := fun p =>
        if h : ∃ t : Fin (2 ^ r n * q n), V.query n x (e.symm (kOf t)) (iOf t) = p
        then w h.choose else false with hpidef
      have hpiw : ∀ t, pi (V.query n x (e.symm (kOf t)) (iOf t)) = w t := by
        intro t
        have hex : ∃ t' : Fin (2 ^ r n * q n),
            V.query n x (e.symm (kOf t')) (iOf t') = V.query n x (e.symm (kOf t)) (iOf t) :=
          ⟨t, rfl⟩
        rw [hpidef]
        simp only [dif_pos hex]
        have hspec := hex.choose_spec
        have hbits : (fun j => (V.pos n (iOf hex.choose) j).eval
              (Fin.append x (e.symm (kOf hex.choose))))
            = fun j => (V.pos n (iOf t) j).eval (Fin.append x (e.symm (kOf t))) :=
          bitsToNat_injective hspec
        exact hcons _ _ fun j => congrFun hbits j
      have hall : ∀ rho : Bits (r n), V.accepts n x rho pi = true := by
        intro rho
        have h2 : ∀ i, pi (V.query n x rho i) = w (wIdx (e rho) i) := by
          intro i
          have := hpiw (wIdx (e rho) i)
          simpa [e.symm_apply_apply] using this
        rw [PCPVerifier.accepts]
        simpa [h2, ← he, e.symm_apply_apply] using hacc (e rho)
      have hcard := (hV n x).2 hx pi
      rw [Finset.filter_true_of_mem fun rho _ => hall rho] at hcard
      have hcard' : (Finset.univ : Finset (Bits (r n))).card = 2 ^ r n := by simp
      rw [hcard'] at hcard
      have : 0 < 2 ^ r n := Nat.two_pow_pos _
      omega

end CS

/-! ## NP ⊆ PCP(0, poly) -/

namespace CS

/-- Reindexing an NP circuit as a PCP decision circuit with an empty random string. -/
