/-
# Hilbert 10 Undecidable
Category: Frontier Cs
Target: CS.hilbert10_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.Hilbert10.Basic
import RequestProject.Hilbert10.MRDP

/-!
# Hilbert 10 Undecidable
Category: Frontier Cs
Target: CS.hilbert10_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Overview

The development is organised as follows.

* `RequestProject.Hilbert10.Basic`: the halting set is r.e. but not computable, normalisation of
  Diophantine sets, and the passage from Mathlib's `Poly` to `MvPolynomial`.
* `RequestProject.Hilbert10.DiophTools`: pairing, unpairing and Gödel's `β` function are
  Diophantine.
* `RequestProject.Hilbert10.Choose`, `.Product`: binomial coefficients, factorials and products
  of arithmetic progressions are Diophantine.
* `RequestProject.Hilbert10.DPRTools`, `.DPRCore`, `.BddForall`: the Davis–Putnam–Robinson
  theorem, i.e. Diophantine relations are closed under bounded universal quantification.
* `RequestProject.Hilbert10.Primrec`: primitive recursive functions have Diophantine graphs.
* `RequestProject.Hilbert10.MRDP`: the MRDP theorem, every r.e. set of naturals is Diophantine.

This file combines these into the undecidability of Hilbert's tenth problem, over `ℕ`
(`CS.hilbert10_undecidable`) and over `ℤ` (`CS.hilbert10_undecidable_int`).
-/

namespace CS

/-- The reduction of Hilbert's tenth problem to the MRDP theorem: if every r.e. set of naturals
is Diophantine, then no algorithm decides solvability of a suitable Diophantine equation with a
natural number parameter.  (This implication is proved unconditionally; the MRDP hypothesis is
supplied by `CS.dioph_of_rePred`.) -/

theorem prec_graph {f g : ℕ → ℕ} (z n w : ℕ) :
    (Nat.rec (motive := fun _ => ℕ) (f z) (fun y IH => g (Nat.pair z (Nat.pair y IH))) n) = w ↔
      ∃ c, Nat.beta c 0 = f z ∧
        (∀ i < n, Nat.beta c (i + 1) = g (Nat.pair z (Nat.pair i (Nat.beta c i)))) ∧
        Nat.beta c n = w := by
  let H : ℕ → ℕ := fun n => Nat.rec (motive := fun _ => ℕ) (f z)
    (fun y IH => g (Nat.pair z (Nat.pair y IH))) n
  have hH0 : H 0 = f z := rfl
  have hHs : ∀ y, H (y + 1) = g (Nat.pair z (Nat.pair y (H y))) := fun _ => rfl
  show H n = w ↔ _
  constructor
  · rintro rfl
    let l : List ℕ := (List.range (n + 1)).map H
    have hget : ∀ i : ℕ, i < n + 1 → Nat.beta (Nat.unbeta l) i = H i := by
      intro i hi
      have := Nat.beta_unbeta_coe l ⟨i, by simp [l]; omega⟩
      simpa [l] using this
    refine ⟨Nat.unbeta l, ?_, ?_, ?_⟩
    · rw [hget 0 (by omega), hH0]
    · intro i hi
      rw [hget (i + 1) (by omega), hget i (by omega), hHs i]
    · rw [hget n (by omega)]
  · rintro ⟨c, h0, hstep, hend⟩
    have key : ∀ i ≤ n, Nat.beta c i = H i := by
      intro i
      induction i with
      | zero => intro _; rw [h0, hH0]
      | succ j ih =>
        intro hj
        rw [hstep j (by omega), ih (by omega), hHs j]
    rw [← key n le_rfl, hend]

/-- Every primitive recursive function has a Diophantine graph. -/
