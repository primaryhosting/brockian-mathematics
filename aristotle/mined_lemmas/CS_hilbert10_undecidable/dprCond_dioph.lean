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

private theorem dprCond_dioph (p : Poly (Fin2 (n + 1) ⊕ Fin m)) (C D : ℕ)
    {b : Vector3 ℕ n → ℕ} (db : DiophFn b) :
    Dioph {w : Idx n m → ℕ | dprCond p C D b (w none) (w (some none)) (w (some (some none)))
      (fun a => w (vIdx a)) (fun j => w (xIdx j))} := by
  have dc : DiophFn fun w : Idx n m → ℕ => w none := proj_dioph _
  have dY : DiophFn fun w : Idx n m → ℕ => w (some none) := proj_dioph _
  have dK : DiophFn fun w : Idx n m → ℕ => w (some (some none)) := proj_dioph _
  have dN : DiophFn fun w : Idx n m → ℕ => b (fun a => w (vIdx a)) :=
    reindex_diophFn (fun a : Fin2 n => (vIdx a : Idx n m)) db
  have dS : DiophFn fun w : Idx n m → ℕ => ∑ a : Fin2 n, w (vIdx a) :=
    finsum_dioph fun a _ => proj_dioph (vIdx a)
  have dd : DiophFn fun w : Idx n m → ℕ => Nat.factorial (w none) := factorial_dioph dc
  have dM : DiophFn fun w : Idx n m → ℕ =>
      prodLin 1 (Nat.factorial (w none)) (b fun a => w (vIdx a)) :=
    prodLin_dioph (const_dioph 1) dd dN
  have c1 : Dioph fun w : Idx n m → ℕ =>
      C * (b (fun a => w (vIdx a)) + w (some none) + (∑ a : Fin2 n, w (vIdx a)) + 1) ^ D
        + (b (fun a => w (vIdx a)) + w (some none) + (∑ a : Fin2 n, w (vIdx a))) < w none :=
    ((const_dioph C) D* (pow_dioph ((dN D+ dY D+ dS) D+ (D.1)) (const_dioph D))
      D+ (dN D+ dY D+ dS)) D< dc
  have c2 : Dioph fun w : Idx n m → ℕ =>
      prodLin 1 (Nat.factorial (w none)) (b fun a => w (vIdx a)) ∣
        Nat.factorial (w none) * (w (some (some none)) + 1) + 1 :=
    dvd_dioph dM ((dd D* (dK D+ (D.1))) D+ (D.1))
  have c3 : Dioph fun w : Idx n m → ℕ => ∀ j : Fin m,
      w (some none) < w (xIdx j) ∧
      prodLin 1 (Nat.factorial (w none)) (b fun a => w (vIdx a)) ∣
        Nat.factorial (w (some none) + 1) * Nat.choose (w (xIdx j)) (w (some none) + 1) := by
    refine dioph_forall_fin (S := fun j => {w : Idx n m → ℕ |
      w (some none) < w (xIdx j) ∧
      prodLin 1 (Nat.factorial (w none)) (b fun a => w (vIdx a)) ∣
        Nat.factorial (w (some none) + 1) * Nat.choose (w (xIdx j)) (w (some none) + 1)})
      fun j => ?_
    exact (dY D< (proj_dioph (xIdx j))) D∧
      dvd_dioph dM ((factorial_dioph (dY D+ (D.1))) D*
        (choose_dioph (proj_dioph (xIdx j)) (dY D+ (D.1))))
  have c4 : Dioph fun w : Idx n m → ℕ =>
      prodLin 1 (Nat.factorial (w none)) (b fun a => w (vIdx a)) ∣
        (p (Sum.elim (Vector3.cons (w (some (some none))) (fun a => w (vIdx a)))
          (fun j => w (xIdx j)))).natAbs := by
    have h := dvd_dioph dM (abs_poly_dioph (p.map (argIdx n m)))
    refine h.ext fun w => ?_
    have heq : (fun x => w (argIdx n m x)) =
        Sum.elim (Vector3.cons (w (some (some none))) (fun a => w (vIdx a)))
          (fun j => w (xIdx j)) := by
      funext x
      rcases x with z | j
      · cases z with
        | fz => rfl
        | fs a => rfl
      · rfl
    show (prodLin 1 (Nat.factorial (w none)) (b fun a => w (vIdx a)) ∣
        (p fun x => w (argIdx n m x)).natAbs) ↔ _
    rw [heq]
    exact Iff.rfl
  exact c1 D∧ c2 D∧ c3 D∧ c4

end

/-- **Davis–Putnam–Robinson**: Diophantine relations are closed under bounded universal
quantification. -/
