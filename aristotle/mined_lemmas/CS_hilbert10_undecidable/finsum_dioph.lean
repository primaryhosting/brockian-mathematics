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

theorem finsum_dioph {α ι : Type} {s : Finset ι} {f : ι → (α → ℕ) → ℕ}
    (hf : ∀ i ∈ s, DiophFn (f i)) : DiophFn fun v => ∑ i ∈ s, f i v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const_dioph (α := α) 0
  | insert a s ha ih =>
    have h1 : DiophFn (f a) := hf a (by simp)
    have h2 : DiophFn fun v => ∑ i ∈ s, f i v := ih fun i hi => hf i (by simp [hi])
    simpa [Finset.sum_insert ha] using h1 D+ h2

end CS

import RequestProject.Hilbert10.Choose

/-!
# Products of arithmetic progressions are Diophantine

Following Davis, the product `∏_{k=1}^{N} (a + b k)` is Diophantine: modulo a suitable modulus
`M` it equals `b ^ N * N ! * (q + N).choose N`, where `q` is an inverse-type solution of
`b q ≡ a [MOD M]`, and the product itself is smaller than `M`.

This is the ingredient that allows the modulus `∏_{k=1}^{N} (1 + k d)` of the Chinese remainder
coding used in the Davis–Putnam–Robinson theorem to be described Diophantinely.
-/

namespace CS

open Finset

/-- The product of an arithmetic progression, `∏_{k=1}^{N} (a + b k)`. -/
