/-
# Brockian.Characters5 — ℤ/5 characters and discrete Fourier analysis (draft definitions)

The rigorous bridge between the five-ray wheel (naturals sorted by `n % 5`) and
Dirichlet characters mod 5. This file contains DEFINITIONS ONLY (no `sorry`,
no theorems); the accompanying frontier queue
`aristotle/core_consolidation/frontier_characters_draft.json` states the
theorems as fleet-ready formalization targets.

The endgame this library serves: the Brockian zeta twist has zero mean over
each period-5 block — `∑_{k=0}^{4} e^{2πik/5} = 0` — which is exactly what
kills the pole of the twisted Dirichlet series at `s = 1` (Dirichlet-test seed:
bounded partial sums, target `twistPartialSum_norm_le`).

## Mathlib API this file deliberately builds on (lean-4.32.0 Mathlib)

* `AddChar (ZMod 5) ℂ` and the standard character `ZMod.stdAddChar`
  (`Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar`):
  `ZMod.stdAddChar j = exp (2 * π * I * j.val / 5)` via `ZMod.stdAddChar_apply`
  + `ZMod.toCircle_apply`; primitivity is `ZMod.isPrimitive_stdAddChar`.
  Our bespoke `e` below (requested explicit form `ω ^ k.val`) is EQUAL to
  `ZMod.stdAddChar` — that bridge is queue target `e_eq_stdAddChar`, after
  which the whole `AddChar` API (`AddChar.sum_eq_zero_of_ne_one`,
  `AddChar.sum_mulShift`) applies.
* Roots of unity: `Complex.isPrimitiveRoot_exp 5 (by norm_num) :
  IsPrimitiveRoot (exp (2 * π * I / 5)) 5` and
  `IsPrimitiveRoot.geom_sum_eq_zero` (`Mathlib.RingTheory.RootsOfUnity.*`).
* DFT: Mathlib already has `ZMod.dft` (notation `𝓕`,
  `Mathlib.Analysis.Fourier.ZMod`), defined with the CONJUGATE convention
  `𝓕 Φ k = ∑ j, stdAddChar (-(j * k)) • Φ j` and inversion `ZMod.dft_dft`.
  We keep the requested positive-sign convention
  `dft f a = ∑ x, e (a * x) * f x`; note `dft f = 𝓕 f ∘ Neg.neg` once
  `e_eq_stdAddChar` is proved (a good lemma to mine but not required by the
  queue).
* Multiplicative side: `DirichletCharacter ℂ 5` is definitionally
  `MulChar (ZMod 5) ℂ`; orthogonality is `MulChar.sum_eq_zero_of_ne_one`
  (`Mathlib.NumberTheory.MulChar.Basic`). We add NO bespoke multiplicative
  characters — Mathlib's are used as-is.
-/
import Mathlib

namespace Brockian.Characters5

open Complex Finset

noncomputable section

/-- The primitive 5th root of unity `ω = e^{2πi/5}`.
Mathlib knows this is a primitive 5th root:
`Complex.isPrimitiveRoot_exp 5 (by norm_num)` (up to the cast `(5 : ℂ) = ((5 : ℕ) : ℂ)`). -/
def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `e : ZMod 5 → ℂ`, `e k = ω ^ k.val`.
This is (pointwise) Mathlib's `ZMod.stdAddChar : AddChar (ZMod 5) ℂ`;
queue target `e_eq_stdAddChar` establishes the bridge, after which
`AddChar.sum_eq_zero_of_ne_one` / `AddChar.sum_mulShift` become available. -/
def e : ZMod 5 → ℂ := fun k => ω ^ k.val

/-- Mathlib's standard additive character mod 5, `j ↦ exp (2πi·j/5)` —
the bundled `AddChar` we bridge `e` to (no bespoke bundling needed). -/
abbrev stdChar : AddChar (ZMod 5) ℂ := ZMod.stdAddChar (N := 5)

/-- Ray indicator: `rayIndicator r n = 1` if the natural `n` lies on ray `r`
of the five-ray wheel (i.e. `n ≡ r [MOD 5]`), else `0`. Valued in `ℂ` so it
can be expanded as a character sum (queue target `rayIndicator_eq_charSum`). -/
def rayIndicator (r : ZMod 5) (n : ℕ) : ℂ := if (n : ZMod 5) = r then 1 else 0

/-- Discrete Fourier transform on `ZMod 5` with the positive-sign convention
`dft f a = ∑_x e(a·x) f(x)`. Mathlib's `ZMod.dft` (`𝓕`) uses the conjugate
convention `∑ j, stdAddChar (-(j * k)) • Φ j`; the two agree after `a ↦ -a`. -/
def dft (f : ZMod 5 → ℂ) : ZMod 5 → ℂ := fun a => ∑ x : ZMod 5, e (a * x) * f x

/-- Number of elements of a finite set of naturals lying on ray `r` of the
five-ray wheel. -/
def raySum (S : Finset ℕ) (r : ZMod 5) : ℕ :=
  (S.filter fun n => (n : ZMod 5) = r).card

/-- Partial sums of the zero-mean Brockian zeta twist: `∑_{n < N} e(n mod 5)`.
Bounded partial sums (queue target `twistPartialSum_norm_le`, bound `2`) are
the Dirichlet-test seed for convergence of `ζ_B(s) = ∑ e(n mod 5) / n^s`
beyond `Re s > 1` — the twist that kills the pole at `s = 1`. -/
def twistPartialSum (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, e ((n : ZMod 5))

/-- Dirichlet characters mod 5 with complex values — Mathlib's
`DirichletCharacter ℂ 5` (definitionally `MulChar (ZMod 5) ℂ`), reused as-is;
orthogonality comes from `MulChar.sum_eq_zero_of_ne_one`. -/
abbrev DChar := DirichletCharacter ℂ 5

end

end Brockian.Characters5
