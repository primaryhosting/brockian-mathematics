import RequestProject.Main

/-!
# A consistency witness for `CS.LadnerSetup`

`CS.ladner` is stated relative to the abstract axiomatisation `CS.LadnerSetup`.
To rule out the possibility that this package of hypotheses is contradictory
(in which case the theorem would be vacuous), we build an explicit model of it.

The model takes both classes to be the class `FC` of languages that are *finite
variations of a constant language* (equivalently: finite or cofinite sets), which
is enumerable, closed under finite variation, contains the finite languages and is
closed downwards under the reductions of the model; `SAT` is taken to be the
cofinite language `{x | x ≠ 0}`, which is complete for `FC` under those
reductions, and the clock is taken to be constant (so all four clock-semantics
fields hold trivially or vacuously).

Of course `P = NP` holds in this model, so `CS.ladner` says nothing about it; the
point of the construction is only that the hypotheses of `CS.LadnerSetup` are
jointly satisfiable, hence consistent.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CS

namespace FinCofinModel

attribute [local instance] Classical.propDecidable

/-! ### Binary digits -/

/-- `bit n x` says that the `x`-th binary digit of `n` is `1`. -/

theorem ladnerLang_NPIntermediate (hPNP : S.P ≠ S.NP) :
    S.NPIntermediate S.ladnerLang :=
  ⟨S.ladnerLang_mem_NP, S.ladnerLang_not_mem_P hPNP, S.ladnerLang_not_NPHard hPNP⟩

end LadnerSetup

/--
**Ladner's theorem.**  If `P ≠ NP`, then `NP`-intermediate problems exist: there is
a language `L` in `NP` which is neither in `P` nor `NP`-hard (in particular, `L` is
not `NP`-complete).

The statement is relative to an abstract `LadnerSetup`, which packages the
complexity-theoretic data (the classes `P` and `NP`, an `NP`-complete language
`SAT`, an enumeration of `P`, an enumeration of the polynomial-time reductions and
Ladner's clocked stage function) together with standard closure properties.
The language exhibited is Ladner's `SAT ∩ {x | f x` is even `}`.
-/
