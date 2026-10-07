/-
  QuasiRH003/Import003.lean — instantiation of the Brockian θ-transfer at θ = 7/8 from the
  external result openai/math family 003 ("The quasi-Riemann hypothesis").

  REGISTER INTENT: CONDITIONAL until Mode B (below) kernel-checks; then PROVED ⟨ext: 003⟩.
  This file is NOT in the `Brockian` lean_lib and is NOT built by CI or the full-corpus
  audit, because it imports the `OAI` library of openai/math.  It must be built inside a
  checkout of that project.  Nothing here is an `axiom`: the external theorems are imported
  by name and used as ordinary hypotheses of `Brockian.QuasiRHTransfer.*`, so `#print axioms`
  on every declaration below is expected to stay at {propext, Classical.choice, Quot.sound}.

  EXTERNAL INPUT (exact provenance):
    repository : https://github.com/openai/math
    commit     : adc7f1241b42e322a6451854ab7e4b4c146bf78a  (2026-10-06, "Initial commit")
    module     : OAI.NumberTheory.DirichletL.Nonvanishing
    theorems   : OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re
                 OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
    challenge  : lean/ComparatorChallenges/QuasiRiemannHypothesis.lean
                 lean/ComparatorChallenges/DirichletSevenEighths.lean
    toolchain  : leanprover/lean4:v4.34.1 ; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612
    audit      : writeups/openai-math-003-quasi-rh-audit.md
    closure    : provenance/external-inputs/openai-math-003/

  TOOLCHAIN NOTE: openai/math is on lean-4.34.1; this corpus is on lean-4.32.0.  The only
  local dependency, `Brockian.QuasiRHTransfer`, uses API whose names and signatures were
  checked identical at both Mathlib pins (see the audit §5), so the same source builds in
  both environments.

  MODE B (build):
    git clone https://github.com/openai/math.git && cd math
    git checkout adc7f1241b42e322a6451854ab7e4b4c146bf78a && cd lean
    mkdir -p Brockian && cp <this repo>/Brockian/QuasiRHTransfer.lean Brockian/
    cp <this repo>/formal/QuasiRH003/Import003.lean Brockian/QuasiRH003Import.lean
    # lakefile.lean: add   lean_lib Brockian where globs := #[`Brockian.+]
    lake update && lake exe cache get
    lake build OAI.NumberTheory.DirichletL.Nonvanishing      # ~2,924 modules; hours
    lake build Brockian.QuasiRH003Import
    # then  #print axioms Brockian.QuasiRH003.zetaB_ne_zero_of_seven_eighths_lt_re  etc.

  VERIFICATION STATUS (2026-10-07): drafted; NOT yet compiled anywhere.
-/
import OAI.NumberTheory.DirichletL.Nonvanishing
import Brockian.QuasiRHTransfer

open Complex Brockian.QuasiRHTransfer

noncomputable section

namespace Brockian.QuasiRH003

/-! ### The 7/8 half-plane for `ζ_B` -/

/-- **External corollary.**  `ζ_B(s) ≠ 0` for `Re s > 7/8`.
Zero-free bound: openai/math 003.  Transfer: `zetaB_ne_zero_of_zeroFree`. -/
theorem zetaB_ne_zero_of_seven_eighths_lt_re {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) :
    zetaB s ≠ 0 :=
  zetaB_ne_zero_of_zeroFree (7 / 8) (by norm_num)
    (fun _ hs' => OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re hs') hs

/-- The same fact reached through the *Dirichlet* theorem (principal character mod 5)
instead of the `ζ` theorem, via `zetaB_eq_LFunctionTrivChar`.  Two independent routes
from the same external source to one Brockian statement. -/
theorem zetaB_ne_zero_of_seven_eighths_lt_re' {s : ℂ} (hs : (7 / 8 : ℝ) < s.re)
    (hs1 : s ≠ 1) : zetaB s ≠ 0 := by
  rw [zetaB_eq_LFunctionTrivChar hs1]
  exact OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
    (1 : DirichletCharacter ℂ 5) hs (fun h => hs1 h.2)

/-! ### The four Dirichlet L-functions mod 5 -/

/-- All four `L(s, χ)`, `χ mod 5`, are zero-free on `Re s > 7/8` (pole excluded).  This is
the input the prime-ray estimates `ψ(x; 5, a) = x/4 + O(x^{7/8+ε})` would consume. -/
theorem LFunction_mod5_ne_zero_of_seven_eighths_lt_re (χ : DirichletCharacter ℂ 5) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re χ hs hpole

/-- For a non-principal character mod 5 the pole hypothesis is vacuous. -/
theorem LFunction_mod5_ne_zero_of_seven_eighths_lt_re_of_ne_one {χ : DirichletCharacter ℂ 5}
    (hχ : χ ≠ 1) {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  LFunction_mod5_ne_zero_of_seven_eighths_lt_re χ hs (fun h => hχ h.1)

/-! ### The zero strip `1/8 ≤ Re ρ ≤ 7/8` -/

/-- **The strip theorem for `ζ_B`.**  Every zero of `ζ_B` in the critical strip satisfies
`1/8 ≤ Re ρ ≤ 7/8`.  RH would be `Re ρ = 1/2`. -/
theorem zetaB_zero_strip {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hρ : zetaB ρ = 0) :
    (1 / 8 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 7 / 8 := by
  have h := zetaB_zero_strip_of_zeroFree (7 / 8)
    (fun _ hs' => OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re hs') h0 h1 hρ
  constructor
  · linarith [h.1]
  · exact h.2

/-- The same strip for `ζ` itself, for the theorem map. -/
theorem riemannZeta_zero_strip {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hρ : riemannZeta ρ = 0) : (1 / 8 : ℝ) ≤ ρ.re ∧ ρ.re ≤ 7 / 8 :=
  zetaB_zero_strip h0 h1 ((zetaB_eq_zero_iff h0).mpr hρ)

end Brockian.QuasiRH003

end
