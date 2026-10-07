# Static audit of the openai/math family 003 formalization — the quasi-Riemann hypothesis (θ = 7/8)

**Status:** DRAFT for internal review (Chris). Static pass only; **no Lean kernel was run** (see §3.4).
**Verifier:** Riemann Labs / primaryhosting (third party). **Not the author of the result.**
**Date of audit:** 2026-10-07, from a sparse clone of `openai/math/lean` at the pinned commit.
**Consumers in this corpus:** `Brockian/QuasiRHTransfer.lean` (Mathlib-only transfer), `formal/QuasiRH003/` (θ = 7/8 instantiation and open targets).
**Machine-readable provenance:** `provenance/external-inputs/openai-math-003/manifest.json` and the frozen closure lists beside it.

Same form as `writeups/zeta-two-thirds-independent-replication.md`: object, statement fidelity, trust chain, provenance, what is and is not established, how to reproduce.
---

## 0. Verdict in one paragraph

The four formal statements of family 003 are stated against Mathlib's own `riemannZeta` and `DirichletCharacter.LFunction` (the analytic continuations), with no custom definitions in the ζ, Dirichlet, or Siegel challenges and only the standard three axioms permitted. A text scan of the complete import closure — 2,924 modules, 489,414 lines for the 7/8 result; 306 modules, 70,124 lines for Siegel — finds **zero** `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `implemented_by`, or `extern`, and no metaprogramming (`macro`/`elab`/`syntax`) that could hide one. The Mathlib pin and both dependency pins are real upstream commits. **What this audit did not do is run the kernel**: no Lean toolchain was reachable from the audit environment. Until `lake build` + `#print axioms` completes on the 003 closure (Mode B in the README), the correct Riemann Lab badge for anything resting on 003 is *pending*, not PROVED. Three provenance findings below need to travel with the result wherever it is cited.

---

## 1. Object audited

| Item | Value |
|---|---|
| Repository | https://github.com/openai/math |
| Commit | `adc7f1241b42e322a6451854ab7e4b4c146bf78a` — 2026-10-06 14:58:50 −0700, "Initial commit" (single commit; no history) |
| Toolchain | `leanprover/lean4:v4.34.1` (sha256 `d5edba4e…bea7b`) |
| Mathlib pin | `leanprover-community/mathlib4 @ d13f23b723b8a846827a245b89c10fc7d3f11612` — verified upstream, 2026-09-24, "chore: bump toolchain to v4.34.1" |
| Scope note | `lean/docs/003.md` |
| Checker | [leanprover/comparator](https://github.com/leanprover/comparator) — challenge/solution separation; config in `ComparatorChallenges/*.json` |
| Permitted axioms (all four) | `propext`, `Quot.sound`, `Classical.choice` |
| `enable_nanoda` | `false` (no external kernel re-check configured) |

Audited file hashes (sha256, at the commit above):

```
065f8c9a…12cc5  ComparatorChallenges/QuasiRiemannHypothesis.lean
8fb13ad9…eff54  ComparatorChallenges/DirichletSevenEighths.lean
cb5e404f…0cfc2  ComparatorChallenges/HeckeSevenEighths.lean
bedaac02…136ce  ComparatorChallenges/SiegelZeros.lean
d98c4a7e…6ae89  OAI/NumberTheory/DirichletL/Nonvanishing.lean
0f52159a…af615  OAI/NumberTheory/DirichletL/Detector/FinalAssemblyUnconditional.lean
cf6105a2…c0794  lake-manifest.json
08904323…03d82  patches/PrimeNumberTheoremAnd-lean4341.patch
```

---

## 2. Statement fidelity

The question here is the one the "trust you can check" thesis turns on: does the Lean theorem say what the paper says, against definitions a third party already trusts?

### 2.1 Riemann zeta — `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`

```lean
theorem riemannZeta_ne_zero_of_seven_eighths_lt_re
    {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) : riemannZeta s ≠ 0
```

- `riemannZeta` is Mathlib's (`Mathlib/NumberTheory/LSeries/RiemannZeta.lean`), the analytic continuation via Hurwitz zeta, not a series.
- No `s ≠ 1` hypothesis: Mathlib's junk value at `s = 1` is nonzero (Mathlib's own `riemannZeta_ne_zero_of_one_le_re` has the same shape), so the statement is correct as written.
- **Reading: exactly the paper's Theorem 1.1 restricted to ζ. Faithful.**

### 2.2 Dirichlet L-functions — `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`

```lean
theorem LFunction_ne_zero_of_seven_eighths_lt_re
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0
```

- `DirichletCharacter.LFunction` is Mathlib's continuation (`DirichletContinuation.lean`). Uniform in `q` (any positive modulus) and in `χ` (primitive or not).
- Pole exclusion is exactly `χ = 1 ∧ s = 1`.
- **Faithful. This is the theorem the Brockian programme consumes:** for `q = 5` it covers ζ_B = L(·, χ₀ mod 5) and the three non-principal characters.

### 2.3 Hecke L-functions over ℚ(√−3) — `OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re`

```lean
theorem LFunction_ne_zero_of_seven_eighths_lt_re
    (χ : Character) {s : ℂ} (hs : (7 / 8 : ℝ) < s.re)
    (hpole : ¬ (χ.residue = 1 ∧ s = 1)) : LFunction χ s ≠ 0
```

- **Different in kind from 2.1–2.2.** Mathlib has no Hecke L-function. `HeckeFamily.LFunction` is *defined inside the challenge file* (~150 lines) as a theta-series construction: products and rescalings of `HurwitzZeta.hurwitzEvenFEPair`, assembled into a `WeakFEPair`, with `LFunction χ s := latticeL (coefficients χ) s / 6` (6 = #units of ℤ[ω]). `Character` is a `MulChar (O ⧸ 𝔪) ℂ` trivial on units — a ray-class character for the class-number-1 field, i.e. a finite-order Hecke character.
- The comparator JSON has `definition_names: []`, so **the identity of this construction with the classical Hecke L-function is a definition the reader must check by hand, not a verified fact.** The construction is plausible (it is the standard theta-lift of a ray-class character), but it is the one place in 003 where trust rests on ~150 lines of ad-hoc definition rather than on Mathlib.
- Irrelevant to the mod-5 programme. Flagged for anyone citing the Hecke statement.

### 2.4 Siegel zeros — `OAI.SiegelZeros.WeightedTorusJets.exists_absolute_real_zero_gap`

```lean
∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
  ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
  ∀ β : ℝ, 0 < β → β < 1 → χ.LFunction (β : ℂ) = 0 → c ≤ (1 - β) * Real.log (q : ℝ)
```

- Stated against Mathlib's `LFunction` and `IsPrimitive`. Real-valuedness as `∀ a, (χ a).im = 0`. Faithful to the scope note.
- **As formalized, this is implied by 2.2 in three lines**: any real zero has β ≤ 7/8, so (1−β)·log q ≥ (log 3)/8 ≈ 0.137, i.e. c = (log 3)/8 works. The theorem is therefore *weaker* than 2.2 restricted to real zeros.
- **But the proof is independent**: the Siegel import closure (306 modules) and the 7/8 closure (2,924 modules) share **zero** modules. So 003 contains two unrelated proofs that Siegel zeros don't exist in the log-q sense. That is worth more than one, and the theorem map should record both routes rather than filing Siegel as a corollary.
- A second declaration, `dirichletRealZeroBound_proof`, states the same thing with the three β-hypotheses conjoined.

### 2.5 What 003 does *not* formalize

- **The 11/12 alternate proof** (`preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/paper2.pdf`). Correction to an earlier note: this is a *different proof of a weaker half-plane* (Re s > 11/12 ⊂ Re s > 7/8), covering Dirichlet and Hecke, not a stronger result for ζ. The README names it as one of two exceptions to the fixed automated procedure and says its write-up was human-edited for readability. It has no entry in `formalization.yaml` and no comparator challenge. Value: a second, independent-method route to a zero-free half-plane; it does not change any number in the Brockian corpus.
- **The paper's later applications** (scope note: "The paper's later applications are not included"). In particular the prime-distribution consequences ψ(x; q, a) = x/φ(q) + O(x^{7/8+ε}) are **paper-level**, not Lean. Two companion papers in the release use them: *A Power Saving for Polynomial Differences at Prime Arguments* and *A power saving for intersective polynomial differences…* (both 2026-10-05) — the explicit-formula derivation Codex sketched for the mod-5 rays is presumably written out there; that is the reference to cite for ψ(x; 5, a) until Lean catches up.
- No explicit constant `c` in the Siegel theorem; no explicit constants or thresholds anywhere — the 7/8 result is a pure half-plane, which is all the ζ_B transfer needs, but the x^{−1/8+ε} rate for the rays cannot be plotted as an error bar.

---

## 3. Trust chain (static)

### 3.1 Closure sizes

| Target | Internal modules | Lines | Mathlib modules imported | Other externals |
|---|---|---|---|---|
| ζ + Dirichlet 7/8 | 2,924 | 489,414 | 248 | `PrimeNumberTheoremAnd.Wiener`, `RellichKondrachov…Rellich`, `Lean.Elab.Tactic.Omega` |
| Hecke 7/8 | 2,925 | 489,450 | 248 | same |
| Siegel | 306 | 70,124 | 322 | `PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport`, `Lean.Elab.Tactic.Omega` |

Module lists frozen in `provenance/external-inputs/openai-math-003/closure_*.txt`.

### 3.2 Token scan (comments stripped; all three closures)

| Token | Severity | Count |
|---|---|---|
| `sorry` | fatal | **0** |
| `admit` | fatal | **0** |
| `axiom` | fatal | **0** |
| `unsafe` | fatal | **0** |
| `implemented_by` | fatal | **0** |
| `@[extern` | fatal | **0** |
| `native_decide` | review | **0** |
| `opaque` | review | **0** |
| `partial def` | review | **0** |
| `maxHeartbeats 0` | review | **0** |
| `macro`/`elab`/`syntax`/`macro_rules` | review | **0** |
| `decide` | info | 754 (7/8) / 83 (Siegel) — kernel-checked |
| `noncomputable` | info | 3,220 / 495 |

`Lean.Elab.Tactic.Omega` is just the `omega` tactic.

### 3.3 Shape of the 7/8 proof's top

`FinalAssemblyUnconditional.lean` discharges a proposition `DetectorCertifiedBands` by applying `terminal_certificate` with **explicit rational parameters** (1/4, 9/4, 33/50, …) closed by `norm_num` and `linarith`. The "certification" is symbolic, not floating-point; consistent with the zero count of `native_decide`. The naming (`Probe…`, `Detector…`, `Energy.CertifiedExistence`, `Moments…`) suggests a moment/energy method with a detector functional; the paper's proof overview (pp. 4–7) should be read alongside it. This audit did not evaluate the mathematics of the 489k lines — that is what the kernel is for.

### 3.4 What a kernel check adds

Everything in 3.2 is necessary, not sufficient. Lean's kernel is the arbiter; `#print axioms` on the four target theorems is the one-line test, and `comparator` adds the challenge/solution statement match. The audit environment could not reach the Lean release host or the Mathlib cache (network allowlist), so **this remains the outstanding step**. Commands in `formal/QuasiRH003/Import003.lean`, MODE B. Expect hours on a workstation; the repo's own README warns about `vm.max_map_count` on Linux for large builds.

---

## 4. Provenance of dependencies — three findings

### 4.1 The PrimeNumberTheoremAnd "compatibility patch" is substantially new code

`patches/PrimeNumberTheoremAnd-lean4341.patch` (2.0 MB) touches 55 files and **creates 47 that do not exist at the pinned upstream commit** (verified by fetching `c39a751…` from AlexKontorovich/PrimeNumberTheoremAnd and listing its tree): the entire `PrimeNumberTheoremAnd/SiegelZeros/` directory (12 files + `NOTICE.md`), plus `Erdos970/`, `Catalan/`, `ZetaFive/`. Every one of the 306 Siegel modules imports `PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport`, which is one of these.

`SiegelZeros/NOTICE.md` says the material "is derived from PrimeNumberTheoremAnd" and retains copyright notices for Matteo Cipollina and Stefan Kebekus (the Hadamard-factorization contributors). So the accurate provenance line is: **PNT+-derived Hadamard-product support, captured from a different PNT+ revision and vendored into the patch; not present at the pinned upstream commit.** It lives in the PNT+ namespace but is not what a reader cloning upstream PNT+ would find.

Soundness impact: none that the static scan can see — the patch adds no `sorry`/`axiom`/`unsafe`, and the kernel will check it like everything else. Provenance impact: real. "Depends on PrimeNumberTheoremAnd" overstates the upstream dependency.

### 4.2 `PrimeNumberTheoremAnd/Wiener.lean` is replaced, not patched

The same patch rewrites `Wiener.lean` (+439 / −2,716 lines) with the header "This compatibility port retains the proven declarations used by this project." Upstream's 221 KB file is replaced by OpenAI's trimmed port; 173 declaration heads removed, 138 added (mostly `lemma` → `theorem` renames and pruning). The 7/8 closure imports this module (via `IdealMangoldt.lean` and `PrimeCounting/Progressions.lean`). Same soundness/provenance split as 4.1: the Wiener–Ikehara machinery in the closure is OpenAI's rewrite of Kontorovich et al., kernel-checked at build, not upstream verbatim.

### 4.3 Pins are genuine

| Package | Pin | Upstream |
|---|---|---|
| mathlib4 | `d13f23b7…` | exists; 2026-09-24 |
| PrimeNumberTheoremAnd | `c39a7511…` | exists; 2026-10-01 "Chore: Bump to V4.34.0 (#1782)" |
| rellich-kondrachov | `70f85d4c…` | exists; 2026-05-14 |

No Mathlib patch exists in `patches/`; the statements in §2 are against unmodified Mathlib.

---

## 5. Consequences for the Brockian corpus

Theorem map entries, with the provenance tag each must carry.  "Mode A" = this repo's CI kernel-checking `Brockian/QuasiRHTransfer.lean` at lean-4.32.0 + AXLE attestation; "Mode B" = building `formal/QuasiRH003/Import003.lean` inside openai/math (instructions in that file).

| # | Statement | Where | Depends on | Badge now | Badge after Mode A | Badge after Mode B |
|---|---|---|---|---|---|---|
| T1 | `1 − 5^{−s} ≠ 0` for Re s > 0 | `Brockian.QuasiRHTransfer.eulerFactor_five_ne_zero` | Mathlib | pending CI | PROVED | PROVED |
| T2 | ζ_B(s) = 0 ⟺ ζ(s) = 0 on Re s > 0 | `…QuasiRHTransfer.zetaB_eq_zero_iff` | Mathlib | pending CI | PROVED | PROVED |
| T3 | ζ_B(s) = `LFunctionTrivChar 5 s` for s ≠ 1 | `…QuasiRHTransfer.zetaB_eq_LFunctionTrivChar` | Mathlib | pending CI | PROVED | PROVED |
| T4 | θ-transfer, both directions; θ-strip | `…QuasiRHTransfer.zetaB_ne_zero_of_zeroFree`, `riemannZeta_ne_zero_of_zetaB_zeroFree`, `zetaB_zero_strip_of_zeroFree` | Mathlib | pending CI | PROVED | PROVED |
| T5 | ζ(ρ) = 0, 0 < Re ρ < 1 ⟹ ζ(1−ρ) = 0 | `…QuasiRHTransfer.riemannZeta_one_sub_eq_zero_of_eq_zero` | Mathlib | pending CI | PROVED | PROVED |
| T6 | ζ_B(s) ≠ 0 for Re s > 7/8 | `Brockian.QuasiRH003.zetaB_ne_zero_of_seven_eighths_lt_re` (+ `'` via Dirichlet) | **003 @ adc7f124** | CONDITIONAL | — | PROVED ⟨ext: 003⟩ |
| T7 | L(s, χ) ≠ 0, χ mod 5, Re s > 7/8 | `…QuasiRH003.LFunction_mod5_ne_zero_of_seven_eighths_lt_re` | **003** | CONDITIONAL | — | PROVED ⟨ext: 003⟩ |
| T8 | zeros of ζ_B (and ζ) in the strip: 1/8 ≤ Re ρ ≤ 7/8 | `…QuasiRH003.zetaB_zero_strip`, `riemannZeta_zero_strip` | **003** + T4 | CONDITIONAL | — | PROVED ⟨ext: 003⟩ |
| P1 | ψ(x; 5, a) = x/4 + O(x^{7/8+ε}) | paper only | 003 + explicit formula | CONJECTURED (proof sketch) | — | — |
| P2 | Δ₅(x) = O(x^{7/8+ε}) (quadratic prime race bound) | paper only | P1 | CONJECTURED | — | — |
| A/B | scattering function / det Φ_{Γ₀(5)} analytic off the band [1/16, 7/16] | `formal/QuasiRH003/Targets.lean` | T8 | OPEN (card `math-scat5-scattering-pole-band`) | — | PROVED ⟨ext: 003⟩ once the `sorry`s close |

Two structural notes for the map:

1. **T3 gives a second, independent route to T6.** `Brockian.QuasiRH003.zetaB_ne_zero_of_seven_eighths_lt_re'` reaches ζ_B through the *Dirichlet* theorem (χ₀ mod 5) rather than the ζ theorem. Same external source, different theorem; if either formal statement were ever retracted the other would still stand.
2. **T4's converse direction is the honest statement of the programme's position.** Any zero-free half-plane proved for ζ_B *is* the same half-plane for ζ. The Brockian formulation can only win by exposing structure that produces a new estimate — it cannot win by being an easier problem.

The public theorem count should not move on the strength of this audit. It moves when `Brockian.QuasiRHTransfer` is AXLE-attested (Mode A; up to 10 declarations, all Mathlib-only), and again only if a Mode B receipt is committed under `provenance/` for the `QuasiRH003` instantiations.

Toolchain note: this corpus pins Mathlib v4.32.0 (`81a5d257`); openai/math pins `d13f23b7` (v4.34.1). Every Mathlib lemma used by `QuasiRHTransfer.lean` — `LFunctionTrivChar`, `LFunctionTrivChar_eq_mul_riemannZeta`, `norm_natCast_cpow_of_pos`, `rpow_lt_one_of_one_lt_of_neg`, `riemannZeta_one_sub`, `riemannZeta_ne_zero_of_one_le_re`, `Nat.Prime.primeFactors`, `Nat.prime_five` — was checked present with identical signature at **both** pins, so the same source file builds in both environments.

---

## 6. Replication

Repo side (this corpus):

```sh
# Mathlib-only transfer — kernel-checked by CI on any PR touching it; locally:
python3 scripts/check_lean_modules.py Brockian/QuasiRHTransfer.lean
# then, in a scratch file:  #print axioms Brockian.QuasiRHTransfer.zetaB_zero_strip_of_zeroFree
```

External side (openai/math):

```sh
# 1. pin
git clone https://github.com/openai/math.git && cd math
git checkout adc7f1241b42e322a6451854ab7e4b4c146bf78a
sha256sum lean/ComparatorChallenges/{QuasiRiemannHypothesis,DirichletSevenEighths,HeckeSevenEighths,SiegelZeros}.lean   # compare §1

# 2. static audit (seconds)
cd lean
python3 -I <this repo>/scripts/audit_external_lean_closure.py . OAI.NumberTheory.DirichletL.Nonvanishing
python3 -I <this repo>/scripts/audit_external_lean_closure.py . OAI.NumberTheory.SiegelZeros.Main
# compare against provenance/external-inputs/openai-math-003/manifest.json

# 3. kernel check (hours)
lake update && lake exe cache get
lake build OAI.NumberTheory.DirichletL.Nonvanishing
lake env comparator ComparatorChallenges/QuasiRiemannHypothesis.json
lake env comparator ComparatorChallenges/DirichletSevenEighths.json
# then, in a scratch file:
#   #print axioms OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re
#   #print axioms OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
```

---

## 7. Open questions worth raising publicly

1. Will OpenAI publish `#print axioms` output and a `comparator` run log for the four 003 targets, and enable `nanoda` as an independent kernel? The repo asks the community to check; the cheapest check is the one they already ran.
2. Will the PNT+-derived `SiegelZeros/` support and the `Wiener.lean` port be upstreamed to PrimeNumberTheoremAnd, or published as a named package? As a patch inside another project's namespace it is hard to cite and harder to maintain.
3. Is there a formalization planned for the paper's prime-distribution applications (the explicit-formula step)? That is the piece every downstream user — this programme included — needs next.
4. For the Hecke statement: is a Lean proof planned that `HeckeFamily.LFunction` agrees with the classical Hecke L-series on Re s > 1? That would move §2.3 from "definition to trust" to "theorem to check".

---

*Static audit performed from a sparse clone of `lean/` at the pinned commit. No Lean kernel was run. Every file hash, lemma name, and pin above was read from source; nothing was taken from the README or press coverage. Prepared with Claude (Anthropic) as the auditing agent; the verifier of record is Riemann Labs / primaryhosting.*
