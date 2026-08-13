# COMPOUND_CANDIDATES — composing the proved Brockian corpus

Date: 2026-08-13. Inputs surveyed: `aristotle/best_proofs/` (988 standalone .lean files, of
which ~254 are Brockian_* islands), `registry/domains.json` (983 entries: 770 PROVED,
213 PROVED_UNVERIFIED), `registry/theorems.json` (11,819 entries: 11,126 PROVED, 626
DEFINITION, 40 CONJECTURE, 20 CONDITIONAL, 7 DISCHARGED). All names below are exact
corpus/registry names; every "blocked by" line is a real definitional mismatch observed
in the files, not a guess.

Method note (honesty): a compound theorem below is only claimed to be *composable* —
i.e., its ingredients are proved and the gap is definitional glue — never to be already
proved. Registers follow the standing convention: PROVED / PROVED_UNVERIFIED /
CONDITIONAL / CONJECTURE. Composites inherit the *weakest* register of their inputs.

---

## 1. Ten compound-theorem candidates

### C1. `KernelPrincipalPairBridge` — transition kernel × q−2 counting
- **Composes:** `Brockian.TransitionKernel.totalSum_count` (double sum of the gap-g kernel
  over ZMod q counts nonzero-endpoint pairs), `universal_count_theorem`
  (aristotle/best_proofs/universal_count_theorem.lean: for odd prime q, gcd(g,q)=1,
  exactly q−2 principal pairs exist on `Fin q × Fin q`), and
  `Brockian.GoldbachComb.gCount_eq` (`gCount p c = if c = 0 then p−1 else p−2`).
- **Compound statement:** For an odd prime q and gap g with `(g : ZMod q) ≠ 0`,
  `∑ i, ∑ j, kernel q g i j = q − 2`, and this sum equals
  `(principalPairsQ q g).card` — the kernel's total mass IS the q−2 principal-pair count.
- **Why un-stateable today:** `TransitionKernel.kernel` lives on `ZMod q` with an
  ℕ-valued indicator (`i ≠ 0 ∧ i+g ≠ 0 ∧ j = i+g`); `universal_count_theorem` lives on
  `Fin q × Fin q` with `.val` arithmetic in `isPrincipalPair`. There is no
  `ZMod q ≃ Fin q` transfer lemma in the corpus matching the two "nonzero endpoint"
  predicates, so the equality cannot even be typed without a bridging bijection.
- **Difficulty:** EASY-MEDIUM. Finset bijection + ZMod case analysis — squarely in fleet
  strength. Register on completion: PROVED.

### C2. `DirichletKernelRealization` — transition kernel × Dirichlet (WheelK2 composite)
- **Composes:** `goldbachWheelK2_of_prime` (in
  aristotle/best_proofs/Brockian_GoldbachWheelK2_631.lean — proved via Dirichlet's
  theorem on primes in APs; instances `Brockian.GoldbachWheelK2_631` … `_1327` all
  PROVED) with `Brockian.TransitionKernel.admissibleStarts` and
  `twin_admissible_singleton` / `brockian_table_card`.
- **Compound statement:** For prime m ≥ 3, gap g, and any `i ∈ admissibleStarts m g`,
  for every N there exist primes p, q > N with `(p : ZMod m) = i` and
  `(q : ZMod m) = i + g`. I.e., **every nonzero entry of the transition kernel is realized
  by actual prime pairs at arbitrary height** — the kernel support equals the
  prime-pair support mod m. Corollary via `twin_admissible_singleton`: mod 3 the only
  Dirichlet-realizable twin channel is (2,1); mod 5 exactly the 3 Brockian channels.
- **Why un-stateable today:** `GoldbachWheelK2 m` quantifies over the residue of the
  *sum* p+q; the kernel constrains the *pair* of residues (p mod m, (p+g) mod m). The
  quantifier shapes don't match — the compound needs a two-variable Dirichlet statement
  (two independent applications of primes-in-APs), which no corpus file states.
- **Difficulty:** EASY-MEDIUM. Mathlib's Dirichlet theorem
  (`Nat.setOf_prime_and_eq_mod_infinite` machinery) is already used successfully by the
  WheelK2 family; two independent applications is routine. Register: PROVED.

### C3. `KernelAdmissibilitySingularSeries` — transition kernel × Hardy–Littlewood positivity
- **Composes:** `Brockian.SingularSeries.Wire.singular_series_pos_unconditional`
  (admissible G ⇒ 0 < singular series; PROVED, hole-free per module header),
  `Brockian.SingularSeries.nu_p` / `localFactor`, and the TransitionKernel pinning
  lemmas `twin_pins_mod_three`, `quadruplet_pins_mod_five`, plus
  `ConstellationLocalCountK3` (`localCount p H = p − |image of H in ZMod p|`).
- **Compound statement:** If for every prime p the gap pattern G has
  `admissibleStarts p g ≠ ∅` (kernel-admissibility, decidable per p), then
  `Brockian.SingularSeries.Wire.IsAdmissible G` holds, hence
  `0 < singularSeries G`. One theorem: **kernel-level admissibility implies a positive
  Hardy–Littlewood constant.**
- **Why un-stateable today:** two rival admissibility notions. `admissibleStarts` counts
  *pair starts* `i` on `ZMod q` for a single gap g; `IsAdmissible` demands
  `nu_p G < p` for a `Finset ℕ` of *offsets*. No corpus lemma converts
  "nonempty admissible starts at p" into "`nu G p < p`" (the ν-counting in
  `Frontier.BrockianSieveDeep.nu_le_card` gets close but stops at ν ≤ |G|).
- **Difficulty:** MEDIUM. The conversion is finite ZMod counting per prime (fleet
  strength), but stating it for all p needs the `localCount` image formula as the pivot.
  Register: PROVED.

### C4. `FibPisanoEquidistribution` — Fibonacci/Pisano × character sums
- **Composes:** `Brockian.ElementaryPlates.pisano_five`
  (`fib (n+20) ≡ fib n [ZMod 5]`, PROVED) and `fib_window_turn`
  (`fib (n+5) = 3·fib n` in ZMod 5) with the character-sum toolkit of
  `Brockian.MsGaussSum.gauss_sum_abs_sq` and the orthogonality-style counting of
  `Brockian.GoldbachComb.gCount_eq`.
- **Compound statement:** Over one Pisano period, Fibonacci is *exactly* equidistributed
  mod 5: for every `r : ZMod 5`,
  `((Finset.range 20).filter (fun n => (fib n : ZMod 5) = r)).card = 4`; equivalently
  every nontrivial additive character sum `∑ n ∈ range 20, e(k·fib n/5)` vanishes.
  (Verified numerically: residues 0,1,1,2,3,0,3,3,1,4,0,4,4,3,2,0,2,2,4,1 — each class
  hit exactly 4 times. This is special to p = 5, the Wall–Sun–Sun-flavored case, and is
  exactly the Brockian pentagonal modulus.)
- **Why un-stateable today:** the Pisano results live in `ZMod 5`; the corpus's character
  sums live in `ℂ` via `Complex.exp` (MsGaussSum). The standard
  count-vs-exponential-sum identity `card = (1/q)·∑_k Σ_n e(k(f n − r)/q)` is stated
  nowhere, so the two islands cannot talk. The counting form alone is stateable and
  `decide`-able immediately.
- **Difficulty:** EASY (counting form, `decide` over range 20) / MEDIUM (exponential-sum
  form, needs the finite Fourier inversion bridge). Register: PROVED.

### C5. `GoldenBeattyPartition` — Beatty × golden fundamental equation
- **Composes:** `Brockian.MsBeatty.beatty` (full Beatty partition theorem: for irrational
  r > 1 with 1/r + 1/s = 1, every n > 0 is hit exactly once by ⌊mr⌋ ∪ ⌊ms⌋; PROVED) with
  `golden_fundamental` (`φ² = φ + 1`, PROVED_UNVERIFIED) and
  `Brock.GoldenRatio.sqrt5_pos` / `BrockianQuantum.golden_eq`.
- **Compound statement:** The Beatty sequences `⌊n·φ⌋` and `⌊n·φ²⌋` partition ℕ⁺
  (the lower and upper Wythoff sequences). Pure instantiation: φ² = φ + 1 gives
  1/φ + 1/φ² = 1, and irrationality of φ follows from irrationality of √5.
- **Why un-stateable today:** nothing structural — only that `Irrational goldenRatio` is
  proved nowhere in the corpus (the φ islands prove positivity and the quadratic, never
  irrationality), and the hypothesis `1/r + 1/s = 1` needs the division-form rearrangement
  of `φ² = φ + 1`, which lives in a PROVED_UNVERIFIED island with its own local `φ`.
  The three φ definitions (`Brockian.φ`, `BrockianFramework.φ`, `D5Structure.φ`,
  Mathlib's `goldenRatio`) are not identified with each other anywhere.
- **Difficulty:** EASY. `Nat.Prime.irrational_sqrt` + field_simp. This would be the
  cheapest genuinely-classical compound in the whole list. Register: PROVED.

### C6. `PentagonWalkLucasLaw` — C5/golden spectrum × Fibonacci counting
- **Composes:** `BrockianFrontier.PentagonSpectrum.C5_golden_eigenvalue`
  (`C5.charpoly.eval ((√5−1)/2) = 0`), `Brockian.Spectral.golden_unique_to_five` +
  `neg_golden_in_C5_spectrum`, `Brockian.PentagonMultiplicities.finrank_eigenspace_golden`
  (multiplicity 2), `Chem.huckel_C5` (full eigenvalue list 2cos(2πk/5)), and
  `Brockian.MsBinet.binet` with the local `lucas` def of `Brockian.ElementaryPlates`.
- **Compound statement:** For all k,
  `Matrix.trace (C5ᵏ) = 2ᵏ + 2·(−1)ᵏ·(lucas k)` — closed k-walks on the pentagon are
  counted by Lucas numbers (since the spectrum is {2, (φ−1)×2, (−φ)×2} and
  (φ−1)ᵏ + ... folds to (−1)ᵏ·L_k via Binet). First genuinely *quantitative* bridge
  between the pentagon-spectral island and the Fibonacci island.
- **Why un-stateable today:** the spectral corpus states eigenvalues only as
  `charpoly.eval λ = 0` facts, never as a diagonalization; `trace (C5^k) = Σ λᵏ` needs
  the assembled spectral decomposition (the pieces exist in `Brockian.PentagonIsotypic`
  / `C5SpectralMultiplicities` as eigenmode statements but no trace-power formula).
  Also there is no Binet-for-Lucas: `lucas` is a bare recursive def with no closed form.
- **Difficulty:** MEDIUM. Route that avoids diagonalization entirely: charpoly of C5
  gives a linear recurrence on `trace (C5^k)` (Newton/Cayley–Hamilton — matrix algebra
  is a demonstrated strength), then induction against the Lucas recurrence. Small-k
  instances are `decide`-able on the ℤ matrix immediately. Register: PROVED.

### C7. `PartitionPentagonalMod5` — Euler/Franklin partition theory × ZMod case analysis
- **Composes:** `Brockian.FranklinFixedPoint.pentagonalNumberTheorem` (the
  **unconditional** pentagonal number theorem, PROVED — roadmap #1 closed),
  `Brockian.PartitionRecurrence.partition_recurrence` (Euler's recurrence for the
  partition generating function, PROVED), and `Brockian.PentagonalPartition.pent_values`
  / `pent_reflect`.
- **Compound statement:** The pentagonal recurrence reduced into `ZMod 5`:
  `(p(n) : ZMod 5) = ∑_{k≠0} (−1)^{k+1} p(n − g_k)` for the generalized pentagonal
  numbers g_k ≤ n, plus verified instances `p(4) ≡ p(9) ≡ p(14) ≡ p(19) ≡ p(24) ≡ 0
  (mod 5)` — the concrete gateway toward Ramanujan's congruence p(5n+4) ≡ 0 (mod 5).
- **Why un-stateable today:** `partition_recurrence` is stated on ℤ-coefficients of
  `PowerSeries` (`(genFun pstChar).coeff`); the corpus has `coeff_partitionGF` linking to
  partition counts, but no cast lemma pushing the whole convolution into `ZMod 5`, and no
  machinery to *evaluate* p(n) for concrete n except by the recurrence itself (direct
  `decide` on `Nat.Partition n` blows up near n = 24).
- **Difficulty:** EASY-MEDIUM for the ZMod recurrence + instances (ring_nf + norm_num
  chains). The general p(5n+4) ≡ 0 congruence is OPEN for this fleet — it needs
  q-series/modular machinery the corpus does not have. State the instances, register the
  general congruence as CONJECTURE.

### C8. `GoldbachLocalFactorCountIdentity` — Goldbach character count × singular-series local factor
- **Composes:** `Brockian.GoldbachComb.gCount_eq` (`gCount p c = p−1` if c=0 else `p−2`;
  PROVED), the `Kp` / `K23` local-factor lemmas of `Brockian.Goldbach.LocalWheel`
  (`K23_pos_iff_two_dvd`, `Kp_five`, … all PROVED), and
  `Brockian.SingularSeries.localFactorAt_eq`.
- **Compound statement:** For odd prime p and `n : ZMod p`, the Goldbach local density
  identity `Kp p n = (p · gCount p n) / (p−1)²` — the ℚ-valued Hardy–Littlewood local
  factor at p *is* the normalized nonzero-residue representation count. This fuses the
  three separately-proved local-Goldbach islands (gCount, Kp, localFactor) into one
  object with two evaluations.
- **Why un-stateable today:** `gCount` is ℕ-valued on `ZMod p` with a `[Fact p.Prime]`
  instance; `Kp` is ℚ-valued on ℤ shifts h with its own divisibility case-split; there
  is no cast lemma `((gCount p (h : ZMod p)) : ℚ)` nor an alignment of "c = 0 in ZMod p"
  with "p ∣ h". Pure normalization glue, but it must be written.
- **Difficulty:** EASY-MEDIUM. field_simp + the two existing case analyses. Register:
  PROVED.

### C9. `RayUniformityTransfer` — transitive-action uniformity × ray decomposition
- **Composes:** `Brockian.weight_const_of_transitive` +
  `const_of_transitive_invariant.equidistribution_of_transitive_symmetry` (invariant
  weight under a pretransitive action is constant, with the sum/card corollaries —
  PROVED) with the ray island `mem_ray_iff` (`n ∈ Ray p i ↔ (n : ZMod p) = i`),
  `ray_cover`, `unique_membership` (all PROVED_UNVERIFIED).
- **Compound statement:** The unit group `(ZMod p)ˣ` acts transitively on the p−1
  nonzero rays; hence any `(ZMod p)ˣ`-invariant weight on nonzero rays is uniform —
  each nonzero ray carries exactly `1/(p−1)` of the total. This turns the descriptive
  ray-decomposition (rays partition ℕ) into a *rigidity* statement: symmetric counting
  measures cannot prefer a ray. (The clean finite analogue of Dirichlet density
  equidistribution, provable with zero analytic input.)
- **Why un-stateable today:** the uniformity theorems are typeclass-generic
  (`MulAction.IsPretransitive G X`); the rays are a bespoke inductive/`Finset` structure
  (`BrockRay`, `Mod5Ray`, `HarmonicArch.RaySpace` — three near-duplicate definitions,
  all PROVED_UNVERIFIED, none with a `MulAction` instance). Need: one canonical ray
  type, a `MulAction (ZMod p)ˣ` instance on nonzero rays, and a pretransitivity proof
  (which is just unit-group transitivity on nonzero residues).
- **Difficulty:** EASY-MEDIUM. All finite algebra. Note the composite inherits
  PROVED_UNVERIFIED from the ray island unless the ray files are re-verified first.

### C10. `PentagonChordGoldenSpectrum` — pentagon geometry × spectral golden ratio
- **Composes:** `pentagon_chord_formula`
  (`pentDist j k = 2·|sin(π(k−j)/5)|`, PROVED_UNVERIFIED) with
  `Brockian.Spectral.golden_sub_one_eq_two_cos` (φ − 1 = 2cos(2π/5), PROVED),
  `BrockianFrontier.PentagonSpectrum.C5_golden_eigenvalue`, and
  `C4.BM3.pentagonal_pentagon_area`.
- **Compound statement:** `pentDist 0 2 / pentDist 0 1 = φ` (diagonal-to-side ratio of
  the regular pentagon is the golden ratio), and therefore the pentagon's *metric*
  golden ratio and its *spectral* golden eigenvalue (2cos(2π/5) = φ − 1 in the C5
  spectrum) are the same number witnessed two ways — geometry and spectrum fused for
  the first time in the corpus.
- **Why un-stateable today:** the geometry island's `pentDist` and the spectral island's
  eigenvalues never meet: no file states sin(2π/5)/sin(π/5) = 2cos(π/5), and the
  identity 2cos(π/5) = φ (vs the proved 2cos(2π/5) = φ − 1) is absent. Both need the
  double-angle manipulations Mathlib supplies (`Real.sin_two_mul`), but nobody has
  written the two-line bridge. Also `pentDist` is PROVED_UNVERIFIED.
- **Difficulty:** EASY-MEDIUM (trig identity chain; `nlinarith`/`polyrith`-shaped).
  Register: PROVED once pentagon_chord_formula is re-verified, else PROVED_UNVERIFIED.

---

## 2. Five next research directions (ranked by corpus-strength fit × novelty)

### R1. Finite harmonic analysis on ZMod q — the "discrete Weyl" toolkit  [TOP PICK]
- **Why it fits:** the fleet's proven strengths are exactly Finset sums, ZMod case
  analysis, and `decide` on small moduli. Finite Fourier inversion, character
  orthogonality on `ZMod q`, and the count = (1/q)·Σ character-sum identity are all
  Finset-sum theorems with no analysis. `Brockian.MsGaussSum.gauss_sum_abs_sq` and
  `Brockian.GoldbachComb.gCount_eq` prove the fleet can already touch both ends.
- **What it unlocks:** C4, C8, C9 above; a *discrete* Weyl criterion
  ("all nontrivial character averages → 0 ⇒ ray densities equalize") that gives the
  Equidistribution program a finite home where its CONDITIONAL results
  (`equidistribution_of_asymptotic`, the whole BVReduction block) become PROVED
  finite-model analogues. Directly continues the corpus's strongest original line
  (kernel/wheel/q−2).
- **Honest register:** PROVED for everything finite; the lift from finite models to
  actual prime sequences stays CONDITIONAL (that is where BV/asymptotic hypotheses
  live, and they should stay named).

### R2. Trace-power spectral counting (Newton's identities on small graphs)
- **Why it fits:** matrix algebra over `Fin n` is a demonstrated strength (the entire
  BrockianQuantum block, CosTraceNorm family, Chem.huckel_C3–C20 cycle spectra). The
  corpus has ~40 charpoly-eval eigenvalue facts sitting idle; Cayley–Hamilton converts
  each into a linear recurrence for `trace (A^k)` without ever diagonalizing.
- **What it unlocks:** C6 (walk counts = Lucas numbers); analogous laws for
  `Chem.huckel_Cn` (walks on C_n vs Chebyshev), `ConstellationSpectrum.H1/H2/H3`;
  a uniform "spectral alphabet ⇒ counting law" template that turns the spectral island
  into a counting engine.
- **Honest register:** PROVED throughout — nothing conditional anywhere in this lane.

### R3. Partition congruence instances from the closed pentagonal theorem
- **Why it fits:** `FranklinFixedPoint.pentagonalNumberTheorem` +
  `PartitionRecurrence.partition_recurrence` are the corpus's biggest recent wins and
  currently have *zero* downstream consumers. Recurrence evaluation + ZMod reduction is
  induction + norm_num, i.e., fleet bread-and-butter.
- **What it unlocks:** C7; a verified p(n) table (say n ≤ 100) as a corpus artifact;
  Ramanujan congruence *instances* mod 5, 7, 11 at concrete n.
- **Honest register:** PROVED for the recurrence-mod-m and all instances;
  p(5n+4) ≡ 0 (mod 5) in general is CONJECTURE for this fleet — do not queue it as a
  proof target, queue only instances.

### R4. Two-variable Dirichlet realization of kernel supports
- **Why it fits:** the WheelK2 family (150+ PROVED instances plus the generic
  `goldbachWheelK2_of_prime`) proves the fleet can drive Mathlib's Dirichlet theorem
  reliably. Extending from "sum residue realized" to "pair of residues realized" is the
  same tool applied twice.
- **What it unlocks:** C2; "kernel support = prime-pair support mod q" for every wheel in
  the corpus; makes every `admissibleStarts` computation a statement about actual primes
  rather than residue combinatorics.
- **Honest register:** PROVED (Dirichlet is unconditional in Mathlib). Note this gives
  infinitude *in each channel*, never counts — asymptotic channel densities remain
  CONDITIONAL (that is Chebotarev/PNT-in-APs territory, out of reach).

### R5. Effective deviation budgets: merging DeviationBound with SingularSeries.Convergence
- **Why it fits (weakest of the five, still real):** both blocks are PROVED
  (`Equidistribution.DeviationBound.*` 9/9,
  `SingularSeries.Convergence.err_bound`, `SingularSeriesConvergenceRate`), and the
  merge is inequality bookkeeping (Finset sums + `tendsto` composition — demonstrated
  strengths), not new analysis.
- **What it unlocks:** C3's quantitative sequel: one theorem
  "kernel-admissible G ⇒ singular series positive with explicit finite-range error ε(Q)".
  This is the honest, effective skeleton of Hardy–Littlewood with every analytic input
  still a named hypothesis.
- **Honest register:** CONDITIONAL by construction (BV-type and asymptotic hypotheses
  remain named forever at this fleet's capability level) — valuable precisely because
  the conditionality is explicit and the constants are effective.

---

## 3. What the corpus CANNOT do yet — observed capability gaps

Queue-planners: route around these; they are empirical, not speculative.

1. **Hard real/oscillatory analysis.** The sinc integrals are the canary:
   `Zeta23Scaffold.integral_sinc_sq` sits at PROVED_UNVERIFIED and the reattack queue
   (`aristotle/reattack_queue.json`) carries repeated re-attacks on this cluster.
   Anything needing contour integration, stationary phase, or genuine ∫ℝ asymptotics
   fails or stalls. Do not queue oscillatory-integral targets.
2. **Genuine analytic continuation.** Zeta results stop at re(s) > 1
   (`Riemann.zeta_ne_zero_re_gt_one`) plus imported special values; the functional
   equation is consumed, never re-derived. Nothing requiring continuation off the
   half-plane (zero counting, explicit formula) is within reach. The Uncharted-RH
   lesson stands: finite calibration ≠ global claim — witness-kernel interpretations
   died under blind refereeing (Aug 10-11).
3. **Prime asymptotics.** Every primes-in-intervals density statement in the corpus is
   CONDITIONAL (`equidistribution_of_asymptotic`, all four `EquidistributionBVReduction`
   theorems, the 20 CONDITIONAL entries in theorems.json). PNT-strength inputs are not
   provable here and should always enter as named hypotheses, never as goals.
4. **q-series / modular forms.** The Franklin closure was won with bare PowerSeries and
   a hand-built involution; there is no modular machinery at all. General Ramanujan
   congruences, eta-quotients, and theta identities are out of reach — instances only.
5. **Large `decide` blowups.** `native_decide` is banned corpus-wide (see file headers);
   plain `decide` dies on partition counts past n ≈ 20 and on kernels beyond small
   moduli. Big verification instances must go through recurrences or stay small.
6. **The PROVED_UNVERIFIED debt.** 213 domains.json entries — concentrated exactly in
   the ray-decomposition and pentagon-geometry islands that C9/C10 want to consume
   (`mem_ray_iff`, `pentagon_chord_formula`, `golden_fundamental`, all three duplicate
   φ/ray definitions). Composites inherit this register; re-verifying those islands
   through AXLE is a prerequisite for clean compound registers, and unifying the three
   `φ` definitions and three ray types is the single highest-leverage janitorial task.
7. **Statement-only files are not inputs.** The `Frontier_*_statement.lean` family
   (RH, FLT, BSD, P vs NP, …) proves well-formedness, not content. They must never
   appear as an ingredient in a compound-theorem queue item.
