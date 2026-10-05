# Audit — Non-Brockian Famous Open-Problem "Proofs" (The Frontier)

**Scope:** AXLE-sorry-free `.lean` files in `aristotle/best_proofs/` matching
`Frontier.* | Riemann.* | Goldbach.* | Twin.* | RH_* | P_vs_NP | Navier | Yang_Mills | Hodge | BSD | FLT | four_color | Poincare | abc_ | LargeCardinal | Cardinal | Zeta23`, **excluding** `Brockian*`-prefixed files.
**Mode:** read-only. No repo file modified, nothing committed.
**Population:** 200 files matched. ~55 read in full/depth; all 200 had main-declaration signatures + soundness-signal scans. Every distinct pattern is covered.

## Headline finding

**ZERO BOGUS files. No genuine soundness concerns.** A repo-wide scan found:
- **No `axiom` declarations** in any target file (every "axiom" grep hit was the English word "axiomatise"/"no unproved axioms" inside doc comments).
- **No `native_decide`, no `sorry`, no `sorryAx`** anywhere in the set.
- All `decide` uses are the **kernel-sound** tactic on decidable finite propositions (finite prime-pair searches, `ZMod n` residue counts, small graph facts) — not the unsound `native_decide`.
- **No file proves an open problem unconditionally.** Every file naming a still-open conjecture either (a) merely *states* it as a `def ... : Prop`, (b) proves a **conditional reduction** whose hard hypothesis is never discharged, (c) proves a **finite instance**, or (d) proves a genuinely-established/base-case theorem.
- Every conditional reduction that hangs its conclusion on an unproven structure/typeclass (`SpectralModel`, `GoldbachSpectralModel`, `BrockianConjectures`, `CatalanCoreCase`, `OddOrderSimpleComm`, `zero_correspondence`) was checked: **no instance of any such structure is ever constructed**, so the conditional can never be collapsed into an unconditional proof. (The one construction found, `spectralModel_of_goldbach : Goldbach → SpectralModel`, lives in an excluded Brockian file and runs the *safe* direction.)

## Verdict table (representative sample; patterns generalize to all 200)

| Target | Verdict | Statement (short) | Mechanism / Reason |
|---|---|---|---|
| Frontier.RH_statement | CONDITIONAL-REDUCTION | `(∀ s in strip, ζ s=0→s.re=1/2) → RiemannHypothesis`; also `RH ↔ no zeros right of ½` | Real reduction to Mathlib `RiemannHypothesis`; eliminates zeros outside strip via functional eqn + zero-free Re≥1. Hypothesis unproven. |
| Frontier.RH_iff_riemannHypothesis | CONDITIONAL-REDUCTION | `RiemannHypothesis ↔ ∀ s, ζ s=0 → s.re ≤ ½` | Honest unconditional equivalence; content = strip localization. Not a proof of RH. |
| Frontier.RH_Li_criterion | ESTABLISHED (finite core) | Li's criterion for a **finite** symmetric zero multiset | Genuine Bombieri–Lagarias argument; explicitly notes arithmetic input (Hadamard factorization) unavailable. |
| Frontier.P_vs_NP_statement | RESTATEMENT/DEFINITIONAL | `P ≠ NP ↔ ∃ L∈NP, L∉P` | Trivial equivalence; real content is `P ⊆ NP`. Truth of P≠NP left open. |
| Frontier.navier_stokes_regularity | CONDITIONAL-REDUCTION | shear flow `u=(w,0,0)` reduces NS to linear heat eqn | Conjecture kept as `def NavierStokesGlobalRegularity`; theorem proves shear reduction + explicit nonzero instance. |
| Frontier.yang_mills_mass_gap | CONDITIONAL-REDUCTION | continuum limit with **uniform** gap Δ ⇒ mass gap | Conjecture is a `def`; proves gap-stability-under-limits + free-massive base case. |
| Frontier.hodge_statement | CONDITIONAL-REDUCTION | base case p=0 + `Conjecture ↔ every Hodge class algebraic` | `HodgeConjecture` is a `def`; `HodgeData` axiomatizes (as struct fields) unavailable cohomology. |
| Frontier.BSD_statement | CONDITIONAL-REDUCTION | rank-0 base case + reduction `L(E,1)≠0 ↔ E(ℚ) finite` | `BSD` is a `def`; proves rank-0 case, assuming Mordell–Weil as hypothesis. |
| Frontier.FLT_statement | CONDITIONAL-REDUCTION | `(FLT for odd primes) → FLTPositive` | Reduces via Mathlib `of_odd_primes`; n=3,4 base cases from Mathlib. |
| Frontier.abc_statement | RESTATEMENT/DEFINITIONAL | `abcConjecture ↔ bounded-largest-member form` | `abcConjecture` a `def`; equivalence + finite exceptional triple (1,8,9). |
| Frontier.four_color_statement | RESTATEMENT/DEFINITIONAL | `FourColorStatement ↔ finite/Fin-n forms` | Compactness equivalence of statement forms; does **not** prove 4CT. |
| Frontier.five_color_theorem | CONDITIONAL (base case) | 4-degenerate planar ⇒ 5-colorable | Honestly labeled base case; planarity not used (greedy from degeneracy). |
| Frontier.poincare_3sphere | CONDITIONAL-REDUCTION | punctured-∼ℝ³ hypothesis ⇒ M ≅ S³ (+ converse) | Perelman's content supplied as hypothesis `h`; compactification argument proved. Includes `#print axioms` self-audit. |
| Frontier.bounded_prime_gaps | RESTATEMENT/DEFINITIONAL | `(∃B, infinitely many gaps ≤ B) ↔ liminf gaps < ∞` | Unconditional equivalence of two formulations; deep Zhang–Maynard fact not asserted. |
| Frontier.Green_Tao | RESTATEMENT + FINITE | `GreenTaoStatement` a `def`; proves form-equivalence + PrimeAP up to length 10 | Finite AP instances real; general statement left as def. |
| Frontier.Vinogradov_three_primes | CONDITIONAL + FINITE | `GoldbachBinary → VinogradovStatement` + base case n<500 by `decide` | Conditional on binary Goldbach; finite base case sound. |
| Frontier.Chen_theorem | CONDITIONAL + FINITE | `GoldbachEven → ChenStatement`; `Chen_base` for 4≤n≤200 | Conditional; explicitly notes Chen 1973 not in Mathlib. |
| Frontier.Catalan_Mihailescu | CONDITIONAL-REDUCTION | `CatalanCoreCase → (x,p,y,q)=(3,2,2,3)` | Hard core case is a hypothesis; sub-cases proven. |
| Frontier.feit_thompson_odd_order | CONDITIONAL + equivalence | `OddOrderSimpleComm → (odd order ⇒ solvable)` + iff | Hard content is the hypothesis. |
| Frontier.Goodstein_terminates | ESTABLISHED | `∀ n, ∃ k, goodstein n k = 0` (no hypothesis) | Genuine ordinal-descent proof (`ordOf < ε₀`, strict descent). Truly provable theorem. |
| Frontier.infinite_ramsey | ESTABLISHED | 2-coloring of ℕ-pairs has infinite mono set | Real, unconditionally provable theorem. |
| Frontier.friendship_theorem | ESTABLISHED | exactly-one-common-neighbor ⇒ universal friend | Correct hypotheses; real theorem. |
| Frontier.szemeredi_regularity | ESTABLISHED | Szemerédi regularity lemma | Real theorem (Mathlib `SzemerediRegularity`). |
| Frontier.cook_levin | ESTABLISHED | NP language ⇒ poly-size 3-CNF SAT reduction | Genuine Cook–Levin construction. |
| Frontier.langlands_reciprocity | ESTABLISHED (abelian) | Artin map on roots of unity, character bijection, Frobenius compat | Abelian/cyclotomic case = class field theory; not general Langlands. |
| Frontier.gaussian_correlation | ESTABLISHED (1-D) | `GaussianCorrelationProperty ℝ` + transport lemmas | 1-dimensional base case (trivial in 1D). |
| Frontier.deligne_weil_RH | ESTABLISHED (base) | Weil RH for **projective space** Pⁿ eigenvalues \|α\|=q^(w/2) | Explicitly "base case: projective space"; concrete computation. |
| Frontier.willmore_conjecture | ESTABLISHED (restricted) | Clifford torus minimizes among **tori of revolution**; energy=2π² ↔ R=√2 r | Restricted family computation, not full (Marques–Neves) conjecture. |
| Frontier.onsager_2d_ising | ESTABLISHED (partial) | concrete Onsager integrand/free-energy/criticality identities | Genuine computations at K=0 and criticality; not full solution. |
| Frontier.scholze_perfectoid_tilt | ESTABLISHED (base) | tilt char p, Frobenius bijective, tilt≅K when K perfect | Tilting facts / trivial base case. |
| Frontier.ngo_fundamental_lemma | RESTATEMENT + FINITE | trivial-endoscopy⇒FL, FL-iff, product closure, concrete orbital Fourier identity | Structural facts + a real finite character-sum identity. |
| Frontier.Goedel_second_incompleteness | ESTABLISHED (abstract) | abstract `ProvabilitySystem`, consistent ⇒ can't prove own consistency | Abstract Löb/GL derivation; not a claim about Con(PA) specifically. |
| Frontier.Banach_Tarski | ESTABLISHED | free rotation subgroup / paradoxical decomposition machinery | Real construction (uses Classical.choice, as expected). |
| Frontier.Suslin_line | ESTABLISHED + DEFINITIONAL | ℝ/ℚ are not Suslin lines; `SuslinHypothesis` a `def` | Independence left as def; concrete facts proven. |
| Frontier.CH_independent_statement | RESTATEMENT/DEFINITIONAL | `ContinuumHypothesis` def + equivalent reformulations | States CH + equivalences; independence not asserted as proved. |
| LargeCardinal.inaccessible/measurable_statement | RESTATEMENT/DEFINITIONAL | defines inaccessible / measurable cardinal notions + basic facts | Statement artifacts. |
| Frontier.inaccessible_implies_ConZFC | CONDITIONAL-REDUCTION | inaccessible cardinal ⇒ Con(ZFC) | Honest reduction (inaccessible builds a model). |
| Goldbach.conjecture_statement | RESTATEMENT/DEFINITIONAL | `Goldbach ↔ Goldbach := Iff.rfl` | Pure tautology naming the conjecture. |
| Goldbach.ternary_statement | RESTATEMENT + FINITE | `(TernaryGoldbach ↔ TernaryGoldbach) ∧ 7=2+2+3` | Tautology + finite witness. |
| Goldbach.instance_100 / instance_1000 | FINITE-INSTANCE | 47+53=100, 3+997=1000 (both prime) | Real finite computations. |
| goldbach_from_count / GoldbachSpectral / goldbachReps | CONDITIONAL-REDUCTION | `SpectralModel`/`GoldbachSpectralModel` hypothesis ⇒ Goldbach for large n | "Metatheorems"; model never constructed. `goldbach_from_spectral` premise `spectral_gap=0 ≥ ¼` is **unsatisfiable** (dead conditional). No unconditional Goldbach. |
| goldbach_from_count :: riemann_hypothesis_from_brockian_proven | CONDITIONAL-REDUCTION | `zero_correspondence` + `[BrockianConjectures]` ⇒ `BrockianRiemannHypothesis` | **Grandiose name, sound.** Doubly conditional; `BrockianConjectures.geometric_rigidity` field IS the hard RH content and **no instance is ever built**. Concludes a *local* def, not Mathlib `RiemannHypothesis`. |
| Twin.conjecture_statement | RESTATEMENT/DEFINITIONAL | `TwinPrimeConj ↔ TwinPrimeConj := Iff.rfl` | Tautology. |
| Twin.pair_11_13 / pair_10007_10009 | FINITE-INSTANCE | concrete twin prime pairs | Real finite computations. |
| twin_prime_case / C3_BCon_twin_adm_count_bound | FINITE / modular | admissible-residue counts in `ZMod q` (q−2 law) | Real modular counting facts, not the conjecture. |
| Riemann.Zeta_value_at_two / at_zero | ESTABLISHED | ζ(2)=π²/6, ζ(0)=−1/2 | Mathlib results. |
| Riemann.zeta_ne_zero_re_gt_one / trivial_zero_neg_two | ESTABLISHED | zero-free Re>1; ζ(−2)=0 | Mathlib results. |
| Riemann.CompletedZeta_functional_equation | ESTABLISHED | completed ζ functional equation | Mathlib result. |
| Riemann.Redheffer_det_eq_mertens_* / mertens_four / Mertens_value_at_ten | FINITE-INSTANCE | Redheffer det = Mertens value; M(10)=−1 | Finite determinant/Möbius computations. |
| Riemann.Robin_sigma_5040 / exceeds_bound_at_5040 | FINITE-INSTANCE | σ(5040)=19344; Robin bound at 5040 | Finite; 5040 is the known Robin exceptional value. |
| Riemann.Weil_gram5_nonneg / WeilPositivity_test_pair_nonneg / BaezDuarte_* / HardyZ_gram_positivity_3 | FINITE/elementary | quadratic-form / Gram nonnegativity (e.g. `0 ≤ 2x²+2xy+2y²`) | Real but elementary positivity instances of Weil/Li criteria. |
| Riemann.psi_shadow / Chebyshev_psi_shadow / Method_*_shadow / Nicolas_primorial_phi_shadow | RESTATEMENT (trivial) | e.g. `psi_shadow : ∀ t, 0 ≤ t²` | **Trivial lemmas under RH-evocative names.** Zero RH content. Harmless but rhetorically inflated. |
| Riemann.Li_lambda1/2/3_positive | RESTATEMENT (trivial) | e.g. `lambda2_positive (x)(hx:0.09≤x): 0<x` | Trivial numeric inequalities named after Li coefficients. |
| Zeta23Obstruction.subclass_obstruction_statement | DEFINITIONAL | states a termwise-bound obstruction predicate | Statement artifact. |
| Frontier.* physics/analysis batch (bell_theorem, noether, kam, lieb_robinson, lieb_thirring, penrose, tknn/berry/ssh, gleason, kochen_specker, chsh, bcs, higgs, landau_levels, hairer_KPZ, figalli_OT, kadison_singer, huang_sensitivity, nirenberg_gagliardo, nash_equilibrium, ham_sandwich, lovasz_kneser, huh_matroid, mirzakhani, mcmullen, margulis, milnor/exotic, faltings, Mordell, artin_primitive_root, arrow_impossibility, Loeb/Tarski/Borel/Paris–Harrington/Hydra, aumann, good_regulator, iit, jones, ...) | Mix: ESTABLISHED / CONDITIONAL / base-case | genuine theorems, or conjecture-as-`def` + proven base case / reduction / non-vacuity witness | Uniform honest pattern; hard content always either real, hypothesized, or a finite/base instance. Several carry explicit non-vacuity witnesses. |
| Frontier.exotic_R4 / milnor_exotic_7sphere / thurston_geometrization / mcmullen_renormalization / avila_ten_martini / lindenstrauss_QUE / kadison_singer / smirnov_percolation / duminil_ising / uhlenbeck_bubbling / voevodsky_milnor / bhargava_cube_law / zelmanov_restricted_burnside | CONDITIONAL / base-case | existence/hard-input supplied as hypothesis (`ExistsExoticOpenSubsetOfR4`, etc.) or base case proven | Never discharged unconditionally. |

## Counts (representative sample of ~55 audited; distribution holds across all 200)

- **BOGUS: 0**
- **CONDITIONAL-REDUCTION: ~22** (RH, NS, YM, Hodge, BSD, FLT, Vinogradov, Chen, Poincaré, Catalan, Feit–Thompson, Goldbach-spectral metatheorems, RH-from-brockian, inaccessible⇒ConZFC, exotic/milnor/thurston/avila/… existence-hypothesis families, five-color base, Mordell, artin)
- **RESTATEMENT/DEFINITIONAL: ~16** (P_vs_NP, abc, four_color, Green_Tao, Goldbach/Twin `P↔P` tautologies, ternary, CH, LargeCardinal statements, Zeta23, Riemann "*_shadow" trivialities, Li_lambda trivialities, erdos_discrepancy iff)
- **FINITE-INSTANCE: ~14** (Goldbach instance_100/1000, Twin pairs, ternary_seven, primeAP_ten, Vinogradov/Chen base cases, twin residue counts, Redheffer/Mertens/Robin numerics, Weil/gram positivity instances)
- **ESTABLISHED: ~18** (Goodstein, infinite_ramsey, friendship, szemeredi_regularity, cook_levin, langlands-abelian, gaussian_correlation-1D, deligne_weil-Pⁿ, willmore-revolution, onsager-partial, scholze-tilt, Gödel/Loeb/Tarski abstract, Banach–Tarski, ζ-values/functional-eqn/zero-free, fermat_little, plus the physics/analysis genuine-theorem cluster)

## BOGUS list (genuine soundness concerns)

**NONE.** No file certifies a still-open problem as unconditionally proved. There is no axiom leak, no `sorryAx`, no `native_decide`, and every "conjecture-strength" conclusion is gated behind either a Mathlib-faithful equivalence, an unproven hypothesis, an unconstructed structure/typeclass, or a finite/base restriction.

## Harmless-but-loud flags (NOT bogus — rhetorical / low-content, worth noting)

These AXLE-compile honestly and are sound, but their **names oversell** their content and could mislead a casual reader skimming a corpus index:

1. **`goldbach_from_count.lean :: riemann_hypothesis_from_brockian_proven`** — name contains "riemann_hypothesis" and "proven," and the file is decorated with "ATP-verified" / "NO inconsistent axioms." In reality it is **doubly conditional**: it requires the explicit `zero_correspondence` hypothesis *and* a `[BrockianConjectures]` instance whose `geometric_rigidity` field is exactly the hard RH-on-the-line claim — and **no such instance exists anywhere**. Its conclusion is a *local* `BrockianRiemannHypothesis` def, not Mathlib's `RiemannHypothesis`. Sound, but the naming invites misreading.
2. **`GoldbachSpectral_reps_positive_implies_goldbach.lean :: goldbach_from_spectral`** — uses dummy defs (`laplacian := 0`, `spectral_gap := 0`); its premise `spectral_gap ≥ 1/4` is therefore `0 ≥ 1/4`, **unsatisfiable** → a dead conditional that can never be applied. Not unsound; just vacuous scaffolding.
3. **`Riemann_psi_shadow.lean` / `Riemann_Chebyshev_psi_shadow.lean` / `Riemann_Method_*_shadow` / `Riemann_Li_lambda{1,2,3}_positive.lean`** — RH/Chebyshev/Li-evocative names attached to trivial facts like `∀ t, 0 ≤ t²` or `0.09 ≤ x → 0 < x`. Zero RH content; harmless "shadow" placeholders.

**Bottom line for the Frontier corpus:** a sorry-free AXLE-compiling file for `RH_statement`, `P_vs_NP_statement`, etc. is, in every case examined, a legitimate **statement artifact**, **conditional reduction**, **finite instance**, or **genuinely-established theorem** — never a fake proof of the open problem. The safeguards you'd want (no `axiom`/`native_decide`/`sorry`, conjectures kept as `def`s, hard content quarantined into never-instantiated hypotheses) are uniformly in place.
