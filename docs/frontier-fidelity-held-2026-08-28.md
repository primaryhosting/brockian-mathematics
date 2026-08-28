# Frontier fidelity triage — held-out (NOT attested)

AXLE-verified but statement does not faithfully match the target name. Excluded from
the registry to prevent overclaiming. WEAK = proves a real but weaker/conditional result
(often assumes the open conjecture as a hypothesis); VACUOUS = mislabeled or trivially true.
Reviewed 2026-08-28 by a 4-agent adversarial fidelity swarm.

## VACUOUS — `Frontier.Brun_twin_reciprocal`
- signature: `(no theorem named Brun_twin_reciprocal; file contains only namespace Brun with lemma bonferroni etc.)`
- The certificate file contains NO theorem matching the target tail and nothing about twin primes or convergence of their reciprocal sum (Brun's theorem). It only proves the Bonferroni / truncated inclusion-exclusion inequality — a generic combinatorial sieve lemma utterly unrelated to and vastly weaker than the named claim. Attesting this as 'Brun_twin_reciprocal' would be a strawman mislabel.

## VACUOUS — `Frontier.Spectral.cycle_fiedler_value`
- signature: `(file contains only a 25-line import/set_option header; NO def/lemma/theorem named cycle_fiedler_value exists)`
- The certificate file Frontier_Spectral_cycle_fiedler_value.lean has zero declarations — it is 25 lines of `import Mathlib` plus set_options, grep for theorem/lemma/def/example finds NONE. There is no formal statement matching the target tail at all, so nothing can be attested. Do NOT promote.

## VACUOUS — `Frontier.inaccessible_implies_ConZFC`
- signature: `NO THEOREM of this name exists; file ends after auxiliary lemmas (Vh, mem_Vh, card_Vh_lt, card_lt_of_rank_lt, rank_range_lt) at 'end Frontier'`
- The certificate file contains NO theorem matching the target tail. It only proves that levels V_o of the cumulative hierarchy are small below an inaccessible cardinal. The model VSet, the first-order theory ZFC, and the Con(ZFC)/satisfiability conclusion promised in the file's own overview docstring are never defined or proved. The named result is entirely absent.

## VACUOUS — `Frontier.kochen_specker`
- signature: `(none — file contains only `import Mathlib` and set_option lines; no namespace, no definitions, no theorem)`
- The certificate file is effectively EMPTY: it has imports and pp/heartbeat set_options only, with no theorem, no definitions, and not even a `namespace Frontier`. There is no Frontier.kochen_specker anywhere. Nothing is stated or proved; the Kochen–Specker theorem is entirely absent.

## VACUOUS — `Frontier.refl`
- signature: `lemma Pref.refl' (x : A) : r.pref x x`
- No declaration named Frontier.refl exists; the only match is the nested helper Frontier.Pref.refl', a one-line triviality (reflexivity of a total preorder, r.pref x x obtained immediately from the totality axiom on (x,x)). This is rfl-level content carrying no frontier significance — it is an auxiliary lemma extracted from the Arrow-impossibility file. Not safe to attest as a Frontier result.

## VACUOUS — `Frontier.rel_irrefl`
- signature: `lemma Ranking.rel_irrefl (R : Ranking A) (x : A) : ¬ R.rel x x`
- The matching declaration is Frontier.Ranking.rel_irrefl, a one-line triviality (irreflexivity of a strict order, proof `fun h => R.rel_asymm h h`). rfl-level content, a trivial helper in the Arrow-impossibility file; the actual Arrow theorem is a separate declaration. Not a frontier result.

## VACUOUS — `Frontier.sshBloch_eq_circleMap`
- signature: `lemma sshBloch_eq_circleMap (v w : ℝ) : sshBloch v w = circleMap (v:ℂ) w`
- A definitional identity closed by `simp`: sshBloch v w k = v + w·exp(k·I) is by definition circleMap (v) w k. rfl-level unfolding, a trivial helper for the SSH winding computation. Carries no independent content; not a frontier result.

## VACUOUS — `Frontier.tknn_chern_hall`
- signature: `(no declaration present)`
- Frontier_tknn_chern_hall.lean contains only `import Mathlib`, open/set_option preamble, and NOTHING else — no namespace, no def, no theorem named tknn_chern_hall. There is no statement to capture the TKNN/Chern–Hall-conductance claim; nothing is proved. A verified:true certificate on an empty file is an integrity failure. Cannot be attested.

## WEAK — `Frontier.BSD_statement`
- signature: `theorem BSD_statement (hBSD:BSD_conjecture)(E)(hΔ)(hmin)(L)(hL): L 1 ≠ 0 ↔ mordellWeilRank E = 0`
- Does NOT prove BSD. It ASSUMES the full Birch–Swinnerton-Dyer conjecture (hBSD:BSD_conjecture) as a hypothesis and derives the trivial rank-zero corollary. The supporting definitions (L-series, rank) are faithful, but the named theorem is a conditional corollary of the entire open conjecture, not the conjecture itself — the name overclaims.

## WEAK — `Frontier.Borel_determinacy`
- signature: `theorem Borel_determinacy [..][Inhabited A](hUnravel:UnravelsBorel A)(S)(hS:MeasurableSet(borel) S): Determined S`
- Assumes Martin's unravelling lemma (hUnravel:UnravelsBorel A) as a hypothesis — the docstring itself calls this 'the deep combinatorial content of Martin's theorem.' Only the base case (open/clopen determinacy) and transfer along coverings are actually proved; the hard content is quantified away into the hypothesis. Honest reduction, but not a proof of Borel determinacy.

## WEAK — `Frontier.CH_independent_statement`
- signature: `theorem CH_independent_statement: (ℵ₁≤𝔠) ∧ (CH↔¬∃c,ℵ₀<c<𝔠) ∧ (CH↔∀s:Set ℝ,s.Countable∨#s=𝔠) ∧ (¬CH↔ℵ₁<𝔠)`
- Despite the name, this does NOT prove CH's independence from ZFC (the docstring openly admits independence is metamathematical and cannot be a Lean theorem about Cardinal). It proves only the ZFC-provable base case ℵ₁≤𝔠 plus three genuine reformulations of CH. Real content, but far weaker than the named independence result.

## WEAK — `Frontier.Catalan_Mihailescu`
- signature: `theorem Catalan_Mihailescu: CatalanMihailescu ↔ CatalanMihailescuReduced`
- Proves an equivalence between the full Catalan–Mihailescu statement and a reduced non-existence statement (distinct prime exponents, ≠(3,2) cases), NOT the theorem itself. Genuinely proved special cases (Lebesgue exponent-3 via Gaussian integers, equal exponents, Levi ben Gerson) power the reduction, but neither side of the iff is discharged — Catalan's conjecture is not proved. Name overclaims.

## WEAK — `Frontier.FLT_statement`
- signature: `theorem FLT_statement: (∀ p, p.Prime → 5≤p → FLTFor p) ↔ FLT`
- Does NOT prove Fermat's Last Theorem. It proves the reduction/equivalence that FLT for all n>2 holds iff it holds for prime exponents p≥5, using the base cases n=3,4 from Mathlib. FLTFor/FLT are faithful definitions, but the named theorem only establishes the reduction, not FLT.

## WEAK — `Frontier.Green_Tao`
- signature: `theorem Green_Tao (hErdos:ErdosAPConjecture)(k:ℕ): HasAPOfLength {p|Nat.Prime p} k`
- Does NOT prove Green–Tao. It assumes the Erdős conjecture on arithmetic progressions (ErdosAPConjecture) — a strictly stronger, still-open statement — and combines it with Mathlib's divergence of prime reciprocals. Only unconditional base cases k≤10 are actually proved. Honest conditional reduction, but the name asserts the unconditional theorem.

## WEAK — `Frontier.Mordell_finite_generation`
- signature: `theorem Mordell_finite_generation (W)[W.IsElliptic](D:DescentData W.toAffine.Point): AddGroup.FG W.toAffine.Point`
- Does NOT prove Mordell's theorem. It assumes DescentData as a hypothesis — the docstring states this packages the weak Mordell–Weil theorem (finiteness of E(ℚ)/2E(ℚ)) plus the Northcott property and height-descent inequality, i.e. the two hard inputs. Only the infinite-descent step (fg_of_descentData) is actually proved. Honest reduction with a ℤ non-vacuity witness, but the substantive content is assumed.

## WEAK — `Frontier.P_vs_NP_statement`
- signature: `theorem P_vs_NP_statement: P ≠ NP ↔ ∃ L:Language, L∈NP ∧ L∉P`
- Does NOT resolve P vs NP (docstring: truth value 'open'). The P/NP Turing-machine definitions are faithful, but the named theorem is only the near-tautological characterization P≠NP ↔ ∃ separating language, which follows immediately from the proved inclusion P⊆NP. A trivial equivalence, not the frontier result the name evokes.

## WEAK — `Frontier.RH_Li_criterion`
- signature: `theorem RH_Li_criterion {ι}[Fintype ι](ρ:ι→ℂ)(h0:∀i,ρ i≠0)(hsymm:∀i,∃j,ρ j=1-ρ i): (∀i,(ρ i).re=1/2) ↔ ∀n≥1,0≤liCoeff ρ n`
- Proves only the finite-family function-theoretic core of Li's criterion for an ARBITRARY finite ρ:ι→ℂ symmetric under ρ↦1-ρ, not the actual criterion for the Riemann zeta zeros. The docstring concedes the arithmetic input (Hadamard factorisation identifying λ_n with a sum over zeros) is unavailable. Genuine (both directions, real Bombieri–Lagarias-style argument) but a strictly weaker finite analogue divorced from ζ; the name evokes the RH-equivalent criterion.

## WEAK — `Frontier.RH_statement`
- signature: `theorem RH_statement: RiemannHypothesis ↔ ∀ s:ℂ, 1/2<s.re → s.re<1 → riemannZeta s ≠ 0`
- Does NOT prove RH. It proves the (real, unconditional) equivalence between Mathlib's RiemannHypothesis and the a-priori-weaker 'no ζ-zeros in the open right half 1/2<Re<1 of the critical strip', using the zero-free region Re≥1 and functional-equation reflection. A genuine reduction/reformulation of RH — both sides remain open — but the name suggests the RH result itself.

## WEAK — `Frontier.Spectral.gap_to_cancellation_conditional`
- signature: `theorem gap_to_cancellation_conditional (P self-adj idem)(‖u‖=1)(hδ:0<δ)(hS:S=⟪u,Pu⟫)(hcontr:‖Pu‖≤1-δ) : |S| ≤ 1-δ`
- Pure Cauchy–Schwarz: |⟪u,Pu⟫| ≤ ‖u‖‖Pu‖ ≤ 1-δ. The load-bearing cancellation bound ‖Pu‖≤1-δ is ASSUMED (hcontr), and the spectral-gap positivity hδ plus self-adjointness/idempotence are entirely unused. So it does not derive cancellation FROM a gap; the name's implication (gap ⟹ cancellation) is not established — the contraction is handed in. Honestly labelled 'conditional' but overclaims 'gap_to_cancellation'.

## WEAK — `Frontier.Suslin_line`
- signature: `theorem Suslin_line : (separable⟹ccc) ∧ (SuslinLine⟹Uncountable) ∧ ¬IsSuslinLine ℝ ∧ (SuslinHypothesis ↔ (every ccc linear continuum is separable))`
- Suslin's problem is independent of ZFC and (correctly) not resolved. What is proved is a bundle of easy ZFC-provable peripheral facts; the 4th conjunct (suslinHypothesis_iff) is essentially a definitional unfolding of SuslinHypothesis. Genuine but far weaker than the name suggests; the definitions (HasCCC, IsLinearContinuum, IsSuslinLine) are faithful, so not vacuous.

## WEAK — `Frontier.abc_statement`
- signature: `theorem abc_statement : abcConjecture ↔ (∀ε>0, ∃C, ∀ t∈abcExceptional ε, c ≤ C)`
- Definitions of rad, abcExceptional and abcConjecture are faithful, but the proved content is only the trivial equivalence 'finitely many exceptional triples ↔ c is bounded on them' (immediate since a,b<c). The abc conjecture itself is not proved. Name 'abc_statement' delivers a faithful statement + easy reduction, not the theorem.

## WEAK — `Frontier.arrow_impossibility`
- signature: `theorem arrow_impossibility : ¬∃ F:(Fin 2→Ranking)→Ranking, Unanimous F ∧ IIA F ∧ ∀ d:Fin 2, ¬IsDictator F d   [Ranking = strict order on Fin 3]`
- Proves Arrow's theorem only for the fixed smallest instance: exactly 2 voters and exactly 3 alternatives. Definitions (Unanimous/IIA/IsDictator) are correct and a dictatorship_spec sanity-check rules out vacuity, but the general Arrow theorem (arbitrary finite voters/≥3 alternatives) is not established. Honestly labelled 'base case'; name overclaims.

## WEAK — `Frontier.artin_primitive_root`
- signature: `theorem artin_primitive_root : (ArtinPrimitiveRootConjecture ↔ ArtinPrimitiveRootUnbounded) ∧ (IsPrimitiveRootMod 2 3 ∧ …2 5 ∧ …2 11 ∧ …2 13)`
- Artin's conjecture is stated faithfully but NOT proved: the theorem only proves a trivial infinitude↔unbounded reduction plus four finite base-case computations (2 is a primitive root mod 3,5,11,13). Far weaker than the named open conjecture.

## WEAK — `Frontier.atiyah_singer_index`
- signature: `theorem atiyah_singer_index (T:V→ₗ[K]W)[FiniteDim] : analyticIndex T = topologicalIndex K V W   [= dim ker T − dim coker T = dim V − dim W]`
- This is the zero-dimensional (point) base case, i.e. exactly the rank–nullity theorem, honestly stated as such in the docstring. The genuine Atiyah–Singer index theorem (elliptic pseudodifferential operators, Chern character, Todd class) is entirely absent. Two sides are independently defined so it is non-vacuous, but drastically weaker than the name.

## WEAK — `Frontier.bhargava_cube_law`
- signature: `theorem bhargava_cube_law : (∀ cube, disc Q₁ = disc Q₂ = disc Q₃) ∧ (concordant cube (0,A,1,0,C,-B,0,-m) slices to the classical triple, disc=B²-4ACm) ∧ (explicit bilinear Gauss-composition identity Q₁·Q₂ = Q₃-opposite)`
- All conjuncts are proved by `ring` as polynomial identities. The common-discriminant fact holds for all cubes, but the composition ('cube law') content is only the explicit concordant-form identity, not a class-group statement — 'Q₁Q₂Q₃=1 in the class group' is asserted only in prose. Honestly labelled base case; genuine Gauss-composition algebra but weaker than the full named law.

## WEAK — `Frontier.bounded_prime_gaps`
- signature: `theorem bounded_prime_gaps : (∃B, ∀N, ∃n≥N, primeGap n ≤ B) ↔ liminf (fun n => (primeGap n:ℕ∞)) atTop < ⊤`
- An UNCONDITIONAL, essentially trivial reformulation ('bounded infinitely often ↔ liminf finite'); the deep Zhang–Maynard content (that either side actually holds) is explicitly NOT proved (the docstring admits this). Definitions faithful, but the name overclaims a bounded-gaps theorem that isn't established.

## WEAK — `Frontier.cook_levin`
- signature: `theorem cook_levin : (∀ f:CNF, ∃ p, linear-size ∧ ∀a, evalProg p a = cnfEval a f) ∧ (∀ L (C:NPCert L), ∃ F, (L n x ↔ Satisfiable(F n x)) ∧ poly-size ∧ ≤3 literals/clause)`
- The Tseitin reduction and SAT∈NP checker are genuine and substantial, but the complexity model is nonstandard: 'NP' is modeled by non-uniform poly-SIZE straight-line-program verifiers (NPCert.prog is an arbitrary function n↦circuit, no uniformity), and the reduction F is only required to have poly-size OUTPUT — its poly-time computability is not asserted. So it does not establish classical (uniform, poly-time) NP-completeness of SAT. Correct combinatorial core, weaker-than-named model.

## WEAK — `Frontier.deligne_weil_RH`
- signature: `theorem deligne_weil_RH (q n:ℕ) : LefschetzTraceFormula (projSpacePointCount q n) n (projFrobEigenvalues q n) ∧ WeilRH q n (projFrobEigenvalues q n)`
- Only the projective-space base case is proved, with a hand-defined eigenvalue family (single eigenvalue q^i in degree 2i). WeilRH then reads ‖q^i‖ = q^(2i/2), which is trivially true; the deep content of Deligne's proof (étale cohomology, actual Frobenius eigenvalues, weight bounds) is entirely absent. Honestly labelled base case; name massively overclaims.

## WEAK — `Frontier.duminil_ising_sharp`
- signature: `theorem duminil_ising_sharp (M:IsingOrderParameter)(hne)(hbdd) : (∀β<βc, m β=0) ∧ (∀β>βc, 0<m β)   [βc:=sInf{β|0<m β}, M packages Monotone m ∧ nonneg]`
- 'Sharpness' here is an automatic property of ANY nonnegative monotone function: given m monotone and βc defined as inf of its positive set, m=0 below βc and >0 above is elementary real analysis. The genuine Duminil-Copin content (that the actual Ising magnetisation has this behaviour, incl. the hard subcritical decay) is axiomatized into the IsingOrderParameter structure. Real but trivial/definitional; name overclaims.

## WEAK — `Frontier.erdos_discrepancy`
- signature: `theorem erdos_discrepancy (f:ℕ→ℤ)(hf:PlusMinusOne f) : ∃ d n>0, 1 < |∑_{i∈Icc 1 n} f (i*d)|`
- Proves only the base case C=1 (every ±1 sequence has a homogeneous AP with discrepancy ≥2, using the first 12 terms), not the full Erdős discrepancy theorem (Tao), which is the ∀C statement ErdosDiscrepancyStatement — defined in the file but left unproved. Honestly labelled base case; name overclaims the full result.

## WEAK — `Frontier.exotic_R4`
- signature: `theorem exotic_R4 (h : SmallExoticR4Exists) : ExoticR4Exists`
- A conditional repackaging: it merely transports an assumed small exotic ℝ⁴ (an open subset of ℝ⁴ homeomorphic but not diffeomorphic to ℝ⁴) into an ExoticR4Exists witness. The hard Donaldson–Freedman existence is entirely the hypothesis; the theorem itself is essentially trivial. Definitions faithful, but the name suggests establishing exotic ℝ⁴, which it does not.

## WEAK — `Frontier.faltings_mordell`
- signature: `theorem faltings_mordell {n:ℕ}(hn:4∣n)(hn0:n≠0) : (fermatCurveRatPoints n).Finite   [{p:ℚ×ℚ | p.1^n+p.2^n=1}]`
- Only finiteness of rational points on the specific Fermat curves x^n+y^n=1 with 4|n, obtained from Mathlib's fermatLastTheoremFour (FLT forces a coordinate to vanish, giving points in {0,1,-1}²). This is a narrow degenerate family proved via FLT, not Faltings' general Mordell conjecture (all genus≥2 curves) nor by Faltings' method. Honestly labelled instance; name overclaims.

## WEAK — `Frontier.feit_thompson_odd_order`
- signature: `theorem feit_thompson_odd_order (hsimple : ∀ S [Group][Finite], IsSimpleGroup S → Odd(card S) → ∀ a b, a*b=b*a) (G)[Group][Finite](hodd:Odd(card G)) : IsSolvable G`
- Conditional reduction: the deep content of Feit–Thompson — that every finite simple group of odd order is abelian (equivalently cyclic of prime order) — is TAKEN AS THE HYPOTHESIS hsimple, and only the standard easy minimal-counterexample reduction to the simple case is proved. The hypothesis is as strong as the theorem, so nothing of the hard theorem is established.

## WEAK — `Frontier.five_color_theorem`
- signature: `theorem five_color_theorem {V}[Fintype V](G:SimpleGraph V)(hplanar:G.Planar)(hdeg:G.DegenerateLE 4) : G.Colorable 5`
- The planarity hypothesis hplanar is DEAD (unused); the proof is pure greedy colouring from the added 4-degeneracy hypothesis hdeg. So this is just '4-degenerate ⟹ 5-colourable', not the five colour theorem (every planar graph is 5-colourable); planar graphs are only guaranteed 5-degenerate, and supplying DegenerateLE 4 begs the question. Honestly labelled base case; name overclaims.

## WEAK — `Frontier.four_color_statement`
- signature: `theorem four_color_statement : FourColorFinite ↔ FourColorAll   [IsPlanar = no K5/K3,3 minor (Wagner)]`
- A genuine, non-trivial De Bruijn–Erdős compactness reduction showing the four-colour statement for all (incl. infinite) planar graphs is equivalent to the finite case — with faithful Wagner minor-free planarity (K5,K3,3 sanity checks included). But the Appel–Haken finite four-colour theorem is only the hypothesis FourColorFinite; the four colour theorem itself is not proved. Name 'four_color_statement' delivers a reduction, not the theorem.

## WEAK — `Frontier.furstenberg_szemeredi`
- signature: `theorem furstenberg_szemeredi (hSz : SzemerediFinitary) {A : Set ℕ} (hA : HasPositiveUpperDensity A) (k : ℕ) : ContainsAP A k`
- The theorem takes the finitary form of Szemerédi's theorem (`hSz : SzemerediFinitary`) as an explicit HYPOTHESIS and only derives the density→AP direction (the easy Furstenberg-correspondence packaging). The hard combinatorial content is assumed, not proved; only the k=2 case (containsAP_two) is unconditional. Name 'Furstenberg–Szemerédi' overclaims a conditional reduction.

## WEAK — `Frontier.gaussian_correlation`
- signature: `theorem gaussian_correlation : GaussianCorrelationHolds 1`
- Proves the Gaussian correlation inequality only in dimension n=1 (GaussianCorrelationHolds 1), where origin-symmetric convex sets are nested intervals so the intersection is trivially the smaller set. Royen's theorem is the all-dimensions statement; this is a trivial special case. Docstring admits 'base case n=1'.

## WEAK — `Frontier.gleason_theorem`
- signature: `theorem gleason_theorem (h3 : 3 ≤ finrank ℂ E) (hquad : ∀ ν : QuantumMeasure E, ∃ T, T.IsSymmetric ∧ ...) (μ : QuantumMeasure E) : ∃ ρ : DensityOperator E, ...`
- Takes the frame-function theorem (the analytic core of Gleason, valid for dim≥3) as hypothesis `hquad`. Only the elementary passage from a symmetric quadratic representation to a density operator (positivity + unit trace) is proved; the dimension hypothesis h3 is never used except to make hquad true. Conditional reduction, not Gleason's theorem.

## WEAK — `Frontier.global_workspace_fixpoint`
- signature: `theorem global_workspace_fixpoint (W : GlobalWorkspace α) : ∃ a, IsLeastFixedPoint W a  -- GlobalWorkspace = monotone bc : α→α on Fintype+Lattice+BoundedOrder`
- This is Knaster–Tarski least-fixed-point existence for a monotone map on a finite bounded lattice — correct but elementary. 'GlobalWorkspace' is defined as merely (monotone operator), a strawman that captures nothing of Global Workspace Theory (broadcast, ignition, coalitions). Genuine math but the frontier 'Mind' name is unearned.

## WEAK — `Frontier.good_regulator`
- signature: `theorem good_regulator [Nonempty R] (psi : R→S→Z) (rho : S→R) (z0 : Z) (hgood : IsGoodRegulator psi rho z0) (hsimple : SimplestRegulation psi z0) : IsModelOf psi rho`
- Deterministic base case of Conant–Ashby. SimplestRegulation forces at most one action per disturbance to hit z0, so rho is uniquely determined by the system column systemMap and IsModelOf holds almost tautologically. Not the information-theoretic (entropy) good-regulator theorem; docstring says 'deterministic base case'.

## WEAK — `Frontier.hodge_statement`
- signature: `theorem hodge_statement : ∀ {H}[...](X : HodgeVariety H), (∀p, alg p ≤ hodgeClasses X p) ∧ (contrapositive reformulation) ∧ (HodgeConjecture X ↔ ∀p, hodgeClasses ≤ alg) ∧ HodgeConjectureAt X 0 ∧ (∀p, piece p p = ⊥ → HodgeConjectureAt X p)`
- Definitions of Hodge structure/variety/conjecture look faithful, but the proved content is only: the always-true inclusion alg⊆hodgeClasses, tautological reformulations, the trivial p=0 base case, and the vanishing case H^{p,p}=0. The Hodge conjecture itself is not proved. Name (softened to 'statement') still packages a Moonshot from trivial reductions.

## WEAK — `Frontier.huh_matroid_log_concave`
- signature: `theorem huh_matroid_log_concave {ι}(E : Finset ι)(k : ℕ) : (charPoly(freeOn E).coeff k).natAbs * (coeff (k+2)).natAbs ≤ ((coeff (k+1)).natAbs)^2`
- Only the free (Boolean) matroid, where the characteristic polynomial is (X-1)^{|E|} and coefficient absolute values are binomial coefficients — log-concavity then reduces to the elementary binomial inequality. The Adiprasito–Huh–Katz theorem is for ALL matroids; this is the trivial base case (docstring admits it).

## WEAK — `Frontier.jones_polynomial_invariant`
- signature: `theorem jones_polynomial_invariant : ∀ d d' : BracketData, RMove d d' → jones d = jones d'  -- RMove encodes Reidemeister moves as relations on (writhe, bracket) pairs`
- Invariance is proved against an ABSTRACT encoding of Reidemeister moves on (writhe, bracket) pairs, not actual link diagrams (no links, crossings, or planar structure exist). R3 is literally reflexivity (RMove ⟨w,b⟩ ⟨w,b⟩) and R2 adds a term with proven-zero coefficient; only R1 (kink) normalization has real content. 'Jones polynomial is a link invariant' overclaims — there are no links.

## WEAK — `Frontier.kadison_singer`
- signature: `theorem kadison_singer : (∀ α d, WeaverKS 1 α d) ∧ (∀ r α, 0<r → 0≤α → WeaverKS r α 1)`
- Proves only the two boundary cases of Weaver's KS_r conjecture: r=1 (one part, trivial) and dimension d=1 (a greedy load-balancing bound). The full statement ∀ r α d WeaverKS r α d (the Marcus–Spielman–Srivastava theorem) is not proved. Docstring admits these are 'the two boundary cases of the induction'.

## WEAK — `Frontier.kam_theorem`
- signature: `theorem kam_theorem (param dyn rot)(Φ : E→E)(K : ℝ≥0)(hK : ContractingWith K Φ)(hfix : ∀u, Φ u = u ↔ IsInvariantTorus ... u)(u₀)(ε)(hε : dist u₀ (Φ u₀) ≤ ε) : ∃ u, IsInvariantTorus ... ∧ dist u₀ u ≤ ε/(1-K) ∧ unique`
- This is Banach's fixed-point theorem in disguise: it ASSUMES an operator Φ whose fixed points are exactly invariant tori (hfix) and that is already a contraction (hK). The entire KAM content — the Newton scheme, small-divisor estimates producing such a Φ — is hypothesized. The satisfiability witness is a trivial map u↦u/2, not a genuine KAM setting. Conditional reduction.

## WEAK — `Frontier.lindenstrauss_QUE`
- signature: `theorem lindenstrauss_QUE (vol)[IsProbabilityMeasure vol](phi : ℕ→C(X,ℝ))(hnorm)(hQL : ∀ subseq, every weak-* limit ν = vol) : ∀ g, Tendsto (∫ g·|phi n|² dvol) atTop (𝓝 (∫ g dvol))`
- Takes hQL — 'every subsequential weak-* limit of the microlocal lifts equals volume', which the docstring itself calls 'exactly the classification of quantum limits which is the content of Lindenstrauss' theorem' — as a HYPOTHESIS. Only the elementary weak-* compactness step (subsequences ⇒ full sequence) is proved. Arithmetic QUE is assumed, not proved.

## WEAK — `Frontier.mcmullen_renormalization`
- signature: `theorem mcmullen_renormalization : (∀Q, connected filledJulia → IsRenormalizationOf Q Q 1 ∧ Renormalizable Q 1) ∧ (∀Q R p q, IsRenormalizationOf R Q p → Renormalizable R q → Renormalizable Q (p*q)) ∧ (∀Q, MapsTo Q.f (filledJulia Q) (filledJulia Q))`
- Only bookkeeping is proved: the period-1 base case is trivial (a map with connected Julia set is its own renormalization) and multiplicativity of periods is just Function.iterate_mul. None of McMullen's analytic content (renormalization convergence, universality, complex bounds) appears. Name massively overclaims a trivial framework.

## WEAK — `Frontier.milnor_exotic_7sphere`
- signature: `theorem milnor_exotic_7sphere (M : ℤ→ℤ→Type)[...](lam)(hlam : ∀h l, h+l=1 → lam h l = milnorLambda h l)(hhomeo : ∀h l, h+l=1 → Nonempty (M h l ≃ₜ S⁷))(hinv : ∀h l, h+l=1 → Nonempty(Diffeomorph ...) → lam h l = 0) : ExoticSphereExists`
- Conditional reduction: the total spaces M h l, their homeomorphism to S⁷ (hhomeo), the λ-invariant computation via Hirzebruch signature (hlam), and diffeomorphism-invariance of λ (hinv) are all ASSUMED as hypotheses. Only a trivial mod-7 arithmetic fact (milnorLambda 2 (-1) ≠ 0) is genuinely proved. The geometric substance of Milnor's theorem is hypothesized.

## WEAK — `Frontier.navier_stokes_regularity`
- signature: `theorem navier_stokes_regularity (ν : ℝ)(a : ℝ→Vec)(ha : ContDiff ℝ ∞ a) : ∃ u p, IsGlobalSmoothSolution ν u p ∧ ∀x, u 0 x = a 0`
- Proves only the spatially-uniform special case u(t,x)=a(t), p(t,x)=-⟨a'(t),x⟩ — essentially an ODE where the nonlinear and viscous terms vanish identically. This is NOT NavierStokesGlobalRegularity ν (the actual def, requiring solutions for all smooth divergence-free initial data). Docstring admits 'restricted to spatially uniform initial data'; the Millennium problem is not addressed.

## WEAK — `Frontier.onsager_2d_ising`
- signature: `theorem onsager_2d_ising : (∀m n β J,0<Z m n β J)∧(∀m n J,0<m→0<n→freeEnergyDensity m n 0 J=onsagerFree 0 J)∧(∀m n J,Z m n 0 J=2^(m*n))∧(∀β J,Z 2 2 β J=12+4*cosh(8βJ))∧(∀β J,0<J→(sinh(2βJ)=1↔β=log(1+√2)/(2J)))`
- Does NOT prove Onsager's solution. The headline claim — free energy per site converges to onsagerFree in the thermodynamic limit for all β — is absent. What is proved is a conjunction of easy facts: partition-function positivity, the β=0 base case (both sides trivially log 2), the β=0 count 2^(mn), an exact 2×2-torus evaluation, and the critical-point identity sinh(2βJ)=1 ↔ β=log(1+√2)/(2J). onsagerFree is merely posited, never equated to the limit. Name overclaims.

## WEAK — `Frontier.penrose_singularity`
- signature: `theorem penrose_singularity {θ θ':ℝ→ℝ}(hderiv: ∀s∈Ici 0, HasDerivAt θ (θ' s) s)(hnec: ∀s∈Ici 0, θ' s ≤ -(θ s)^2/2)(htrapped: θ 0<0): False`
- Only the analytic focusing lemma is formalized: a scalar function on [0,∞) satisfying the Raychaudhuri-NEC inequality θ'≤-θ²/2 with θ0<0 cannot exist (focusing within affine length 2/|θ0|, shown sharp). No spacetime, geodesic, trapped surface, global hyperbolicity, or non-compact Cauchy surface appears — the docstring admits the global causal-topology step is not formalized. Genuine, non-vacuous base case, but the name claims the full singularity theorem.

## WEAK — `Frontier.poincare_3sphere`
- signature: `theorem poincare_3sphere : PoincareConjecture3 ↔ PoincareBijectionForm`
- Proves only an equivalence between the Poincaré conjecture and its 'continuous bijection' variant; it does NOT prove the conjecture. The nontrivial direction is the elementary fact that a continuous bijection from a compact space to a Hausdorff space is a homeomorphism (Continuous.homeoOfEquivCompactToT2). Both sides of the iff remain open. The name strongly implies the conjecture itself is established; the delivered content is a trivial topological reduction.

## WEAK — `Frontier.smirnov_percolation`
- signature: `theorem smirnov_percolation (P:CrossingProbability)(Cardy:ℂ→ℝ)(hCardy: ∀D z₁ z₂ z₃ z₄, P D z₁ z₂ z₃ z₄ = Cardy (crossRatio z₁ z₂ z₃ z₄)): ConformallyInvariant P`
- The hard analytic content of Smirnov/Cardy (existence of the scaling limit and that it equals Cardy's formula) is assumed via hCardy, which posits P is a function of the cross-ratio alone. Given that, conformal invariance is immediate from Möbius-invariance of the cross-ratio (crossRatio_mobius). The docstring admits the scaling-limit analysis is beyond Mathlib. A near-tautological reduction that quantifies away the crux; the name claims a Fields-Medal theorem.

## WEAK — `Frontier.spin_statistics`
- signature: `theorem spin_statistics (F:WightmanField T H)(s:ℕ)(ε:ℤ)(hε:ε=1∨ε=-1)(hwrong:ε≠exchangePhase s)(hW: ∀f, ⟪Ω,φ(f)φ*(f)Ω⟫ = (ε*(-1)^s)*⟪Ω,φ*(f)φ(f)Ω⟫): ∀f, F.field f Ω=0 ∧ F.fieldStar f Ω=0`
- Only the Pauli positivity endgame is formalized. The genuinely hard input — the two-point-function sign relation hW produced by Lorentz covariance + locality + edge-of-the-wedge analytic continuation — is taken as a hypothesis (docstring admits this). Given hW with the wrong sign, positivity forces ‖φΩ‖²=-‖φ*Ω‖², hence both vanish. Correct and non-vacuous, but assumes the physics; the name claims the full spin-statistics theorem.

## WEAK — `Frontier.thurston_geometrization`
- signature: `theorem thurston_geometrization (T:ThreeManifoldTheory)(hprime:T.PrimeDecompositionAxiom)(hjsj:T.JSJAxiom)(hgeo:T.PiecesAreGeometricAxiom): T.Geometrization`
- An abstract-interface reduction: 'manifolds' are an arbitrary type Mfld with arbitrary predicates (IsPrime, TorusDecomp, Geometric, ...) and no actual 3-manifold topology. All deep inputs (Kneser–Milnor, JSJ, Thurston–Perelman) are supplied as hypotheses, and the proof is a trivial chaining of them. The eight-geometry inductive is genuine, but the geometrization conclusion carries no real geometric content — it holds for the toy model of the 8 geometries. Name claims a Fields-Medal theorem; delivers a tautological reduction over a strawman interface.

## WEAK — `Frontier.willmore_conjecture`
- signature: `theorem willmore_conjecture : MinimizedByClifford revolutionTori ∧ ∀R r,0<r→r<R→(willmoreEnergyTorus R r=2π² ↔ R=√2*r)`
- Proves only the classical base case for tori of REVOLUTION, and even there the Willmore energy is DEFINED by the closed formula π²R²/(r√(R²-r²)) rather than derived from a mean-curvature integral. The AM–GM minimization giving ≥2π² with equality at the Clifford ratio R=√2 r is genuine, but MinimizedByClifford ranges only over the 2-parameter revolution family (with genusOne := True, a strawman predicate). The full Marques–Neves theorem over all genus-one surfaces is not proved. Name overclaims.

## WEAK — `Frontier.yang_mills_mass_gap`
- signature: `theorem yang_mills_mass_gap (IsQuantumYangMills:YangMillsTheory→Prop)(hex:IsolatedVacuumStatement IsQuantumYangMills): MassGapStatement IsQuantumYangMills`
- A reduction: the real content is the spectral equivalence hasMassGap_iff_vacuumIsolated (mass gap ⟺ vacuum energy is isolated in the spectrum), which is correct. The theorem then trivially transfers: IF a Yang–Mills theory with isolated vacuum exists (hypothesis hex), it has a mass gap. The dynamical Yang–Mills content is an arbitrary predicate IsQuantumYangMills and unconditional existence is assumed (docstring admits it 'remains open'). Name claims the Millennium problem; delivers an assumed-hypothesis reduction.

## WEAK — `Frontier.zelmanov_restricted_burnside`
- signature: `theorem zelmanov_restricted_burnside (d:ℕ): RestrictedBurnsideBounded d 2`
- RestrictedBurnsideBounded d n is defined faithfully (uniform bound on the order of finite d-generated groups of exponent n). But the theorem proves only the exponent n=2 case: exponent-2 groups are elementary abelian of rank ≤d, so |G|≤2^d. This is the trivial classical base case; Zelmanov's Fields-Medal theorem is ∀ d n, n>0 → RestrictedBurnsideBounded d n. Genuine but a strict special case — the name claims the full theorem.

## Bare-name files excluded (grandiose placeholder sibling decls)

These target theorems are FAITHFUL, but their source files also contain an unregistered
grandiose/placeholder decl (e.g. RH_of_BrockianSystem with a placeholder field). Held for
manual review to avoid importing the placeholder sibling into the corpus.

- `D5_card_verified`
- `IntMagma_op`
- `bridge`

## Repair-campaign edits held for review (2026-08-28)

The type-mismatch repair lane produced these edits that EXCEED mechanical scope or are Frontier claims.
They compile but are NOT attested — a repair that reformalizes a statement needs fidelity review.

Oversized Brockian rewrites (committed d863e2bd, not attested):
- `Brockian.DilationGenerator.symmetric_on_core` (188-line change)
- `Brockian.DilationGenerator.conjugation_to_momentum` (72-line change)
- `Brockian.GoldbachWheelK2_727` (127-line change)

Frontier repairs (need fidelity triage before any attestation):
- `Frontier.avila_ten_martini` (318-line reformalization L2Z->HilbertZ — heavy rewrite of a Ten Martini claim)
- `Frontier.hairer_KPZ`, `Frontier.Spectral.quantified`, `Frontier.berry_phase_quantized`, `Frontier.clm_prod_apply`
