
## Wave 19 (2026-08-27)
- AXLE cloud check (scripts/axle_client.py) + gen_registry.py is the full sanctioned
  registration path; local lake never needed. AXLE verifies a module in ~2s.
- STANDING RULE: every wave's run script must git commit+push (to its exp branch) all
  artifacts later waves depend on — AutoLab does not auto-commit run-time changes.
- Faithfulness compare: strip Aristotle prose from recorded goal text (cut at first
  ``` or 'Proof outline') before signature matching.
- aristotle submit takes the PROMPT as positional text (not a file); --project-dir
  is only for supporting files.
- lake exe cache get works bounded+streamed (8639/8639 oleans in ~600s).

## Wave 22 (2026-08-27)
- MONOTONIC REGISTRY GUARD: gen_registry output is reverted+aborted if the PROVED
  count would shrink. Root cause of the wave-21 regression: re-rendering the Lean
  file from tarballs dropped blocks whose pids weren't found. Standing rule now:
  the committed Lean file is the source of truth; only APPEND, never regenerate.
- zumkeller_mul_coprime registered from its own Context.lean statement (corpus-def
  match + AXLE axiom check as faithfulness basis; no prompt parsing).

## Wave 23 (2026-08-27)
- NEW Aristotle tarball layout: solution lives in RequestProject/*.lean (often
  Main.lean), not Context.lean — harvest must pick the .lean containing the
  target theorem. This caused wave-22's 'staged terminal -> None'.
- Aristotle may substitute its OWN definition of a concept (OddZumkellerFrom3Structure
  came back with a different-but-equivalent Zumkeller def): faithfulness gate must
  compare defs and route def-mismatch proofs to review/ for a bridge lemma.

## Wave 24 (2026-08-27)
- The 40 CONJECTURE registry entries are famous open problems (Twin Primes,
  Collatz, Legendre, Erdos-Straus, ...) and the 20 CONDITIONAL entries pend
  literature rungs: neither is prover-sized. Sustainable growth comes from
  targeting priority (3): NEW structural lemmas extending active clusters
  (aliquot/sigma: Weird, Quasiperfect, Superperfect, Hyperperfect, Zumkeller),
  each stated against corpus definitions extracted verbatim at generation time.
- Generator lives in scripts/autolab_wave24.py (TARGETS + build_prompt), output
  ranked in research/frontier_triage_v2.json with rationale per target; goals are
  recorded in the state file at submit time so faithfulness is checkable later.

## Wave 25 (2026-08-27)
- Harvest/registration is now generic over clusters: faithfulness keys off each
  target's OWN corpus definitions (recorded in the target spec at submit time),
  and non-Zumkeller cluster theorems land in Brockian.AliquotStructure
  (Brockian/AliquotStructure.lean) with every duplicated corpus def verified verbatim.
- Attestation hygiene: every requested declaration must appear in the AXLE report
  with axle_verdict=verified and axioms_ok; an EMPTY axiom list no longer passes
  silently (it is flagged with an explicit logged justification).
- Queue depth is the rate limiter (server searches take 1-4h): hold >= 8
  jobs in flight, ranked targets in research/frontier_triage_v3.json.

## Wave 26 (2026-08-27) — named-problem partials wing
- Tier A/B doctrine: the famous statement is an unproven `def` (metric 0); only tier-B partial theorems count. Modules created this wave: Brockian.LandauProblem.
- Tier-B goals submitted to Aristotle: 7. Registered this wave: hyperperfect_pos_of_hyperperfect, not_quasiperfect_prime, not_semiperfect_of_aliquot_lt, quasiperfect_isSquare_or_two_mul_square, semiperfect_mul_right, zumkeller_two_mul_of_odd_zumkeller.
- The vendored top-100 'brockian' module field is ASPIRATIONAL: most named modules do not exist and must be created; never cite a nonexistent module in the registry.
- Verification stays AXLE-first (cloud, ~2s) + gen_registry monotonic guard; `lake build Brockian.<M>` remains a trap on this node.

## Wave 27 (2026-08-27) — honest metric + governing queue
- METRIC FIX: wave 26 logged 66 by counting every PROVED entry in the wing modules, but those modules already held 48 pre-existing corpus theorems. The count is now an explicit ledger (research/our_theorems.json) cross-checked against the registry PROVED delta vs 11152; the smaller value is logged so an accounting bug can only under-report. Honest cumulative = 18.
- research/frontier_queue.json was absent from every branch, so it is bootstrapped here from in-tree artifacts and AWAITS HUMAN REVIEW of ranks/scores/tiers.
- HUMAN ASK: please re-export the vendored top-100 JSON with a corrected 'brockian' module field plus tier/feasibility columns — 5 of the 6 'missing' wing modules already existed in the tree, so the field cannot be trusted, and the vendored queue entries carry prose goals with no Lean signature (they cannot be submitted or faithfulness-screened as-is).
- Harvest is now module-generic, so named-problem wing goals can land. Registered this wave: none. Pending Aristotle jobs: 9.

## Wave 28 (2026-08-27) — atomic attestation + duplicate audit
- ATOMIC ATTESTATION: candidates are attested one at a time on top of the last known-good module source; a failure restores that snapshot in memory instead of `git checkout`, so one sorryAx proof can no longer abort a whole lane (wave 27 lost two clean Landau theorems that way).
- DUPLICATE AUDIT: wave 26 invented predicates for modules it believed were missing; 5 of its wing goals duplicate theorems the corpus already proves (covering_78557, eleven_dvd_of_palindrome_even_digits, erdosStraus_of_even, erdosStraus_of_mod_three_eq_two, squarefree_of_lehmerProperty). They are retired, not re-submitted — a re-proof of an existing corpus theorem counts for nothing.
- ALWAYS grep the tree for the def AND for an existing theorem with the same content before submitting; the vendored top-100 'brockian' field is unreliable.
- Registered this wave: even_of_sq_add_one_prime, odd_prime_dvd_sq_add_one_mod_four; dropped/retired: 7; ledger=20; pending=6.

## Wave 29 (2026-08-27) — governed harvest + queue-first submission
- QUEUE-FIRST: agent-generated targets now get an `open` frontier_queue entry (statement + rationale + tractability) appended BEFORE submission, so every Aristotle goal is governed and traceable.
- The two remaining tractability>=4 `open` entries duplicate existing corpus theorems (RepunitPrimes.prime_of_repunit_prime, SuperperfectNumbers.superperfect_two_pow_of_mersenne_prime); annotated, never submitted. Legal status transitions only — a duplicate is annotated, not 'refuted'.
- Wave-27's 'def-extractor' theory for the Erdos-Straus/Lehmer/Sierpinski/palindrome rejects was wrong: the wave-28 audit showed they duplicate corpus theorems. Do not retry them.
- Registered this wave: landau_iff_even_infinite, not_isSquare_sq_add_one, three_not_dvd_sq_add_one; dropped/retired: 2; ledger=23; pending=7.

## Wave 30 (2026-08-27) — parallel clusters + queue provenance
- PARALLELISE CLUSTERS: Aristotle searches take 1-4h, so a single cluster (Landau) left waves with nothing to harvest. Wave 30 opens FortunateNumbers and GiugaNumbers tier-B fronts as well (4 goals submitted); always check the module source AND the registry for the short name first — most 'missing' wing theorems turned out to be duplicates.
- GOVERNANCE BACKFILL: the queue must mirror the registry. 20 entries appended as `proved` (with evidence.attestation) and 0 legal status steps applied for theorems registered before the queue-first flow existed. Only open->assigned->in_progress->proved transitions, appended history, nothing rewritten.
- Registered this wave: coprime_sq_add_one, exists_prime_mod_four_dvd_sq_add_one, four_not_dvd_sq_add_one, landau_iff_unbounded; retired: 2; ledger=27; pending=7.

## Wave 32 (2026-08-27) — render auto-repair
- DE-DUPLICATION MUST BE GENERIC: stripping a corpus def pasted verbatim into an Aristotle prompt leaves its doc comment orphaned, and Lean then refuses the file ('unexpected token /--'). Strip the doc comment WITH the def for every def name, in every shape (indented, noncomputable, attribute-prefixed).
- REPAIR, DON'T REJECT: wave 31 threw away three faithfulness-passed proofs on this lint. The renderer now drops doc comments that no longer document a declaration and re-lints; rejection is the last resort.
- A safety check that caches state at startup can deadlock the wave it protects (wave 31's queue-first guard blocked its own freshly appended entries) — always re-read the governing file.
- Registered this wave: fortunateFor_coprime, fortunateFor_unique, giugaNumber_three_primes; retired: 2; ledger=30; pending=6.

## Wave 35 (2026-08-27) — Track-1 Fourier module landed on the reconciled lineage
- LINEAGE IS PART OF THE GATE: the same seven AXLE-verified CharactersQ declarations were unbankable on wave 34's trunk fork and bankable here, because registry-delta accounting only means anything on the branch that carries our registrations. Assert the lineage (registry PROVED >= baseline + ledger) before touching the registry.
- Registered this wave: additive_orthogonality, additive_orthogonality_sub, fourier_apply, fourier_inversion, fourier_twice, multiplicative_orthogonality, parseval, fortunateFor_not_dvd_base_prime, fortunateFor_odd_of_even_base, not_giugaNumber_prime_pow, gcd_sq_add_one_succ_dvd_five; retired 2; ledger=41; pending=4.
- Codex probe: path=/opt/homebrew/bin/codex; codex --help rc=0: Codex CLI | If no subcommand is specified, options will be forwarded to the interactive CLI. | Usage: codex [OPTIONS] [PROMPT] | codex [OPTIONS] <COMMAND> [ARGS] | Commands: | agents            Browse all agent sessions on the shared local app-server daemon | exec              Run Codex non-interact; codex exec --help rc=0: Run Codex non-interactively | Usage: codex exec [OPTIONS] [PROMPT] | codex exec [OPTIONS] <COMMAND> [ARGS] | Commands: | resume  Resume a previous session by id or pick the most recent with --last | fork    Fork a previous session by id into a new session | review  Run a code review against the curr

## Cross-wave insight backfill (recorded 2026-08-27, waves 11-35)

mechanics / verification
- NEVER compile Mathlib from source on this node; populate oleans with
  `lake exe cache get` against lake-manifest.json (waves 12-15 each burned ~55
  min on a `lake build` that never terminated).  confidence 0.95
- Verify single files with `lake env lean <file>`, bypassing lake build
  orchestration, when dependency oleans exist — this unjammed the pipeline at
  wave 22 after 15 failed waves.  confidence 0.95
- `missing_oleans=0` while lake still hangs means the hang is NOT missing
  modules: it is lock-wait, config-hash rebuild, or slow shared storage.
  Diagnose before retrying; wave 15 proved blind retries are worthless.  0.9
- Clear stale .lake locks and orphaned lean processes BEFORE any lake call; on
  budget expiry SIGTERM the process group, wait 30s, then SIGKILL.  Wave 14's
  bare SIGKILL orphaned children and poisoned later waves.  confidence 0.9
- `lake build Brockian.<Module>` never completes here (859-module workspace
  trace scan); only mathlib module targets and `lake env lean` ever compile.  0.9

integrity
- Trust ONLY the axiom check (#print axioms / AXLE per declaration), never a
  backend's prose summary: wave 11 caught `not_zumkeller_prime_pow` carrying
  sorryAx while Aristotle's summary claimed sorry-free.  confidence 1.0
- Atomic per-candidate attestation lets unclean candidates be retired without
  blocking clean siblings in the same batch (wave 28 onward).  confidence 0.9
- A backend sometimes DISPROVES a target (odd_zumkeller_div_three is false, and
  zumkeller_semiperfect fails at n=70): a disproof is a valuable artifact, the
  target must be retired, and it is never registered as PROVED.  confidence 0.9
- Record the exact submitted goal text verbatim at submit time; without it
  faithfulness screening is impossible and clean proofs strand in review/ (3
  proofs from wave 7).  confidence 0.95

metric / governance
- new_proved_theorems must be the registry delta cross-checked against the
  ledger (ledger == registry_proved - 11152); wave 26 logged 66 from a bad
  derivation, wave 27 re-derived it honestly as 18.  confidence 1.0
- Registry updates go only through scripts/gen_registry.py; CI diffs
  registry/theorems.json and fails on hand edits.  confidence 1.0
- Fork each wave from the PREVIOUS wave's branch, never main/trunk: wave 34
  forked the human trunk and its registry read came back 0, collapsing the delta
  derivation even though the proofs were fine.  confidence 0.95
- Queue-first: assert an 'open' frontier_queue.json entry exists BEFORE the
  submit call (gcd_sq_add_one_succ_dvd_five became an untracked provenance
  hole).  confidence 0.85

targeting
- Parallel independent clusters remove the per-wave latency floor: with 3+
  clusters in flight no single search gates the wave — the biggest throughput
  gain after the verification fix.  confidence 0.9
- The named-problem EASY tier is exhausted (Landau cheap results mined out;
  Erdos-Straus even / n=2 mod 3 came back as duplicates).  Only new infinite
  families, propagation lemmas or structural lower bounds count now.  0.85
- An 'already attempted' filter must not block a legitimate retry with a better
  prompt — use distinct theorem names for retries.  confidence 0.8

backend
- Codex's first contribution (CharactersQ.lean: general-q additive
  orthogonality, DFT-twice, inversion, Parseval, Dirichlet cancellation, all
  axiom-clean) suggests it is strongest on Mathlib-idiomatic API design and
  convention-fixing, complementing Aristotle's search strength.  Route
  analytic/API-design goals to Codex, finite/combinatorial to Aristotle, race
  when unsure.  confidence 0.6 (single data point)
- TOOLING GAP: no insight-store API is reachable from a wave script; these
  lessons live in research/insights.md and the node notes.  A human needs to
  expose a writer if the store is to be populated.  confidence 1.0

## Wave 37 (2026-08-27) — observatory exact certificates (operator job 20788714)
- EXACT-STATEMENT DISCIPLINE (tags: integrity, governance; confidence 0.9): the submitted statement is hashed at submit time (`state['stmt_hash']`) and the spliced statement is re-hashed before registration, so a returned proof of a *weakened* variant cannot be banked even if it is axiom-clean. This is the check that the faithfulness screen alone does not give for operator-specified targets, where the statement is fixed in advance.
- DEF EXTRACTION (tags: mechanics; confidence 0.85): the corpus `^def name` regexes silently miss `noncomputable def` (e.g. `RiemannScaffold.riemannXi`), which made analytic-module targets unsubmittable — the prompt would have described the definition instead of pasting it, exactly the failure that let Aristotle substitute its own `IsSierpinski`. Extractors now accept `noncomputable/private/protected def`.
- RESULT (tags: targeting, metric; confidence 0.8): registered this wave: firstNinePrimeOffsets_not_admissible; AXLE-verified exact targets: 1/3; ledger 42; pending 6. Submissions: firstNinePrimeOffsets_not_admissible: submitted pid=b143212e-46fe-4513-a62e-a3d9bf6dac09 attempt=1; zeta_zero_quartet_of_mem_critical_strip: submitted pid=01263913-13a9-4732-8010-7d2e5702bd96 attempt=1; riemannXi_criticalLine_even: submitted pid=3f0d51f9-aa31-4c15-87bf-a4e04a216c29 attempt=1.
- RH HYGIENE (tags: integrity; confidence 0.9): the ζ-zero quartet certificate asserts vanishing at four reflected points only. Any returned proof claiming distinctness of those points, a zero location, or RH itself is rejected outright — the certificate must stay unconditional and content-free about the hypothesis.

## Wave 37 (2026-08-27) — observatory exact certificates (operator job 20788714)
- EXACT-STATEMENT DISCIPLINE (tags: integrity, governance; confidence 0.9): the submitted statement is hashed at submit time (`state['stmt_hash']`) and the spliced statement is re-hashed before registration, so a returned proof of a *weakened* variant cannot be banked even if it is axiom-clean. This is the check that the faithfulness screen alone does not give for operator-specified targets, where the statement is fixed in advance.
- DEF EXTRACTION (tags: mechanics; confidence 0.85): the corpus `^def name` regexes silently miss `noncomputable def` (e.g. `RiemannScaffold.riemannXi`), which made analytic-module targets unsubmittable — the prompt would have described the definition instead of pasting it, exactly the failure that let Aristotle substitute its own `IsSierpinski`. Extractors now accept `noncomputable/private/protected def`.
- RESULT (tags: targeting, metric; confidence 0.8): registered this wave: none; AXLE-verified exact targets: 0/3; ledger 42; pending 9. Submissions: harmonicOscillatorPMap_essentiallySelfAdjoint: submitted pid=ddefbb0d-ff0d-4964-bee0-ddcfa1d001e4 attempt=1; harmonicOscillatorClosureResolvents_compact_target: submitted pid=bce1982f-401e-45c3-9acd-ffbc18c9c24e attempt=1.
- RH HYGIENE (tags: integrity; confidence 0.9): the ζ-zero quartet certificate asserts vanishing at four reflected points only. Any returned proof claiming distinctness of those points, a zero location, or RH itself is rejected outright — the certificate must stay unconditional and content-free about the hypothesis.

## Wave 37 (2026-08-27) — observatory exact certificates (operator job 20788714)
- EXACT-STATEMENT DISCIPLINE (tags: integrity, governance; confidence 0.9): the submitted statement is hashed at submit time (`state['stmt_hash']`) and the spliced statement is re-hashed before registration, so a returned proof of a *weakened* variant cannot be banked even if it is axiom-clean. This is the check that the faithfulness screen alone does not give for operator-specified targets, where the statement is fixed in advance.
- DEF EXTRACTION (tags: mechanics; confidence 0.85): the corpus `^def name` regexes silently miss `noncomputable def` (e.g. `RiemannScaffold.riemannXi`), which made analytic-module targets unsubmittable — the prompt would have described the definition instead of pasting it, exactly the failure that let Aristotle substitute its own `IsSierpinski`. Extractors now accept `noncomputable/private/protected def`.
- RESULT (tags: targeting, metric; confidence 0.8): registered this wave: riemannXi_criticalLine_even, riemannXi_one_sub, riemannXi_reflect_of_riemannXi_criticalLine_even; AXLE-verified exact targets: 0/3; ledger 45; pending 8. Submissions: .
- RH HYGIENE (tags: integrity; confidence 0.9): the ζ-zero quartet certificate asserts vanishing at four reflected points only. Any returned proof claiming distinctness of those points, a zero location, or RH itself is rejected outright — the certificate must stay unconditional and content-free about the hypothesis.

## wave45
- HARNESS STRUCTURE (tags: mechanics, verification; confidence 0.9): NEVER inherit and call a previous wave's `main()`, and never rely on another wave's module-level globals. Wave 41 sets `TARGETS = []` on the shared module (it was a deliberate zero-spend wave); waves 42-44 inherited that and silently submitted nothing while logging their own target list. Each wave must drive its lanes explicitly and pass its targets as arguments.
- LANE ASSERTIONS (tags: mechanics, metric; confidence 0.85): any lane that computes a non-empty plan (missing imports, renames, reshapes) must assert its application counter > 0; three consecutive waves reported 'fix applied' while the effect counter stayed 0.
- MULTI-FILE ARTIFACTS (tags: backend, verification; confidence 0.8): Aristotle can return a multi-FILE project (e.g. `import RequestProject.Compactness`); harvest must extract ALL .lean files and inline/flatten internal imports before any standalone AXLE check, or the proof is judged on an incomplete fragment.
- WAVE45 STATE (tags: governance, metric; confidence 1.0): ledger=45, submitted=4, codex_submitted=1, codex_returned=0.

## wave46
- RESHAPED-MODULE HEADER (tags: mechanics, verification; confidence 0.9): when emitting a NEW module from a prover artifact, assemble the header strictly as [all imports, deduped] then [opens, deduped, with any `open X in` form DROPPED], then declarations. Lean requires every import to precede all commands and `open X in` scopes only the next command; wave 45 emitted the artifact header in source order with extra imports appended, so the module never elaborated and AXLE reported sorryAx/empty axioms as an ERROR-RECOVERY artifact, not as a dishonest proof.
- CORPUS-DUPLICATE IMPORTS (tags: mechanics, verification; confidence 0.85): artifacts re-derive corpus DEFS AND THEOREMS; drop every declaration whose name exists anywhere in Brockian/ and add an import of each dropped declaration's DEFINING module (decl->module map), so the target resolves against the corpus originals.
- CODEX CREDENTIAL BLOCK (tags: backend, mechanics; confidence 0.9): `codex exec` reaches the model but returns HTTP 401 'Missing bearer or basic authentication' from the run env; the dual-backend race is credential-blocked and needs OPENAI_API_KEY (or a logged-in `codex login`) exported in /Users/acutis/.openclaw/vault-bridges.env. Until then route every goal to Aristotle and do not count races as a lane.
- NON-ELABORATING MODULE SIGNATURE (tags: verification, integrity; confidence 0.9): all declarations `failed` with empty axiom lists (or sorryAx on a file containing no `sorry`) means module-level elaboration failure. Read the verbatim AXLE errors before concluding anything about the mathematics.
- WAVE46 STATE (tags: governance, metric; confidence 1.0): ledger=47, submitted=0 (submit lane deliberately skipped, pending pool full), codex_returned=0.

## wave48
- RECONSTRUCTED CORPUS LEMMAS ARE A FAITHFULNESS REJECT (tags: integrity, targeting; confidence 0.9): a returned artifact that reproduces corpus declarations 'verbatim where supplied and reconstructed where the supplying module was not part of the prompt' proves its theorem about ITS OWN copies, not the corpus objects. Fix the PROMPT (paste every supporting module verbatim + forbid reconstruction), never the splice shape.
- SPLICE-RESHAPE LANE RETIRED (tags: mechanics, verification; confidence 0.85): four waves (44-47) of flatten/dedup/new-module/fresh-namespace engineering registered 0 theorems; the residual failures were successive shape bugs masking the faithfulness problem above. Harvest into the ORIGINAL corpus module or not at all.
- CORPUS-SHADOW SCAN (tags: integrity, verification; confidence 0.8): reject any artifact declaration whose name matches a corpus declaration but whose statement differs after whitespace normalisation — this is the IsSierpinski substitution class, and it is cheap to detect at harvest time.
- WAVE48 STATE (tags: metric, governance; confidence 1.0): ledger=51, registered_this_wave=4, weyl_resubmitted=2, faithfulness_rejects=0+1 (phrase+shadow).

## wave50
- COMMIT+PUSH IMMEDIATELY AFTER THE SUBMIT LANE (tags: mechanics, governance; confidence 0.95): wave 49 crashed after submitting four Aristotle searches and before its single end-of-wave commit, so the repo-side governance entries were lost. Persist after EVERY state-changing lane, and wrap each lane in try/except with a status line so a late bug cannot discard earlier lanes' results.
- $AUTOLAB_DATA_DIR SURVIVES A CRASHED WAVE (tags: mechanics; confidence 0.9): aristotle_state.json lives outside the worktree, so pids/goals/statement hashes of in-flight searches are recoverable even when nothing was committed; only repo files (frontier_queue, ledger, spliced Lean) need redoing.
- SECTION-VARIABLE BINDERS ARE NOT A DEVIATION (tags: verification, integrity; confidence 0.8): a corpus def whose implicit/instance binders come from a section `variable` compares unequal when an artifact inlines them (CharactersQ.fourier). Normalise binder groups in the signature before rejecting, but keep the strict same-name-different-STATEMENT shadow screen — that one catches real definition substitution.
- ATTEST ARGV MUST BE A SORTED LIST (tags: mechanics; confidence 1.0): `argv + names` with a set raises TypeError; pass sorted(names).
- WAVE50 STATE (tags: metric, governance; confidence 1.0): ledger_total=53, substantive_total=51, registered_this_wave=2, counters={'orphans_recorded': 0, 'queue_entries_backfilled': 0, 'binder_normalised_defs': 1, 'header_lines_deduped': 42}, lane_status={'0-hygiene': 'ok', '0-splice-hygiene': 'ok', '0-def-extractors': 'ok', '0-attest-guard': 'ok', '2-binder-screen': 'ok', '1-faithfulness-gate': 'ok', 'lineage': 'ok', '1-recover-orphans': 'ok', '1-queue-save': 'ok', '3-harvest': 'ok', '3-ledger': 'ok', '4-header-dedupe': 'ok'}.

## wave56 (2026-08-27)

- **[mechanics, verification, confidence 0.95]** Append-only splicing MUST be idempotent and source-sanity-checked: a single duplicated declaration or a repeated `set_option`/`open` header block with an extra `namespace`/`end` pair silently breaks the whole corpus module, and then every later AXLE attestation of it returns all-`failed` with EMPTY axiom lists. Waves 51-55 lost five in-hand proofs to this.
- **[verification, confidence 0.9]** Whole-module `failed` + empty axiom lists always means elaboration failure, never a dishonest proof; repair the file (or dump AXLE's verbatim errors) before touching the mathematics.
- **[integrity, metric, confidence 1.0]** Scratch attestations must never be written where `gen_registry.py` reads canonical ones; guard canonical `registry/attestations/*.json` with a superset check (wave 54 shrank PROVED 11205 -> 11163 that way).
- **[metric, confidence 1.0]** ledger_total=53 substantive_total=51 registered_this_wave=0; the ledger must equal registry PROVED - 11152 exactly.

## wave57 — verdict source, declaration boundaries, one gate path
- **Never read a gate verdict from a file another guard protects from writes — read it from the producing tool's own report.** Wave 56 rejected `admissible_image_affine` with 'absent from registry/attestations/AdmissibilityHLCriterion.json' immediately after attest.py returned rc=0, because wave 55's write guard had (correctly) restored the canonical report. The gate now believes attest.py's returned JSON only. (confidence 0.95; tags: verification, mechanics, integrity)
- **A declaration block must end at the NEXT declaration's doc comment, not its keyword.** Cutting at the keyword dragged the following `/-- ... -/` into the block, which made the corpus-def anchor see 'deviations' that were pure comment drift: nu, residueImage, fourier and harmonicOscillatorClosureResolventAtI all failed the shadow screen for text that is byte-identical modulo comments (7 candidates unblocked here). The same off-by-one is what orphaned doc comments after dedup in earlier waves. The shadow and reconstruction screens stay strict — they still reject zumkeller_semiperfect, fourier_sq_sum_le and the reconstruction-claiming oscillator artifact. (confidence 0.9; tags: verification, mechanics)
- **One gate path only.** Every wave that kept calling inherited harvest helpers (W25/W27/W28) died on a one-line type bug inside them; the TypeError that cost waves 52, 53 and 56 was never in this wave's own code. (confidence 0.85; tags: mechanics)
- wave57 counters: attempted=12 attested=6 registered=6 screen_rejects=4 axle_failures=2 dumps=2 splice_reverts=0 ledger_total=62 substantive_total=60. (confidence 0.9; tags: metric)

## wave59 — the canonical attestation report is the only register input
- **gen_registry.py reads ONLY registry/attestations/<Module>.json, so a declaration can be spliced, elaborating and cleanly attested under review/ and still be invisible to the registry.** Waves 57-58 left nu_image_neg, nu_eq_of_injOn_card_ge and not_admissible_of_thirteen_scattered_residues in exactly that state. The fix is a reconciliation lane: attest the module with UNION(canonical verified decls, file decls already gated clean) so the fresh report is a strict superset, then assert each claimed declaration is actually PROVED in registry/theorems.json. (confidence 0.9; tags: verification, mechanics, metric)
- **Reconciliation must be provenance-restricted.** ~300 theorem/lemma declarations in Brockian/*.lean are unregistered, mostly pre-existing trunk mathematics; attesting them would inflate new_proved_theorems with work we did not do. Only declarations introduced by our own exp-branch wave commits (git log -S + commit-subject check) and already gated are eligible; the rest are reported in research/corpus_attestation_gap.md as an operator question. (confidence 0.95; tags: integrity, metric, governance)
- **AXLE reports `verified` with an EMPTY axiom list for many declarations** (12 of 20 in the canonical AdmissibilityHLCriterion report, including long-registered ones), so axioms_ok carries no information for those. Treat the per-declaration `verified` verdict as the signal, never deregister on an empty list alone, and surface the gap for human review. (confidence 0.8; tags: verification, integrity)
- **sorry/admit scans must be comment-blind**: wave 57's only lane failure was the doc line 'kernel-verified: no `sorry` / `admit` / `native_decide`' in SuperperfectNumbers.lean. (confidence 0.95; tags: mechanics)
- wave59 counters: attempted=10 attested=1 registered=4 reconciled=3 screen_rejects=6 axle_failures=2 corpus_gap_ours=0 corpus_gap_trunk=14 ledger_total=66 substantive_total=64. (confidence 0.9; tags: metric)

## wave60 — the canonical attestation report is the only register input
- **gen_registry.py reads ONLY registry/attestations/<Module>.json, so a declaration can be spliced, elaborating and cleanly attested under review/ and still be invisible to the registry.** Waves 57-58 left nu_image_neg, nu_eq_of_injOn_card_ge and not_admissible_of_thirteen_scattered_residues in exactly that state. The fix is a reconciliation lane: attest the module with UNION(canonical verified decls, file decls already gated clean) so the fresh report is a strict superset, then assert each claimed declaration is actually PROVED in registry/theorems.json. (confidence 0.9; tags: verification, mechanics, metric)
- **Reconciliation must be provenance-restricted.** ~300 theorem/lemma declarations in Brockian/*.lean are unregistered, mostly pre-existing trunk mathematics; attesting them would inflate new_proved_theorems with work we did not do. Only declarations introduced by our own exp-branch wave commits (git log -S + commit-subject check) and already gated are eligible; the rest are reported in research/corpus_attestation_gap.md as an operator question. (confidence 0.95; tags: integrity, metric, governance)
- **AXLE reports `verified` with an EMPTY axiom list for many declarations** (12 of 20 in the canonical AdmissibilityHLCriterion report, including long-registered ones), so axioms_ok carries no information for those. Treat the per-declaration `verified` verdict as the signal, never deregister on an empty list alone, and surface the gap for human review. (confidence 0.8; tags: verification, integrity)
- **sorry/admit scans must be comment-blind**: wave 57's only lane failure was the doc line 'kernel-verified: no `sorry` / `admit` / `native_decide`' in SuperperfectNumbers.lean. (confidence 0.95; tags: mechanics)
- **Supply every module the goal depends on VERBATIM, and record the corpus defs in the spec.** The zeta/xi vein's repeated "artifact claims reconstruction and anchors no corpus def" rejects had two causes, both ours: the submitted spec carried defs=[] so the gate had nothing to anchor, and the prompt supplied only the target module while `riemannXi` lives in Brockian/RiemannScaffold.lean, so the prover rebuilt it. Wave 60 repairs in-flight specs and submits with the full verbatim dependency closure plus an explicit no-restatement instruction; aristotle_state.json now records prompt_scheme per pid so reject rates can be compared. (confidence 0.7; tags: targeting, backend, mechanics)
- **An Aristotle project can come back with no files at all** (not_superperfect_odd_of_not_sq, wave 59). Probe the project after submit / before counting a pid as live, and resubmit dead pids instead of leaving them pending forever. (confidence 0.8; tags: backend, mechanics)
- wave60 counters: attempted=9 attested=3 registered=3 reconciled=0 screen_rejects=3 axle_failures=3 corpus_gap_ours=0 corpus_gap_trunk=14 ledger_total=79 substantive_total=77. (confidence 0.9; tags: metric)

## wave61 — the canonical attestation report is the only register input
- **gen_registry.py reads ONLY registry/attestations/<Module>.json, so a declaration can be spliced, elaborating and cleanly attested under review/ and still be invisible to the registry.** Waves 57-58 left nu_image_neg, nu_eq_of_injOn_card_ge and not_admissible_of_thirteen_scattered_residues in exactly that state. The fix is a reconciliation lane: attest the module with UNION(canonical verified decls, file decls already gated clean) so the fresh report is a strict superset, then assert each claimed declaration is actually PROVED in registry/theorems.json. (confidence 0.9; tags: verification, mechanics, metric)
- **Reconciliation must be provenance-restricted.** ~300 theorem/lemma declarations in Brockian/*.lean are unregistered, mostly pre-existing trunk mathematics; attesting them would inflate new_proved_theorems with work we did not do. Only declarations introduced by our own exp-branch wave commits (git log -S + commit-subject check) and already gated are eligible; the rest are reported in research/corpus_attestation_gap.md as an operator question. (confidence 0.95; tags: integrity, metric, governance)
- **AXLE reports `verified` with an EMPTY axiom list for many declarations** (12 of 20 in the canonical AdmissibilityHLCriterion report, including long-registered ones), so axioms_ok carries no information for those. Treat the per-declaration `verified` verdict as the signal, never deregister on an empty list alone, and surface the gap for human review. (confidence 0.8; tags: verification, integrity)
- **sorry/admit scans must be comment-blind**: wave 57's only lane failure was the doc line 'kernel-verified: no `sorry` / `admit` / `native_decide`' in SuperperfectNumbers.lean. (confidence 0.95; tags: mechanics)
- **Supply every module the goal depends on VERBATIM, and record the corpus defs in the spec.** The zeta/xi vein's repeated "artifact claims reconstruction and anchors no corpus def" rejects had two causes, both ours: the submitted spec carried defs=[] so the gate had nothing to anchor, and the prompt supplied only the target module while `riemannXi` lives in Brockian/RiemannScaffold.lean, so the prover rebuilt it. Wave 60 repairs in-flight specs and submits with the full verbatim dependency closure plus an explicit no-restatement instruction; aristotle_state.json now records prompt_scheme per pid so reject rates can be compared. (confidence 0.7; tags: targeting, backend, mechanics)
- **An Aristotle project can come back with no files at all** (not_superperfect_odd_of_not_sq, wave 59). Probe the project after submit / before counting a pid as live, and resubmit dead pids instead of leaving them pending forever. (confidence 0.8; tags: backend, mechanics)
- **A cross-module duplicate screen is mandatory: the shadow screen only compares WITHIN the target module.** Wave 60 registered Brockian.XiFunctionalEquation.riemannXi_eq_zero_of_nontrivial_zeta_zero, a same-name same-statement copy of the already-PROVED RiemannScaffold declaration (and the new sibling proof called the Scaffold original, not the copy). Wave 61 indexes every theorem/lemma in Brockian/*.lean by short name and by doc-comment-stripped statement; a candidate whose own name/statement already exists elsewhere is rejected, a duplicated helper is recorded in research/duplicate_entries.json and excluded from substantive_total. Registry entries are never deleted. (confidence 0.9; tags: integrity, metric, verification)
- **Verbatim dependency-closure prompting is the dominant lever measured so far**: the two zeta/xi goals that had been rejected for reconstruction in earlier waves came back citing the supplied lemmas and yielded 13 registrations (+13, the project's largest jump) once the prompt carried every dependency module verbatim plus an explicit no-restatement instruction. Description-only prompts reliably produce reconstruction rejects; make verbatim-context the default scheme for every submit. (confidence 0.9; tags: targeting, backend, mechanics)
- wave61 counters: attempted=8 attested=2 registered=2 reconciled=0 screen_rejects=3 axle_failures=3 corpus_gap_ours=0 corpus_gap_trunk=14 cross_module_dupes=0 dup_helpers=0 ledger_total=81 substantive_total=78. (confidence 0.9; tags: metric)

## wave62 — the canonical attestation report is the only register input
- **gen_registry.py reads ONLY registry/attestations/<Module>.json, so a declaration can be spliced, elaborating and cleanly attested under review/ and still be invisible to the registry.** Waves 57-58 left nu_image_neg, nu_eq_of_injOn_card_ge and not_admissible_of_thirteen_scattered_residues in exactly that state. The fix is a reconciliation lane: attest the module with UNION(canonical verified decls, file decls already gated clean) so the fresh report is a strict superset, then assert each claimed declaration is actually PROVED in registry/theorems.json. (confidence 0.9; tags: verification, mechanics, metric)
- **Reconciliation must be provenance-restricted.** ~300 theorem/lemma declarations in Brockian/*.lean are unregistered, mostly pre-existing trunk mathematics; attesting them would inflate new_proved_theorems with work we did not do. Only declarations introduced by our own exp-branch wave commits (git log -S + commit-subject check) and already gated are eligible; the rest are reported in research/corpus_attestation_gap.md as an operator question. (confidence 0.95; tags: integrity, metric, governance)
- **AXLE reports `verified` with an EMPTY axiom list for many declarations** (12 of 20 in the canonical AdmissibilityHLCriterion report, including long-registered ones), so axioms_ok carries no information for those. Treat the per-declaration `verified` verdict as the signal, never deregister on an empty list alone, and surface the gap for human review. (confidence 0.8; tags: verification, integrity)
- **sorry/admit scans must be comment-blind**: wave 57's only lane failure was the doc line 'kernel-verified: no `sorry` / `admit` / `native_decide`' in SuperperfectNumbers.lean. (confidence 0.95; tags: mechanics)
- **Supply every module the goal depends on VERBATIM, and record the corpus defs in the spec.** The zeta/xi vein's repeated "artifact claims reconstruction and anchors no corpus def" rejects had two causes, both ours: the submitted spec carried defs=[] so the gate had nothing to anchor, and the prompt supplied only the target module while `riemannXi` lives in Brockian/RiemannScaffold.lean, so the prover rebuilt it. Wave 60 repairs in-flight specs and submits with the full verbatim dependency closure plus an explicit no-restatement instruction; aristotle_state.json now records prompt_scheme per pid so reject rates can be compared. (confidence 0.7; tags: targeting, backend, mechanics)
- **An Aristotle project can come back with no files at all** (not_superperfect_odd_of_not_sq, wave 59). Probe the project after submit / before counting a pid as live, and resubmit dead pids instead of leaving them pending forever. (confidence 0.8; tags: backend, mechanics)
- **A cross-module duplicate screen is mandatory: the shadow screen only compares WITHIN the target module.** Wave 60 registered Brockian.XiFunctionalEquation.riemannXi_eq_zero_of_nontrivial_zeta_zero, a same-name same-statement copy of the already-PROVED RiemannScaffold declaration (and the new sibling proof called the Scaffold original, not the copy). Wave 61 indexes every theorem/lemma in Brockian/*.lean by short name and by doc-comment-stripped statement; a candidate whose own name/statement already exists elsewhere is rejected, a duplicated helper is recorded in research/duplicate_entries.json and excluded from substantive_total. Registry entries are never deleted. (confidence 0.9; tags: integrity, metric, verification)
- **Verbatim dependency-closure prompting is the dominant lever measured so far**: the two zeta/xi goals that had been rejected for reconstruction in earlier waves came back citing the supplied lemmas and yielded 13 registrations (+13, the project's largest jump) once the prompt carried every dependency module verbatim plus an explicit no-restatement instruction. Description-only prompts reliably produce reconstruction rejects; make verbatim-context the default scheme for every submit. (confidence 0.9; tags: targeting, backend, mechanics)
- wave62 counters: attempted=7 attested=4 registered=4 reconciled=0 screen_rejects=0 axle_failures=3 corpus_gap_ours=0 corpus_gap_trunk=14 cross_module_dupes=0 dup_helpers=4 ledger_total=89 substantive_total=82. (confidence 0.9; tags: metric)

## wave63 — the canonical attestation report is the only register input
- **gen_registry.py reads ONLY registry/attestations/<Module>.json, so a declaration can be spliced, elaborating and cleanly attested under review/ and still be invisible to the registry.** Waves 57-58 left nu_image_neg, nu_eq_of_injOn_card_ge and not_admissible_of_thirteen_scattered_residues in exactly that state. The fix is a reconciliation lane: attest the module with UNION(canonical verified decls, file decls already gated clean) so the fresh report is a strict superset, then assert each claimed declaration is actually PROVED in registry/theorems.json. (confidence 0.9; tags: verification, mechanics, metric)
- **Reconciliation must be provenance-restricted.** ~300 theorem/lemma declarations in Brockian/*.lean are unregistered, mostly pre-existing trunk mathematics; attesting them would inflate new_proved_theorems with work we did not do. Only declarations introduced by our own exp-branch wave commits (git log -S + commit-subject check) and already gated are eligible; the rest are reported in research/corpus_attestation_gap.md as an operator question. (confidence 0.95; tags: integrity, metric, governance)
- **AXLE reports `verified` with an EMPTY axiom list for many declarations** (12 of 20 in the canonical AdmissibilityHLCriterion report, including long-registered ones), so axioms_ok carries no information for those. Treat the per-declaration `verified` verdict as the signal, never deregister on an empty list alone, and surface the gap for human review. (confidence 0.8; tags: verification, integrity)
- **sorry/admit scans must be comment-blind**: wave 57's only lane failure was the doc line 'kernel-verified: no `sorry` / `admit` / `native_decide`' in SuperperfectNumbers.lean. (confidence 0.95; tags: mechanics)
- **Supply every module the goal depends on VERBATIM, and record the corpus defs in the spec.** The zeta/xi vein's repeated "artifact claims reconstruction and anchors no corpus def" rejects had two causes, both ours: the submitted spec carried defs=[] so the gate had nothing to anchor, and the prompt supplied only the target module while `riemannXi` lives in Brockian/RiemannScaffold.lean, so the prover rebuilt it. Wave 60 repairs in-flight specs and submits with the full verbatim dependency closure plus an explicit no-restatement instruction; aristotle_state.json now records prompt_scheme per pid so reject rates can be compared. (confidence 0.7; tags: targeting, backend, mechanics)
- **An Aristotle project can come back with no files at all** (not_superperfect_odd_of_not_sq, wave 59). Probe the project after submit / before counting a pid as live, and resubmit dead pids instead of leaving them pending forever. (confidence 0.8; tags: backend, mechanics)
- **A cross-module duplicate screen is mandatory: the shadow screen only compares WITHIN the target module.** Wave 60 registered Brockian.XiFunctionalEquation.riemannXi_eq_zero_of_nontrivial_zeta_zero, a same-name same-statement copy of the already-PROVED RiemannScaffold declaration (and the new sibling proof called the Scaffold original, not the copy). Wave 61 indexes every theorem/lemma in Brockian/*.lean by short name and by doc-comment-stripped statement; a candidate whose own name/statement already exists elsewhere is rejected, a duplicated helper is recorded in research/duplicate_entries.json and excluded from substantive_total. Registry entries are never deleted. (confidence 0.9; tags: integrity, metric, verification)
- **Verbatim dependency-closure prompting is the dominant lever measured so far**: the two zeta/xi goals that had been rejected for reconstruction in earlier waves came back citing the supplied lemmas and yielded 13 registrations (+13, the project's largest jump) once the prompt carried every dependency module verbatim plus an explicit no-restatement instruction. Description-only prompts reliably produce reconstruction rejects; make verbatim-context the default scheme for every submit. (confidence 0.9; tags: targeting, backend, mechanics)
- wave63 counters: attempted=9 attested=5 registered=5 reconciled=0 screen_rejects=1 axle_failures=3 corpus_gap_ours=0 corpus_gap_trunk=14 cross_module_dupes=0 dup_helpers=0 ledger_total=95 substantive_total=92. (confidence 0.9; tags: metric)

<!-- insight:wave63:helper-dup -->
- (wave63, conf 0.9, tags metric/integrity/mechanics) The registry keys on fully-qualified names, so splicing a pre-existing corpus lemma into another module registers a new PROVED entry and inflates new_proved_theorems; drop artifact helpers that already exist anywhere in Brockian/*.lean before splicing (the original module is imported anyway).

## wave66 — the canonical attestation report is the only register input
- **gen_registry.py reads ONLY registry/attestations/<Module>.json, so a declaration can be spliced, elaborating and cleanly attested under review/ and still be invisible to the registry.** Waves 57-58 left nu_image_neg, nu_eq_of_injOn_card_ge and not_admissible_of_thirteen_scattered_residues in exactly that state. The fix is a reconciliation lane: attest the module with UNION(canonical verified decls, file decls already gated clean) so the fresh report is a strict superset, then assert each claimed declaration is actually PROVED in registry/theorems.json. (confidence 0.9; tags: verification, mechanics, metric)
- **Reconciliation must be provenance-restricted.** ~300 theorem/lemma declarations in Brockian/*.lean are unregistered, mostly pre-existing trunk mathematics; attesting them would inflate new_proved_theorems with work we did not do. Only declarations introduced by our own exp-branch wave commits (git log -S + commit-subject check) and already gated are eligible; the rest are reported in research/corpus_attestation_gap.md as an operator question. (confidence 0.95; tags: integrity, metric, governance)
- **AXLE reports `verified` with an EMPTY axiom list for many declarations** (12 of 20 in the canonical AdmissibilityHLCriterion report, including long-registered ones), so axioms_ok carries no information for those. Treat the per-declaration `verified` verdict as the signal, never deregister on an empty list alone, and surface the gap for human review. (confidence 0.8; tags: verification, integrity)
- **sorry/admit scans must be comment-blind**: wave 57's only lane failure was the doc line 'kernel-verified: no `sorry` / `admit` / `native_decide`' in SuperperfectNumbers.lean. (confidence 0.95; tags: mechanics)
- **Supply every module the goal depends on VERBATIM, and record the corpus defs in the spec.** The zeta/xi vein's repeated "artifact claims reconstruction and anchors no corpus def" rejects had two causes, both ours: the submitted spec carried defs=[] so the gate had nothing to anchor, and the prompt supplied only the target module while `riemannXi` lives in Brockian/RiemannScaffold.lean, so the prover rebuilt it. Wave 60 repairs in-flight specs and submits with the full verbatim dependency closure plus an explicit no-restatement instruction; aristotle_state.json now records prompt_scheme per pid so reject rates can be compared. (confidence 0.7; tags: targeting, backend, mechanics)
- **An Aristotle project can come back with no files at all** (not_superperfect_odd_of_not_sq, wave 59). Probe the project after submit / before counting a pid as live, and resubmit dead pids instead of leaving them pending forever. (confidence 0.8; tags: backend, mechanics)
- **A cross-module duplicate screen is mandatory: the shadow screen only compares WITHIN the target module.** Wave 60 registered Brockian.XiFunctionalEquation.riemannXi_eq_zero_of_nontrivial_zeta_zero, a same-name same-statement copy of the already-PROVED RiemannScaffold declaration (and the new sibling proof called the Scaffold original, not the copy). Wave 61 indexes every theorem/lemma in Brockian/*.lean by short name and by doc-comment-stripped statement; a candidate whose own name/statement already exists elsewhere is rejected, a duplicated helper is recorded in research/duplicate_entries.json and excluded from substantive_total. Registry entries are never deleted. (confidence 0.9; tags: integrity, metric, verification)
- **Verbatim dependency-closure prompting is the dominant lever measured so far**: the two zeta/xi goals that had been rejected for reconstruction in earlier waves came back citing the supplied lemmas and yielded 13 registrations (+13, the project's largest jump) once the prompt carried every dependency module verbatim plus an explicit no-restatement instruction. Description-only prompts reliably produce reconstruction rejects; make verbatim-context the default scheme for every submit. (confidence 0.9; tags: targeting, backend, mechanics)
- wave66 counters: attempted=11 attested=0 registered=0 reconciled=0 screen_rejects=1 axle_failures=3 corpus_gap_ours=0 corpus_gap_trunk=14 cross_module_dupes=0 dup_helpers=0 ledger_total=93 substantive_total=90. (confidence 0.9; tags: metric)

<!-- insight:wave66:helper-dup -->
- (wave66, conf 0.9, tags metric/integrity/mechanics) The registry keys on fully-qualified names, so splicing a pre-existing corpus lemma into another module registers a new PROVED entry and inflates new_proved_theorems; drop artifact helpers that already exist anywhere in Brockian/*.lean before splicing (the original module is imported anyway).

<!-- insight:wave67:receipt-nonregression -->
- (wave67, conf 0.99, tags verification/integrity/metric) A one-declaration re-attestation must never overwrite a module receipt: merge the fresh declaration into the existing receipt, assert the declaration-count floor, and regenerate the registry before reporting the metric. Wave 66 collapsed eleven receipts; restoring siblings and quarantining only unresolved samples changed the honest trusted delta from the reported 93 to 83.

<!-- insight:wave68:in-process-receipt-merge -->
- (wave68, conf 0.99, tags mechanics/verification/integrity) A proof harvester must call attest.attest in-process and atomically merge fresh declarations by fully-qualified name; invoking the attest.py CLI for one name creates a crash window that can replace a complete module receipt with a singleton.
