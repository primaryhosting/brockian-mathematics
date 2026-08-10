# Uncharted Ground: contributions to the machinery around RH

**Directive (Chris, 2026-08-10):** "now lets try to solve some new uncharted ground in the machinery of the Riemann hypothesis, we have plenty of room for contributions."

## The epistemic contract (fixed BEFORE any mathematics; adapted from the campaign's own C.6)
1. Genuine attempts, adversarial review always on, honest reporting of whatever survives **including "nothing."**
2. Every line of attack carries **control objects** on which any RH-analogue is FALSE: Davenport–Heilbronn functions, Epstein zeta of class number 2, Beurling systems with a planted off-line zero. A method that "proves" the analogue there is dead.
3. Every agent must **name its first unjustified step.** Claims go to hostile reviewers blind to each other and to the claimant, each assigned a specific failure mode.
4. Nothing is reported as a theorem unless it survives refereeing AND (where finite/formalizable) machine verification at our toolchain. Registers as everywhere: PROVED verbatim-only, else COMPUTATION/CONDITIONAL/CONJECTURE/OPEN.
5. Expect results to arrive sideways; log the graveyard as carefully as the survivors.

## Calibration (honest)
The CLAUDE campaign: an unreleased frontier model, 60 agents, 54 hours → exactly ONE new theorem, found sideways, with the model's own verdict that most lines "re-derived the expert frontier." We are a smaller instrument. Our edge is different: a proving FLEET (Aristotle) + attestation (AXLE 4.32.0) + a corpus deep in Hardy–Littlewood constants + interval-certified numerics discipline. We aim where those instruments actually bite.

## Targets (first wave)

**T1 — The ceiling gap (0.6725 → 0.68185), computational-then-exact.**
The paper's Remark 1.1 + §7.4: an extremal law says a bandwidth-one certificate "holding configuration by configuration" can certify 0.68185; the paper's own optimized inequality extracts 0.6725. The 0.0094 gap is a FINITE-DIMENSIONAL question about what the rank–trace family extracts from (tr, tr², block structure). Attack: reproduce the optimization; search richer certificate families (cubic weights à la §7(g), multi-window, configuration-adaptive); either close the gap toward the ceiling or characterize the obstruction precisely. Deliverable EITHER WAY is a statement: "the rank–trace family's exact ceiling is X because Y." Control: certificates must NOT improve on Davenport–Heilbronn (where off-line zeros exist) beyond what its true zero configuration allows.

**T2 — The conditional ladder, formalized.**
§7(f): under HL*(k₀,λ) (higher moments of the sine-kernel Gram spectrum ↔ Hardy–Littlewood-type additive correlations), the counts improve: HL*(4,·) → 13/18; all k → proportion 1 of simple zeros. Contribution: build the FORMAL scaffold at lean-4.32.0 — precise Lean statements of the HL* hypotheses (CONJECTURE register), the sine-kernel moment values m_k(1) = 1, 4/3, 2, 13/4 (k ≤ 4) as PROVED finite computations (Aristotle targets — they are explicit integrals/limits), and the implication skeleton as CONDITIONAL. Nobody has formalized this ladder; it is machinery, it is ours to build, and it feeds the corpus's CONDITIONAL register honestly.

**T3 — The certificate observatory (numerics at scale, interval-certified).**
Extend §8's finite-T tables: compute the certificate ratios C/N on windows of our checksummed zero dataset (and larger fleet-computed sets), with interval arithmetic and provenance, tracking saturation toward 2F(1)−1 = 1/2 and taper dependence. Deliverable: a dataset + site lab + short computational note. Modest, real, publishable.

**T4 — (upstream) von Neumann + Sylvester to Mathlib.**
Already queued to Aristotle (frontier_queue, f8cb569). If fresh proofs land at 4.32.0, prepare Mathlib PRs — permanent community contribution.

**Parked (named so the graveyard is honest):** zero-density near the line (the campaign's own dead follow-up); GL(2)/automorphic extension (beyond our analysis); anything claiming progress on RH itself (the mechanism's ceiling is ≈0.68185 — §1.5 and §7.5 say the road beyond runs through Hardy–Littlewood-strength pair information, which is conjectural).

## Execution
Wave 1 (tonight): two research agents (T1 numerics+search; T2 formal scaffold drafting) with campaign-style briefs + control objects; hostile review before anything is called a result; Aristotle picks up T2's finite pieces + T4 in the night rotation. Larger fan-out (judge panels, refuter swarms per claim) on Chris's word.

**Status:** program written 2026-08-10 late; wave 1 launching.
