# DOCUMENT-TO-THEOREM-CROSSWALK.md

Maps documentary assertions in `Evidence/Provided/` to **checked declarations** in the submitted
Lean, and flags assertions that remain **unsupported** by any submitted source. "Supported (identity
+ static)" = the declaration exists, is byte-identical to submission, and is `sorry`/axiom-clean;
full support additionally requires the deferred compile.

## 1. Supported by submitted Lean (Waves 16–29)

Each wave contributes a **module structure**, a **positive finite witness**, a **countermodel**, and a
**governing non-entailment theorem**. Documentary claim ↔ audited firewall theorem:

| Wave | Documentary claim (title) | Governing non-entailment theorem (audited) |
|---|---|---|
| 16 | Generative Lifeworld / Sedimentation | `Wave16.transmission_does_not_entail_reactivation` |
| 17 | Expression, Sign, Reactivatable Sense | `Wave17.circulating_sign_does_not_entail_reactivatable_sense` |
| 18 | Typification, Relevance, Social Stock | `Wave18.shared_classification_does_not_entail_{relevance, warranted_application}` |
| 19 | Social Acts, Commitments, Deontic Status | `Wave19.public_uptake_does_not_entail_{valid_commitment, deontic_status}` |
| 20 | Collective Agency, Roles, Institutional Persons | `Wave20.coordination_and_roles_do_not_entail_{collective_agency, collective_authority}` |
| 21 | Normative Conflict, Authority, Consent, Answerability | `Wave21.institutional_authority_does_not_entail_{consent, legitimacy, answerability}` |
| 22 | Evidence, Provenance, Epistemic Registers | `Wave22.recorded_provenance_does_not_entail_{evidential_support, justified_acceptance, truth}` |
| 23 | Formal Ontology Kernel / Cross-Ontology Alignment | `Wave23.validated_mapping_does_not_entail_{identity, equivalence, all_theorem_preservation, conservative_extension}` |
| 24 | Operational Digital Ontology / API Semantics | `Wave24.schema_transport_does_not_entail_{authorization, semantic_validity, invariant_preservation, accepted_transition}` |
| 25 | Verified Constitutive Knowledge Graph / Governance Runtime | `Wave25.ingestion_evaluation_does_not_entail_{verified_publication, authorized_governance, safe_execution, invariant_runtime}` |
| 26 | Historical Fidelity / Source-Critical Attribution | `Wave26.citation_comparison_does_not_entail_{historical_fidelity, independent_verdict}` |
| 27 | Empirical Adequacy / Falsifiability / Replication | `Wave27.observed_fit_does_not_entail_{independent_replication, empirical_adequacy}` |
| 28 | Standards Conformance / Interoperability | `Wave28.vocabulary_schema_does_not_entail_{conformance, interoperability}` |
| 29 | Novelty / Priority / Independent Attestation | `Wave29.no_hit_search_does_not_entail_{novelty, priority}`, `…does_not_authorize_novelty_claim` |

Total submitted declarations: **234** `theorem`s across 14 modules; **181** audited via
`#print axioms`; **34** are the Book Three/Four governing firewall roots above. (Identity + static
support established now; compile support pending.)

## 2. Documentary assertions that remain UNSUPPORTED by submitted Lean

| Assertion (source) | Status |
|---|---|
| "Waves 16–**30** passed" / "`BookFive.lean` passed" (`CORPUS-VERIFICATION-2026-08-29.md`) | ❌ **Unsupported** — no `Wave30.lean`/`BookFive.lean` in bundle. Contradicts manifest scope (16–29). |
| Waves 1–15 formalized (roadmaps, `…Waves_10-15.docx`, `…Nine_Waves…docx`) | ❌ **Unsupported** — prose only; no `.lean`. See `MISSING-FORMAL-SOURCES.md §A`. |
| Historical fidelity / empirical adequacy / conformance / interoperability / novelty / priority hold for the corpus | ❌ **Out of formal scope by design** — Book Four proves these are *not entailed* by the internal evidence. They are open external obligations, not theorems. |
| "37 theorems across Waves 16–30 … every footprint `propext`" (`CORPUS-VERIFICATION`) | ⚠️ **Partially supported** — the 34 Waves-16–29 firewall roots are audited (vendor `.out`); the 3 extra assume Wave 30, which is absent. Independent footprint reproduction pending compile. |

## 3. Firewall (applies to every row above)

Compilation supports **only** the consequences of the submitted formal models. The crosswalk maps
prose to *formal claims*; it does not upgrade any external, historical, or empirical claim to a
verified status. The Book Four non-entailment theorems exist precisely to prevent that upgrade.
