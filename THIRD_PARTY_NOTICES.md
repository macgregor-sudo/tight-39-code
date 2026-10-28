# Licenses, source attribution and modifications

## Original project code

Original project code is made available under **Apache-2.0**, in [LICENSE](LICENSE), to the extent that contributors hold or are authorized to license the relevant rights. This grant does not assert exclusive copyright over AI-generated output, mathematical facts or ideas. The AI-generation disclosure and evidenced upstream copyright statements remain intact. No separate license for a standalone manuscript is selected here.

Borrowed implementations retain their original grants, copyright, attribution and modification notices. In particular, the MIT fixed-point sources remain MIT; the Apache root does not replace that grant. Mathematical citations and ordinary dependencies are distinguished from copied/adapted source below.

## SCV complex analysis

Source: [bjbraams/lean-SCV](https://github.com/bjbraams/lean-SCV/tree/50392764ae64d75779abbea1396fe93d80b677cc), revision `50392764ae64d75779abbea1396fe93d80b677cc`, Apache-2.0. The 31 whole-file ports under `Proofs/SeveralComplexVariables/`, `Proofs/ComplexAnalysis/` and `Proofs/ToMathlib/` retain the original relative paths within `Proofs/` and **Copyright (c) 2026 Bastiaan J Braams. All rights reserved.** notices. Exact upstream grant: [LICENSES/SCV-Apache-2.0.txt](LICENSES/SCV-Apache-2.0.txt).

Changes include pinned-toolchain compatibility repairs, current module/public-import syntax, and attribution/comment edits. Original mathematical qualifications and copyright notices remain. The pinned original and present source are the comparison endpoints; historical `vendor/LICENSE` and `PORT-REPAIRS.md` paths are not shipped files. Their license/change-notice roles are fulfilled by this section, the retained license and individual headers.

Additional adaptations of `SeveralComplexVariables/AnalyticGerm.lean` occur in `Proofs/ConvergentGermLocalRing.lean`, `Proofs/ConvergentResidualJetMap.lean`, `Proofs/PairingA6.lean`, the concrete germ definitions in `Proofs/PairingDefinitions.lean`, and expanded germ definitions in `Challenge.lean`. They specialize to finite complex coordinate germs at zero and supply the stated local-ring/jet interfaces; headers distinguish adapted definitions from subsequent project proofs.

**Cauchy formula credits.** Pinned SCV `ComplexAnalysis/CauchyDerivatives.lean` is identical to [lean-CA at `fd55e2ef4fdc95a97bc0b2d887e290ae7d8744b2`](https://github.com/bjbraams/lean-CA/blob/fd55e2ef4fdc95a97bc0b2d887e290ae7d8744b2/ComplexAnalysis/CauchyDerivatives.lean). SCV's importing commit is `23caf97abf4759f4fce234112054b57e49d8a68c`. The actual [lean-CA CREDITS.md](https://github.com/bjbraams/lean-CA/blob/fd55e2ef4fdc95a97bc0b2d887e290ae7d8744b2/CREDITS.md) acknowledges the related integral formula in [Mathlib PR #43100](https://github.com/leanprover-community/mathlib4/pull/43100), by `JJYYY-JJY` with credited coauthor `ajirving`, using historical comparison commit `bdaa4f3ed881b13004888a59002451824e0ece24`. That record expressly distinguishes related results from proof origin. This is theorem-level credit, not a claim that SCV copied a proof body from the PR. The retained Braams notice and Apache grant apply to the actual copied implementation. The lean-CA and SCV license texts agree.

## Growth dimension and topology

| Source and revision | Selected use, grant and modifications |
|---|---|
| [ImperialCollegeLondon/FLT](https://github.com/ImperialCollegeLondon/FLT/tree/923d45174c500aa1d994ba973bac38ea39eacbf7), `923d45174c500aa1d994ba973bac38ea39eacbf7` | `FLT/Slop/DimensionTheorem/{Numeric,Defs,DimLeGrowth}.lean` → the three same-named `Proofs/GrowthDimension` files. Akhil Mathew's copyright/Apache-2.0 notices remain; exact grant [LICENSE-FLT](LICENSE-FLT). Headers describe extraction, namespace/module changes and chain-argument adaptation. Later consumers are local compositions. |
| [Xmask19/mathlib4](https://github.com/Xmask19/mathlib4/blob/230d75acb32d80e7d7c4f4cd028b139f3dc28be7/Mathlib/AlgebraicTopology/InvarianceOfDomain.lean), `230d75acb32d80e7d7c4f4cd028b139f3dc28be7` | Kai Lam's `InvarianceOfDomain.lean` split into `Proofs/TopologyPreflight/ConditionalIoD.lean` and `Proofs/TopologyPreflight/ConditionalDimension.lean`. Copyright/change notices remain. Apache-2.0, [LICENSES/Apache-2.0.txt](LICENSES/Apache-2.0.txt); this standard text differs in appendix placeholder spelling from upstream, not in operative terms. Other topology adapters are local. |
| [harfe/fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4/tree/770940ddf9878cf61952ed53d910b92bca841838), `770940ddf9878cf61952ed53d910b92bca841838` | Five same-named `Proofs/FixedPointTheorems/*.lean` ports retain harfe's copyright and **MIT** grant, [LICENSES/harfe-MIT.txt](LICENSES/harfe-MIT.txt). Compatibility patch ancestry is Apache-2.0: OpenAI/math `1581d4cbdd69a0faf34b2089614fe2a814316a6a`, `lean/patches/fixed-point-theorems-lean4341.patch`. Both source and patch credits remain in headers. |

## OpenAI multiplicity excerpts and Abel factorization

[openai/math](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a), `1581d4cbdd69a0faf34b2089614fe2a814316a6a`, supplies these Apache-2.0 adaptations. Original files are under `lean/OAI/RingTheory/Multiplicity/`:

| Local file | Original files and declaration scope |
|---|---|
| `Proofs/HSGrading.lean` | `LechBoundedEquiv.lean`, `SeparableOrderNormalizedLength.lean`: grading image/sub decompositions, finite-rank recurrence, quotient generators, finiteness and torsion helpers |
| `Proofs/HSAssociatedGraded.lean` | `LechBoundedEquiv.lean`, `IdealGradedRing.lean`: ideal-power pieces, length telescoping, Rees grading, quotient grade and degree-one generators |
| `Proofs/HSEventualPolynomial.lean` | `SeparableOrderNormalizedLength.lean`: `sumPolynomial` through `EventuallyPolynomial.of_recurrence` |
| `Proofs/HSHilbertSerre.lean` | `LechHilbertSerre.lean`: `Lech.hilbertSerre` and the two eventual-polynomial ideal-grade results |

Changes comprise selected-declaration extraction, narrow imports, module format and compatibility repairs. Inspected originals have no separate individual author/copyright header; none is invented. Standard Apache-2.0 grant: [LICENSE](LICENSE).

[archernikov/abel-formalization](https://github.com/archernikov/abel-formalization/blob/acf1a5a138aa966e1380e4af3100e6c286d00fe6/AbelFormalization/AnalyticHadamard.lean), `acf1a5a138aa966e1380e4af3100e6c286d00fe6`: `analyticAt_exists_sub_eq_linear` adapted as private `shifted_series_factor` in `Proofs/ConvergentGermPolynomialRepresentatives.lean`. It specializes to finite complex coordinates, retains the given/shifted convergent series, and passes factorization to neighborhood germs. Subsequent polynomial-representative induction and quotient surjectivity are local. The original specifies no individual author/copyright header. Apache-2.0 grant: [LICENSE](LICENSE).

## Native Albert code

Source: [compact-albert-recognition](https://github.com/macgregor-sudo/compact-albert-recognition/tree/40d3b344180d9ddb78aaa2876873377c1e631515), `40d3b344180d9ddb78aaa2876873377c1e631515`. Retained grant/notices: [Native-Albert-Apache-2.0.txt](LICENSES/Native-Albert-Apache-2.0.txt) and [Native-Albert-THIRD-PARTY-NOTICES.md](LICENSES/Native-Albert-THIRD-PARTY-NOTICES.md). This is prior-project reuse. Its maintained AI-generation disclosure does not establish a copyright holder/year; none is invented.

| Selected use | Upstream expression and modifications |
|---|---|
| `Proofs/NativeIncludedQuartetReadouts.lean`; selected native definitions expanded in `Challenge.lean` | The included body reproduces `Glennie/Native.lean`, all declarations in namespace `Glennie`; source SHA256 `fe4ccae1467e8b51511aa8361bc8f8d68965f8a409c56a6ca2a0f988c39f6591`. Challenge expands only its required native definitions. `Proofs/PairingDefinitions.lean` imports native providers and adds statement adapters; it does not recopy that body. Assembly hoists imports; native product retained rather than defined by transport. |
| Coordinate adapters within `Proofs/NativeIncludedQuartetReadouts.lean` | `Glennie/SectorModel.lean::{complexHermitianMatrix_isHermitian,complexHermitianMatrix_inverse}` supply Hermitian coordinate adapters; `Glennie/Sector.lean::hiddenColumn` is adapted as `octonionComplexVector`. Retained headers describe changes and first-party surrounding product proofs. |
| `Proofs/NativeRightSU3Action.lean` | `Glennie/Native/SectorLeftAction.lean::{leftMulEquiv,sectorLeftEquiv}` and Gram/adjugate/product/trace proofs; `Glennie/Theorems/SectorTransport.lean::{sectorAdjointAdjugate_mul,sectorAdjointAdjugate_unitary}`. Uses the common-right convention B=Mᴴ=−conj Z and h=Vᴴ, with the existing native coordinate/product equivalence; exact original hashes and changes remain in its header. |
| `Proofs/NativePolynomialEvaluationStaged.lean` | `Glennie/Native/AlgebraLaws.lean`: `octDot_add_left`, `octDot_smul_left`, Jordan add/smul/unit laws; `Glennie/Native/CubicIdentity.lean`: `jordanLinear`, `traceLinear` and application lemmas. Extraction omits file wrappers/imports and reuses one carrier. Later coordinate tensor/evaluation proofs are first-party. |
| `Proofs/NativeTrialityReuseAlgebraLaws.lean` | `Glennie/Native/AlgebraLaws.lean`, lines 119–130 and 141–180; earlier laws reused from the provider; namespace renamed. |
| `Proofs/NativeTrialityReuseCubicIdentity.lean` | `Glennie/Native/CubicIdentity.lean`, lines 30–59, `cubicResidual_eq_zero` and `jordan_identity`; namespace and references adapted. |
| `Proofs/NativeTrialityReuseCubicJordan.lean` | `Glennie/Native/CubicJordan.lean`, lines 16–89; namespace renamed and module names flattened. |
| `Proofs/NativeTrialityReuseOctonionLaws.lean` | `Glennie/Native/AlgebraLaws.lean`, lines 15–77; namespace adapted, original octonion-law proofs retained. |
| `Proofs/NativeTrialityReuseInnerDerivation.lean` | `Glennie/Compact/InnerDerivation.lean`, lines 17–182; namespace and native-carrier references adapted as recorded in its header. |
| Three helpers in `Proofs/GSAnalytic.lean` | `Glennie/Compact/Flows.lean`: `hasDerivAt_flowC_apply` (118–123) → `analytic_hasDerivAt_exp_smul_apply`; `flowC_mul_flowInvC` (90–97) → `analytic_exp_smul_mul_exp_smul_neg`; `flowC_prodC` (131–160), with `hasDerivAt_flowInvC` (125–127) inlined → `exp_map_bilinear`. Generalized from the native product as recorded in source. Other first-party reuse is separately credited. |

The bilinear-law original has SHA256 `5073790a660cf4bed5de5db24b215b2ecb3e8fc7477016aa0a4599328d2b9b67`; the linear-packaging original has SHA256 `f9567c1e8f64a22376ea20a42fb513ad0b45936a1a0049586f205223ae729c35`. The historical 66-line extracted body has SHA256 `b697fa80547875fdbe3b930cf20d8352c8849bf88ae006dcb3b80db302ea2aa1`. These identify ancestry, not a fresh certification of every assembled byte. This public map replaces private `NATIVE-POLYNOMIAL-PROVENANCE.md`, `SOURCE-ATTRIBUTION.md`, `PARITY.md` and `coordinates/upstream/` locators for redistribution; historical records remain outside this tree. The source retains the assembled module scopes/options and one native carrier. Real native evaluation asserts no ring map from ℝ or ℚ to a finite field.

Cubic ancestor: [albert-frame-triple-invariants](https://github.com/macgregor-sudo/albert-frame-triple-invariants/blob/dd06ef5d423a0e4a5d814d2c221e999b98887ee1/AlbertLean/CubicJordan.lean), `dd06ef5d423a0e4a5d814d2c221e999b98887ee1`, `AlbertLean/CubicJordan.lean`, SHA256 `cc885b590ac2317fbde15b490d8205d684fafbf7dbe4ffd883155275a0986826`. Its Apache license matches the retained native text. The upstream adaptation changes ℚ to ℝ and module/API packaging; it does not transport a split-Albert theorem by renaming a type. No separate individual author/header is present.

## Small Mathlib adaptation and ordinary dependencies

`Proofs/SpanningDescent.lean::zmodField` follows [Mathlib/Algebra/Field/ZMod.lean](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Field/ZMod.lean), lines 19–36, revision `065356127b1dc0016f66b7283ce0ce2c4055aa55`. **Copyright (c) 2018 Chris Hughes. All rights reserved.** Author: Chris Hughes. Apache-2.0, [LICENSE](LICENSE). Local changes use a definition instead of a global instance, explicit primality and a locally proved inverse-cancellation fact; exact changes are described beside the definition.

Lean `v4.35.0-rc2` and nine locked Lake packages are ordinary dependencies, not vendored source in this tree. Mathlib, plausible, LeanSearchClient, importGraph, ProofWidgets, aesop, Qq and batteries have Apache-2.0 root grants; Cli has MIT. Exact revisions remain in [lake-manifest.json](lake-manifest.json); dependency notices remain in their own checkouts. A future distribution of checkouts/caches/binaries must retain notices for that actual payload. Mathlib's current official [LICENSE](https://github.com/leanprover-community/mathlib4/blob/master/LICENSE) was checked on 28 October 2026 and remains Apache-2.0; this neither upgrades the pinned dependency nor implies endorsement or contribution acceptance.

## Generated source and mathematical references

Generated Lean files and exact certificate data are included as Lean source. Generator references remain as provenance, not a claim that every historical generator is bundled or required to build this closure. Existing generators/useful inputs remain preserved in the development archive; none is deleted or relicensed here. No blanket preferred-source claim is made, and no GPL corresponding-source packaging is imposed on this Apache release. Any regeneration scripts later selected for distribution need their actual license, template and input provenance checked.

CKM, Werner, Engelking, Boyd–Vandenberghe, Höhn and related algebraic literature are mathematical citations, not copied software merely by being cited. CompositionAlgebras doubling is a reading reference: its implementation is neither shipped nor imported here. Höhn is not a proof dependency. Calls to Mathlib APIs, including the adjugate formula, are ordinary dependency use unless explicitly identified above as an adaptation.

Thank you to the credited source authors/maintainers and Lean/Mathlib contributors. “If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
