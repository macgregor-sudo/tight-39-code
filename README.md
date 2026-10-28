# On the local geometry of the tight 39-point code in 𝕆P²

Cohn, Kumar and Minton’s tight thirty-nine-point code in the octonionic projective plane consists of thirteen mutually unbiased Jordan frames. Its four-phase family raises a local question. Do explicit deformation families account for every nearby real solution of the defining equations?

At every good phase, the real answer is yes. Four smooth labelled families meet along a common family, and their solution germ in an automorphism slice has normal form $`\mathbb R^4\times\bigcup_{i=0}^3\mathbb R_i^6`$. A sharp local residual-distance estimate makes this description quantitative. On a specified, possibly smaller, open dense locus, the complex germ has exactly four top-dimensional components and the unlabelled code quotient has local dimension ten. Accumulating open ten-dimensional patches rule out a twenty-four-dimensional manifold neighborhood of the original resonant code, without classifying its germ.

The distinction between the two phase loci, the two metrics and the labelled and unlabelled statements matters throughout. The exact-frame loss corollary is a separate selected consequence. The verification section below distinguishes completed compilation checks from the remaining release checks.

## Objects and hypotheses

Let $`J=H_3(\mathbb O)`$ be the compact real Albert algebra, with Jordan product $`x\circ y`$, identity $`e`$, trace $`\mathrm{tr}`$, and positive trace pairing
```math
\langle x,y\rangle=\mathrm{tr}(x\circ y).
```
A pure point satisfies $`p\circ p=p`$ and $`\mathrm{tr}p=1`$. An ordered Jordan frame is a triple of pairwise orthogonal pure points summing to $`e`$. Two frames are complementary when all nine cross overlaps equal $`1/3`$. The configuration has thirteen frame labels and three outcome labels per frame. Its four marked quartets have frame labels
```math
\{0,1,2,3\},\quad\{0,4,5,6\},\quad\{0,7,8,9\},\quad\{0,10,11,12\}.
```
Labels, outcome order and central representatives are retained until the stated quotient is taken.

Write $`P(\xi)`$ for the literal CKM family, with $`\xi=(A,B,C,D)\in(S^1)^4`$. The four normalized phase triples are
```math
\begin{aligned}
d_0&=(AB/C,(AD)^{-1},CD/B),\\
d_1&=(ACD,-B/C,-(ABD)^{-1}),\\
d_2&=(-CD,C^{-1},-D^{-1}),\\
d_3&=(-A^{-1},-B^{-1},AB).
\end{aligned}
```
Each triple has product one. Call a phase *good* when every entry of every $`d_H`$ has cube different from one. This is the predicate `CKM.NativeFourFamily.IsGoodPhase`. The real exhaustion and error bound hold at every good phase. The complex component theorem and the stated local dimension theorem use the possibly smaller locus
```math
\mathcal G=\{\xi\mid\xi\text{ is good}\}\cap\{\text{the selected native Jacobian minor is nonzero}\}.
```
The actual minor is defined by the original equations in `nativePivotLocus`; $`\mathcal G`$ is `Option2.NativeStress.PhaseA6.nativeA6Locus`. Its nonemptiness, openness and density are conclusions, rather than additional rank assumptions supplied by the reader. The first-order and representation theorems hold at all unit phases, including resonances.

For quantitative statements, $`F`$ is the full original polynomial residual, comprising 1,053 idempotency coordinates, 39 trace equations, 351 frame-sum coordinates and 741 distinct-pair overlap equations. Thus $`F`$ has 2,184 real coordinates. Its product uses the original half normalization, and its cross-overlap target is $`1/3`$. The native coordinates are the 27 real upper coordinates of each Albert element. The default coordinate and residual norms are finite-product supremum norms. A second configuration distance comes from the positive trace pairing. No nonlinear change of coordinates is assumed to be an isometry.

## Native results and their limits

For any finite family of native pure points $`P_1,\ldots,P_N`$, the distinct-pair bound $`\langle P_i,P_j\rangle\le1/3`$ implies $`N\le39`$. The literal CKM configuration attains the bound. For 39 pure points, the overlap bound holds if and only if the labels can be partitioned into thirteen actual complementary Jordan frames. Distinct labels have zero overlap exactly when they belong to the same frame. This labelled partition is locally constant on the tight-code locus in the product topology of the native upper coordinates; it is not asserted constant under arbitrary ambient perturbations. Thus the code-to-frame passage is a theorem about arbitrary equality configurations, not an assumed frame presentation.

Fixing the specified complex quartet identifies every complementary pure point with
$`p(U)=(I/3,U/3)`$, $`U\in SU(3)`$, in the specified Tits coordinates. A complementary ordered frame is a central triple $`U,\omega U,\omega^2U`$, with both possible cyclic orientations accounted for. Two frames are complementary exactly when their representatives are orthogonal for the full complex Hilbert–Schmidt trace. The nine remaining frames therefore form a determinant-normalized qutrit unitary error basis. Actual Albert automorphisms fixing the selected subalgebra pointwise give precisely the common-right $`SU(3)`$ gauge. This is a specific gauge equivalence, not the broader left/right/phase/permutation equivalence sometimes used for unitary error bases.

After removal of the common-right gauge, the labelled normalized construction gives an embedded $`PSU(3)\times T^2`$ family. Its matrix construction is the classical [shift-and-multiply construction of Werner, Definition 8, Proposition 9 and equation (23)](https://arxiv.org/pdf/quant-ph/0003070v1#page=17). The global embedding of this family does not assert global exhaustion of all unitary error bases or configurations.

For the matrix family $`U_{ab}=X^bD_bZ^a`$, with $`D_0=D_1=I`$ and $`D_2=\mathrm{diag}(d)`$, the unrestricted real first-order space is
```math
\mathbb R^6\oplus\mathbb C^6\oplus\mathbb C^{\{j\mid d_j^3=1\}},
\qquad \dim_{\mathbb R}=18+2r,\quad r\in\{0,1,3\}.
```
All nine matrices may vary; the variations are not confined to monomial matrices. For the actual thirteen-frame residual, the tangent dimension is $`80+2\sum_H r_H`$ at every unit phase. At good phases, removing the 52-dimensional automorphism orbit leaves dimension 28. The actual symmetry representation on this quotient is isomorphic to
```math
(\mathfrak s/\mathfrak t)\oplus\mathfrak z_{\mathfrak s}(\tau),
```
where $`\mathfrak s\cong\mathfrak{so}(8)`$ is the actual diagonal fixer, $`\mathfrak t`$ its common Cartan subalgebra, and $`\tau`$ the specified adjoint-torus element. This is a noncanonical real representation isomorphism preserving the four marked character types. It gives neither a Lie bracket nor a $`\mathrm{Spin}(8)`$ action on the moduli space.

The family construction keeps the left $`SU(3)`$ and the two torus parameters after removing the common-right $`SU(3)`$ gauge. In the explicit maps, `preMap` has left, right and torus variables, while `rawMap62` sets the right variable to zero and adds the 52-dimensional automorphism chart. The quartet-fixing $`SU(3)`$ itself is automorphism gauge and does not generate a deformation family modulo automorphisms.

At each good phase, the four constructed real families are smooth of dimension 62 before removing the orbit and meet in a smooth 56-dimensional family. Simultaneous analytic coordinates give four ten-dimensional families in a labelled local slice, with common dimension four. At phases in $`\mathcal G`$, the complex analytic local algebra of the original equations has Krull dimension 62 and ordinary Hilbert–Samuel multiplicity four. Its four components of maximal dimension are exactly the complexifications of those constructed families, each generically reduced. This does not classify smaller complex components, embedded structure, or the full complex support.

The real conclusion is stronger. At every good phase, the *entire* local real zero germ is the constructed union. Its labelled normal-slice germ is homeomorphic to
```math
\mathbb R^4\times\left(\mathbb R_0^6\cup\mathbb R_1^6\cup\mathbb R_2^6\cup\mathbb R_3^6\right),
```
where the four six-dimensional axes occupy independent blocks of $`\bigoplus_{i=0}^3\mathbb R_i^6`$. The four-dimensional factor is the actual common family. Every nearby real solution of the defining equations lies in this union. Arbitrary nearby ambient configurations need not satisfy those equations.

The ambient normal slice has dimension 1,001. Its residual derivative has a 28-dimensional kernel at good phases, while each solution branch has dimension ten. A derivative kernel alone does not determine the dimension or smoothness of a zero set. Here the nonlinear equations obstruct mixed transverse directions, and the real normal-form theorem determines the actual solution germ.

More precisely, let $`S_\xi`$ be the saturation under actual Albert automorphisms of the four slice families restricted to the neighborhoods supplied by the theorem. There are an open neighborhood $`U_\xi`$ of the whole orbit of $`P(\xi)`$ and $`C_\xi>0`$ such that
```math
\mathrm{dist}(y,S_\xi)^2\le C_\xi\|F(y)\|,
\qquad y\in U_\xi,
```
and $`F(y)=0`$ there exactly when $`y\in S_\xi`$. Writing the second configuration metric as $`d_{\mathrm{tr}}(x,y)^2=\sum_{i=1}^{39}\langle x_i-y_i,x_i-y_i\rangle`$, its distance to $`S_\xi`$ satisfies the same bound with constant $`2116C_\xi`$. Thus the displayed squared-distance estimate is a Hölder estimate with exponent one-half on distance itself. For either metric, no estimate $`\mathrm{dist}(y,S_\xi)\le C\|F(y)\|^\alpha`$ holds on a neighborhood of $`P(\xi)`$ for any $`\alpha>1/2`$. This sharpness is an ambient statement. Neighborhoods and constants may depend on the phase; uniform conditioning near excluded phases is not asserted.

After forgetting labels and quotienting by automorphisms, local dimension ten holds at every phase in $`\mathcal G`$. Here *local dimension ten* means that every open neighborhood of the corresponding code class has small inductive dimension at least ten, and some open neighborhood has dimension exactly ten. The finite quotient may merge labelled components. Phases in $`\mathcal G`$ accumulate at the all-one phase, and every neighborhood of the original code contains a nonempty open ten-dimensional Euclidean patch. Consequently no neighborhood of the original code admits a twenty-four-dimensional Euclidean atlas. This addresses [Cohn–Kumar–Minton’s Conjecture 8.4, arXiv PDF page 50](https://arxiv.org/pdf/1308.3188v4#page=50). No nonlinear classification of the resonant original germ is needed or claimed.

## Separate exact-frame overlap-loss corollary

For thirteen canonically labelled exact frames, put $`B_{ij}=\langle P_i,P_j\rangle`$ and let $`\delta`$ contain the 702 cross-frame deviations $`B_{ij}-1/3`$. Sum over unordered distinct **index** pairs, without presupposing distinct point values. If $`\phi:\mathbb R\to\mathbb R`$ satisfies $`\phi|_I\in C^2(I)`$, with $`I`$ open and convex, $`1/3\in I`$, and $`0<m\le\phi''\le M`$ throughout $`I`$, then
```math
\frac m2\sum\delta^2\le
\sum_{i<j}\phi(B_{ij})-\bigl[39\phi(0)+702\phi(1/3)\bigr]
\le\frac M2\sum\delta^2
```
whenever all cross overlaps lie in $`I`$. The 39 within-frame contributions are fixed; differentiability near zero is not required. For every good phase, a sufficiently small open neighborhood of its whole orbit makes overlap-domain membership automatic. On exact frames in that neighborhood, the loss gap is at least $`c_\xi\mathrm{dist}(y,T_\xi)^4`$, with $`c_\xi>0`$, for both stated metrics, where $`T_\xi`$ is the localized saturation of the four constructed families supplied by this corollary. Its neighborhood witnesses need not be literally those chosen in a separate application of the real theorem.

A uniform positive lower bound on the second derivative of the overlap potential is essential; strict convexity alone is insufficient. The corollary supplies a lower bound, not a sharp exponent within the exact-frame constraint. It is separate from the main deformation statements.


## Sketch of proof

The fixed-quartet equations first reduce the problem to ordinary complex matrices. The native Albert-to-Tits equivalence preserves the product and trace, so the reduction describes the actual compact algebra, not a substitute model. Solving the anchored purity equations yields $`SU(3)`$; frame orthogonality gives the central triples, and cross-frame complementarity becomes complex trace orthogonality. Keeping representatives and outcome order explicit makes the common-right gauge faithful.

A Fourier transform in the finite clock index then solves the unrestricted linearized matrix equations. Its exceptional coefficients vanish precisely at the cubic resonance conditions above. Transport through all four marked subalgebras gives the full native tangent space. The actual diagonal fixer and its root decomposition identify these resonance conditions with the opposite-root pairs of $`D_4`$. Matching the marked character multiplicities constructs the stated noncanonical representation isomorphism; the native triality calculation identifies the diagonal fixer and its root data. Neither step equips the moduli space with a Lie bracket or a $`\mathrm{Spin}(8)`$ action.

The four fixed-quartet constructions provide actual solution families through the retained left and torus parameters, followed by automorphism saturation. Their common tangent directions and independent transverse directions give simultaneous analytic coordinates. The orbit chart removes the 52 automorphism directions. At good phases this leaves four six-dimensional blocks and their common four-dimensional factor, explaining both the ten parameters on a family and the twenty-eight infinitesimal parameters of their union.

Two arguments control what the families might miss. For the complex germ, the selected Jacobian minor and the exact obstruction relations bound the growth of finite jets. Passing to the actual convergent local algebra gives dimension 62 and multiplicity four. The four known smooth complexified families already contribute four distinct top components of that dimension. The multiplicity comparison leaves no additional component of maximal dimension and forces generic reducedness along each one. This argument allows smaller complex components.

For the real germ, the residual is expressed in the simultaneous family coordinates and reduced along its nonsingular range directions. The transverse quadratic zero set is exactly the union of the four axes. A reusable supported-stress criterion, with $`C^2`$ regularity and exact sheet vanishing as hypotheses, upgrades this quadratic description to the full local equation. Hypothetical counterexamples are normalized first toward an axis and then in a normal direction to it. Along-sheet covectors annihilate the relevant first derivatives, while their quadratic values are strictly positive on the remaining possible normal limits. The covector field is continuous along the sheet for each fixed unit limiting direction. Positivity is required on the normal directions satisfying the linearized quadratic constraint, not on arbitrary directions. Taylor expansion then contradicts the counterexample. The same argument gives the squared-distance estimate. Exact native stress identities discharge the criterion’s assumptions for the original residual, and actual automorphism transport extends the estimate to an orbit neighborhood.

Ambient sharpness uses a stationary homogeneous quadratic residual combination and an actual tangent direction on which it is nonzero. Along the corresponding straight line, distance from the full zero set is bounded below linearly while the residual is bounded above quadratically. This rules out every residual exponent greater than one-half. It does not supply a curve of exact frames.

Finally, the sharp pure-point code bound and its equality case identify tight 39-point codes with thirteen complementary frames. Local constancy of their labelled frame partition permits the native code-to-frame comparison. Finite compensated stabilizers act on the actual slice. An invariant compatible metric, orbit-type local isometries, small-inductive closed-sum results and Euclidean normalization give the ten-dimensional upper bound; actual open ten-dimensional patches give the lower bound. Transport through the native code quotient proves the stated local dimension. Accumulation at the all-one phase and invariance of Euclidean dimension exclude the proposed twenty-four-dimensional manifold neighborhood. These topological steps concern the actual quotient topology, not only a vector-space dimension count.

On the separately imposed exact-frame constraint, the sum of cross overlaps cancels the linear term in Taylor expansion of the loss. The bounds on the potential's second derivative compare the loss gap with the sum of squared overlap errors. Combining that comparison with the real distance estimate gives a quartic lower bound. Continuity of the finitely many cross overlaps permits shrinking the whole-orbit neighborhood to the prescribed overlap domain.

## Dense proof for AI agents

Albert–Tits $`(\circ,\mathrm{tr})`$-equivalence $`\Rightarrow`$ quartet-pure states $`\simeq SU(3)`$, central triples (both orientations), frame complementarity $`\Leftrightarrow\mathrm{Tr}(U^*V)=0`$, common-right gauge, embedded $`PSU(3)\times T^2`$; Fourier $`\Rightarrow T_d\simeq\mathbb R^6\oplus\mathbb C^6\oplus\mathbb C^{\{j:d_j^3=1\}}`$. $`\forall\xi\in(S^1)^4:\dim\mathcal T_\xi=80+2\sum_Hr_H,\ \dim\mathcal O_\xi=52,\ \mathcal T_\xi/\mathcal O_\xi\simeq_K(\mathfrak s/\mathfrak t)\oplus\mathfrak z_{\mathfrak s}(\tau(\xi))`$ (real linear). $`\mathcal N=\{\texttt{IsGoodPhase}\},\ \mathcal G=\mathcal N\cap\texttt{nativePivotLocus}`$; nonzero native pivot polynomial $`\Rightarrow\mathcal G`$ nonempty/open/dense. On $`\mathcal N`$: actual simultaneous family/orbit charts, dimensions $`62/56\rightarrow10/4`$, range reduction. Criterion: real normed $`C,Z`$, finite-dimensional real inner-product $`E=\bigoplus_{i\in\iota}^{\perp}W_i`$, finite $`\iota`$, open $`U\ni0`$, $`f:C\times E\to Z`$, $`f\in C^2(U)`$, $`f|_{U\cap(C\times W_i)}=0`$, $`Q_f^{-1}(0)=\bigcup_iW_i`$; $`\forall i,\ w\in W_i,\|w\|=1,\ \exists`$ $`V_{i,w}\ni0`$ open in $`U\cap(C\times W_i)`$, $`\ell_{i,w}\in C^0(V_{i,w},Z^*)`$, $`\ell_{i,w}(p)D_{W_i^\perp}f(p)=0\ (p\in V_{i,w})`$, $`\ell_{i,w}(0,0)Q_f(n)>0\ \forall0\ne n\in W_i^\perp\cap\ker DQ_f(w)`$. Two normal limits $`\Rightarrow f^{-1}(0)=C\times\bigcup_iW_i`$ locally, $`\mathrm{dist}(u,\bigcup_iW_i)^2\le M\|f(c,u)\|`$. Native reproduction/equilibrium/anchor/covariance identities $`\Rightarrow`$ criterion on $`\mathcal N`$; chart bounds + metric comparison + automorphism saturation $`\Rightarrow\forall\xi\in\mathcal N\ \exists U_\xi\text{ open},C_\xi>0:\mathrm{Orb}(P(\xi))\subset U_\xi,\ \forall y\in U_\xi,\ \mathrm{dist}(y,S_\xi)^2\le C_\xi\|F(y)\|`$ in both metrics. Ambient stationary-quadratic/tangent witness: $`\mathrm{dist}\gtrsim|t|,\ \|F\|=O(t^2)\Rightarrow\alpha\le1/2`$. On $`\mathcal G`$: original-ideal jet bounds + recurrence + four regular branch quotients $`\Rightarrow H_\xi(n)=p_\xi(n)\ (n\gg0),\ \dim A_\xi=\deg p_\xi=62,\ \mathrm{lc}(p_\xi)=4/62!`$; distinct branch kernels $`P_i`$, $`R/P_i\simeq\mathcal O_{\mathbb C^{62},0}`$, $`\mathrm{Min}_{62}(A_\xi)=\{P_i/I_\xi:i<4\}`$, $`I_\xi R_{P_i}=P_iR_{P_i}`$. Pure-point overlap bound $`\Rightarrow N\le39,\ N=39\Leftrightarrow13`$ complementary frames; partition constancy + finite compensated stabilizer + compatible quotient metric + orbit-type local isometries + countable closed-sum/locality + Euclidean normalization $`\Rightarrow\forall\xi\in\mathcal G:\ [\forall V\ni[P(\xi)]\text{ open},\mathrm{ind}V\ge10]\land[\exists V\ni[P(\xi)]\text{ open},\mathrm{ind}V=10]`$, open ten-patches in every such neighborhood; $`\mathcal G`$-code accumulation at $`\xi=1`$ + invariance of dimension $`\Rightarrow`$ no $`24`$-manifold neighborhood there. Separately, exact frames, $`\phi:\mathbb R\to\mathbb R,\ \phi|_I\in C^2(I)`$, open convex $`I\ni1/3`$, $`0<m\le\phi''\le M`$: cross-overlap cancellation $`\Rightarrow\frac m2\sum\delta^2\le\Delta_\phi\le\frac M2\sum\delta^2,\ \|F\|^2\le\sum\delta^2\Rightarrow\Delta_\phi\ge c_\xi\mathrm{dist}(\,\cdot\,,T_\xi)^4`$ locally near the whole orbit, both metrics, $`\xi\in\mathcal N`$; ambient sharpness supplies no exact-frame sharpness.

## Theorem map

[Challenge.lean](Challenge.lean) states the 29 targets below. [Solution.lean](Solution.lean) assembles their native proofs and adapters without importing Challenge. [comparator.json](comparator.json) selects all 29 theorem names and permits no replacement bodies for concrete definitions. Names in the middle column are Challenge targets, qualified by the namespace shown. The linked source supplies the native proof or its exact adapter.

| Result | Challenge targets | Native provider and adapter |
|---|---|---|
| Sharp code bound and frame equality | `CKM.NativeTightCodeConsumer.code_bound`, `code_bound_sharp`, `tight_code_iff_frames` | [TCConsumer](Proofs/TCConsumer.lean) |
| Reusable real criterion | `SupportedStress.supported_stress_local_criterion` | [SupportedStressCriterionV3](Proofs/SupportedStressCriterionV3.lean) |
| Exact-frame loss sandwich | `CKM.NativeExactFrameEnergy.native_energy_sandwich` | [EFMain](Proofs/EFMain.lean) |
| Anchored purity and native coordinates | `CompactAlbert.native_idempotent_iff_scaled_specialUnitary_of_literal_quartet_readouts`, `nativeComplementaryPoint_scaled_hidden_inverse` | [LiteralNativeQuartetReadouts](Proofs/LiteralNativeQuartetReadouts.lean), [NativeComplementaryDictionary](Proofs/NativeComplementaryDictionary.lean) |
| Ordered frames and complex trace | `CompactAlbert.native_complementary_frame_iff_exists_central_order`, `native_ordered_central_triples_overlap_iff_hilbertSchmidt` | [NativeComplementaryDictionary](Proofs/NativeComplementaryDictionary.lean) |
| Literal tight code | `CKM.NativeUnlabelledSlice.literalCfg_mem_tightLocus` | [ULCodeDict](Proofs/ULCodeDict.lean) |
| Actual original-code accumulation | `Option2StatementCode.exists_goodAvoid_codeClass_mem_nhds_one` | [PairingCode](Proofs/PairingCode.lean), [GPCode](Proofs/GPCode.lean) |
| State dictionary, faithful gauge and nine-frame array | `Option2StatementA1.state_equivalence`, `quartet_fixer_classification`, `quartet_fixer_converse`, `nine_frame_array` | [WrappersA124](Proofs/WrappersA124.lean), [NativeActualStateEquivalence](Proofs/NativeActualStateEquivalence.lean), [NativeAnchorFixerClassification](Proofs/NativeAnchorFixerClassification.lean), [NativeActualNineFrameDictionary](Proofs/NativeActualNineFrameDictionary.lean) |
| Original-code obstruction | `Option2StatementCode.originalCode_no_open24_chart`, `originalCode_no_charted24_neighborhood` | [PairingCodeNoManifold](Proofs/PairingCodeNoManifold.lean), [NativeOriginalCodeNoManifold24](Proofs/NativeOriginalCodeNoManifold24.lean) |
| All-unit native tangent law | `Option2StatementA3.finrank_original_derivative_kernel` | [PairingA3](Proofs/PairingA3.lean), [A3Interfaces](Proofs/A3Interfaces.lean) |
| Unrestricted matrix first order | `Option2StatementA3Matrix.unrestricted_matrix_normal_form`, `firstOrder_dimension`, `resonance_count_cases` | [PairingA3Matrix](Proofs/PairingA3Matrix.lean), [PairingA3Numbers](Proofs/PairingA3Numbers.lean), [ThreeCycleDimension](Proofs/ThreeCycleDimension.lean) |
| Embedded normalized family | `Option2StatementA2.full_A2` | [WrappersA124](Proofs/WrappersA124.lean), [NativeNormalizedA2Headline](Proofs/NativeNormalizedA2Headline.lean) |
| Simultaneous native families | `Option2StatementA5Slice.native_A5_geometry` | [PairingA5Geometry](Proofs/PairingA5Geometry.lean), [A5Main](Proofs/A5Main.lean) |
| Actual triality representation | `Option2StatementA4.full_A4` | [WrappersA124](Proofs/WrappersA124.lean), [A4Main](Proofs/A4Main.lean) |
| Complex local algebra on the selected locus | `Option2StatementA6.native_A6` | [PairingA6](Proofs/PairingA6.lean), [NativePhaseA6](Proofs/NativePhaseA6.lean) |
| Unlabelled local dimension | `Option2StatementCode.native_A7_local_dimension` | [PairingA7](Proofs/PairingA7.lean), [NativeLocalDimensionTen](Proofs/NativeLocalDimensionTen.lean) |
| Real exhaustion, sharp bound and normal form | `Option2StatementR.native_real_endpoint`, `normal_form_exists` | [PairingR](Proofs/PairingR.lean), [NativePhaseRealEndpoint](Proofs/NativePhaseRealEndpoint.lean), [NativePhaseNormalForm](Proofs/NativePhaseNormalForm.lean) |
| Separate quartic loss floor | `Option2StatementR.native_exact_frame_quartic_stability_near_orbit` | [PairingR](Proofs/PairingR.lean), [NativeExactFrameStability](Proofs/NativeExactFrameStability.lean) |

The relative local constancy of the recovered frame partition is supplied by `partition_locally_constant` and `partition_native_nhds` in [TCConsumer](Proofs/TCConsumer.lean). The complete normal-zero model and the finite-stabilizer dimension argument are additional proof dependencies, not assumptions inserted into the Challenge targets. The shared concrete definitions in [PairingDefinitions](Proofs/PairingDefinitions.lean) retain the native coordinate, family, residual and quotient meanings.

Synopsis symbols; $`\mathrm{ind}`$ denotes small inductive dimension.

| Symbols | Exact native definitions |
|---|---|
| $`\mathcal T_\xi:=\ker D_{\mathbb R}F(P(\xi))`$, $`\mathcal O_\xi:=\{(D(P_i(\xi)))_i:D\in\mathrm{Der}_{\mathbb R}J\}`$, in native coordinates | $`\mathcal T_\xi`$: $`\texttt{CKM.NativeFirstOrder.tangentSpace}`$ ([A3Interfaces](Proofs/A3Interfaces.lean)); $`\mathcal O_\xi`$ and its inclusion in $`\mathcal T_\xi`$: $`\texttt{CKM.NativeIntrinsicTriality.orbitSpace}`$ ([A4Orbit](Proofs/A4Orbit.lean)); quotient action: $`\texttt{tangentQuotAction}`$ ([A4Quotient](Proofs/A4Quotient.lean)). |
| $`Q_f(u):=\tfrac12D_u^2f(0,0)[u,u]=\tfrac12D^2f(0,0)[(0,u),(0,u)]`$, $`\ell_{i,w}:V_{i,w}\to Z^*`$ | $`\texttt{SupportedStress.transverseQuadraticPart}`$ ([FirstBlockLimitV3](Proofs/FirstBlockLimitV3.lean)); the fields $`\ell_{i,w}`$ and their positivity are hypothesis $`\texttt{hstress}`$ of $`\texttt{supported_stress_local_criterion}`$ ([SupportedStressCriterionV3](Proofs/SupportedStressCriterionV3.lean)); $`Z^*`$ is the continuous real dual. |
| $`R:=\mathcal O_{\mathbb C^{1053},0}`$, $`I_\xi:=(F_{\mathbb C}(P(\xi)+z))`$, $`A_\xi:=R/I_\xi`$, $`\mathfrak m_\xi:=\mathfrak m_{A_\xi}`$, $`H_\xi(n):=\mathrm{length}_{A_\xi}(A_\xi/\mathfrak m_\xi^{n+1})`$ | $`R`$: $`\texttt{ConvergentResidualJets.GermRing}`$ ([ConvergentResidualJetMap](Proofs/ConvergentResidualJetMap.lean)); $`I_\xi`$: $`\texttt{nativePhaseAnalyticIdeal}`$ ([NativePhaseJetBound](Proofs/NativePhaseJetBound.lean)); $`H_\xi`$: $`\texttt{nativePhaseIntrinsicJetLength}`$ ([NativePhaseHilbertSamuelBounds](Proofs/NativePhaseHilbertSamuelBounds.lean)); eventual polynomial: $`\texttt{native_phase_unique_hilbertSamuel_polynomial}`$ ([NativePhaseOrdinaryMultiplicity](Proofs/NativePhaseOrdinaryMultiplicity.lean)). |

## Verification

From the repository root, the ordinary build commands are

```sh
lake build Solution
lake build Challenge
```

Use the exact toolchain and dependency revisions in [lean-toolchain](lean-toolchain) and [lake-manifest.json](lake-manifest.json). These commands compile the proof and statement targets separately. Compilation of Challenge, whose designated targets are theorem holes, does not prove those targets.

Commit `5c32905c537928d749b2e9b7440baf7bbeb93ee0` passed the [full official preflight](https://github.com/macgregor-sudo/tight-39-code/actions/runs/40793588577) and [Palomar mechanical verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/40813809750). All 29 selected targets passed exact Challenge–Solution statement/definition matching, permitted-axiom checks, and verification by Lean and NanoDa. Con-ron recorded an allowed capacity decline and is not claimed as a successful checker. The 993-line Challenge contains designated theorem holes that specify statements, not proofs.

This revision changes only prose and metadata; Lean sources and build configuration are unchanged from that verified commit. Its own full preflight and editorial review remain pending. [SOURCE-PROVENANCE.json](SOURCE-PROVENANCE.json) records the source selection and prior verification scope. A mechanical pass is not permanent registration.

For Palomar submission, the manually dispatched [preflight workflow](.github/workflows/palomar.yml) calls the complete official pipeline at a fixed revision, in `full` mode with the `palomar-standard-v1` profile, for the dispatched commit and `comparator.json`. It includes statement matching and proof verification. Submission requires a mechanical report with `status: pass`; the local build alone does not establish that result. A passing full-workflow report is still required for this release.

## Sources, attribution and scope

The original configuration, four-phase construction and conjecture are due to Cohn, Kumar and Minton, [*Optimal simplices and codes in projective spaces*, §8.2](https://arxiv.org/pdf/1308.3188v4). Shift-and-multiply unitary error bases are classical; the cited [Werner construction](https://arxiv.org/pdf/quant-ph/0003070v1) is a construction input, not a classification of all bases. The overlap-potential comparison is the standard Taylor/strong-convexity estimate; see Boyd–Vandenberghe, *Convex Optimization*, §9.1.2, equations (9.8) and (9.13). The small-inductive dimension arguments formalize classical dimension theory, including Engelking, *Dimension Theory* (1978), Theorem 1.5.3 and Corollary 1.5.4 on closed sums, and Theorems 1.8.1–1.8.2 on cube separation and Euclidean dimension. The no-chart conclusion uses invariance of Euclidean dimension through [NativeOriginalCodeNoManifold24](Proofs/NativeOriginalCodeNoManifold24.lean). These classical inputs and their formal implementations carry no first-priority claim here.

Related work includes Gerald Höhn’s [*Definite integral Albert algebras: arithmetic and finite geometry*, arXiv:2609.27550v1, §7.2, Remark 7.3](https://arxiv.org/pdf/2609.27550v1#page=24). The cited [companion paper, arXiv:2609.25086v1, Lemmas 5.2–5.3 and equation (53), pp. 21–22](https://arxiv.org/pdf/2609.25086v1#page=22), reconstructs the traceless Albert product from the third moment of a Cayley-plane projective 3-design and extends angle-preserving bijections between such designs to Albert automorphisms. Its tight 5-design application concerns 819 points; the present deformation problem concerns the 39-point CKM code. These results supply related geometric context and are not dependencies of the deformation or residual-distance proofs presented here.

The source package uses Lean and Mathlib; the exact toolchain and dependency revisions belong to [lean-toolchain](lean-toolchain) and [lake-manifest.json](lake-manifest.json). Original code is offered under [Apache-2.0](LICENSE) to the extent of rights held or authorized. Mathematical attribution is distinct from permission to redistribute code. Applicable upstream Apache-2.0 and MIT grants, source headers, notices and adaptation credits are recorded in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md), [LICENSES](LICENSES/) and [SOURCE-PROVENANCE.json](SOURCE-PROVENANCE.json) and must be retained. This does not relicense third-party material or assert exclusive copyright in AI-generated output.

The result is local deformation mathematics. It asserts no physical model, dynamics, phase-selection principle, global classification, computable radius, unique nearest family, or uniform estimate at excluded phases. Smaller complex components and nonlinear resonant germs remain unclassified even though the good-phase real germ is exhausted.


## Disclosure

Except for attributed third-party material, all text and code are AI-generated under Robert R. MacGregor’s direction. Robert is an amateur who welcomes collaboration (macgregor@gmail.com).
