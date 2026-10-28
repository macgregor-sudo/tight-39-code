module

public import GSQuot

@[expose] public section

/-!
# The actual compact automorphism group and the native local slice: endpoint bundle

`native_group_slice ξ hξ` collects, for every unit phase `ξ` (resonances included; the only
hypothesis is `IsUnitPhase ξ := ∀ a, Complex.normSq (ξ a) = 1`):

1. **Full group, compactness and identity chart.** `G = autC` is exactly the set of bijective
   real-linear native maps preserving `Glennie.jordan`; it is compact and closed, cut out by the
   product and trace-pairing equations; unit, trace and pairing preservation are derived, and `G` is
   closed under `1`, products and inverses (`Ring.inverse`). The chart
   `groupChart = exp` on the 52-dimensional `derC` (= the triality block's `jordanDerivations`) is
   analytic with tangent the inclusion, and near the identity its image is all of `G`, with an
   analytic inverse.
2. **Free orbit.** The 39 literal points span `J`; the labelled stabilizer of `P = literalCfg ξ` is
   trivial; the derivative of the action is `D ↦ (i ↦ D (P i))`, injective, with image A4's
   `orbitSpace ξ` of dimension 52.
3. **Product chart.** `N(ξ) = O(ξ)ᗮ` (finite-sum trace inner product) has dimension 1001 and
   complements `O(ξ)`; `Θ_ξ (D, n) = χ(D) • (P + n)` is analytic with differential
   `(D, n) ↦ D(P) + n` at `(0, 0)`; its inverse-function partial homeomorphism has an analytic
   inverse near `P`.
4. **Original equations.** Off shell, `F (A • C) = Λ(A) (F C)` for all `A ∈ G` and all
   configurations, with `Λ` acting by `A` on idempotency and frame-sum blocks and trivially on trace
   and pair-overlap rows; `Λ` is invertible on `G` and analytic in `A`;
   `F (Θ (D, n)) = 0 ↔ F (P + n) = 0`; `F P = 0`.
5. **Local orbit relation and quotient germ.** Near `P`, slice points related by any element of `G`
   are equal; the restriction of the quotient map to the slice zero-set germ is an open embedding
   into the labelled orbit space of `{F = 0}` (quotient topology).
-/

noncomputable section

namespace CKM.NativeGroupSlice

open Glennie NativePolynomial CKM.NativeDerivationTriality CKM.NativeFirstOrder
  ConfigurationResidualIndices
open Option2.NativeStress.AnalyticDerivative (originalF)
open scoped Topology

attribute [local instance 100] LieRing.ofAssociativeRing

theorem native_group_slice (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    -- 1. the full group, its compactness and its identity chart
    (∀ A : CEnd, A ∈ autC ↔ Function.Bijective (coordEnd.symm A) ∧
      ∀ x y, coordEnd.symm A (jordan x y) = jordan (coordEnd.symm A x) (coordEnd.symm A y)) ∧
    IsCompact autC ∧
    IsClosed autC ∧
    autC = {A : CEnd | (∀ a b, A (prodC a b) = prodC (A a) (A b)) ∧
      ∀ a b, CoordinateMaps.coordinatePairing (A a) (A b) = CoordinateMaps.coordinatePairing a b} ∧
    (∀ A ∈ autC, A CoordinateMaps.coordinateUnit = CoordinateMaps.coordinateUnit ∧
      (∀ a, CoordinateMaps.coordinateTrace (A a) = CoordinateMaps.coordinateTrace a) ∧
      ∀ a b, CoordinateMaps.coordinatePairing (A a) (A b) = CoordinateMaps.coordinatePairing a b) ∧
    ((1 : CEnd) ∈ autC ∧ (∀ A ∈ autC, ∀ B ∈ autC, A * B ∈ autC) ∧
      ∀ A ∈ autC, Ring.inverse A ∈ autC ∧ A * Ring.inverse A = 1 ∧ Ring.inverse A * A = 1) ∧
    derC = jordanDerivations.toSubmodule.map coordEnd.toLinearMap ∧
    Module.finrank ℝ derC = 52 ∧
    HasStrictFDerivAt groupChart derC.subtypeL 0 ∧
    (∀ D, AnalyticAt ℝ groupChart D) ∧
    (∃ U : Set derC, ∃ W : Set CEnd, ∃ inv : CEnd → derC,
      IsOpen U ∧ (0 : derC) ∈ U ∧ IsOpen W ∧ (1 : CEnd) ∈ W ∧
      Set.InjOn groupChart U ∧ groupChart '' U = autC ∩ W ∧
      (∀ g ∈ autC ∩ W, inv g ∈ U ∧ groupChart (inv g) = g) ∧
      (∀ D ∈ U, inv (groupChart D) = D) ∧ AnalyticOnNhd ℝ inv W) ∧
    -- 2. the free orbit
    Submodule.span ℝ (Set.range (literalPoint ξ)) = ⊤ ∧
    (∀ A : CEnd, actC A (literalCfg ξ) = literalCfg ξ ↔ A = 1) ∧
    HasStrictFDerivAt (fun D : derC => actC (groupChart D) (literalCfg ξ))
      ((orbitMapC ξ).comp derC.subtypeL) 0 ∧
    Function.Injective (orbitMapC ξ) ∧
    orbitC ξ = CKM.NativeIntrinsicTriality.orbitSpace ξ ∧
    Module.finrank ℝ (orbitC ξ) = 52 ∧
    -- 3. the ambient analytic product chart
    Module.finrank ℝ (normalC ξ) = 1001 ∧
    IsCompl (orbitC ξ) (normalC ξ) ∧
    (∀ p, sliceDiff ξ hξ p = orbitMapC ξ p.1 + p.2) ∧
    HasStrictFDerivAt (sliceChart ξ) (sliceDiff ξ hξ : (derC × normalC ξ) →L[ℝ] Cfg) 0 ∧
    (∀ p, AnalyticAt ℝ (sliceChart ξ) p) ∧
    ⇑(slicePH ξ hξ) = sliceChart ξ ∧
    (0 : derC × normalC ξ) ∈ (slicePH ξ hξ).source ∧
    literalCfg ξ ∈ (slicePH ξ hξ).target ∧
    (∃ W ∈ 𝓝 (literalCfg ξ), W ⊆ (slicePH ξ hξ).target ∧ AnalyticOnNhd ℝ (slicePH ξ hξ).symm W) ∧
    -- 4. the original equations
    (∀ A ∈ autC, ∀ C, originalF (actC A C) = rowAction A (originalF C)) ∧
    (∀ A y i k, rowAction A y (fNumber (fId i k)) = A (fun k' => y (fNumber (fId i k'))) k) ∧
    (∀ A y i, rowAction A y (fNumber (fTrace i)) = y (fNumber (fTrace i))) ∧
    (∀ A y f k, rowAction A y (fNumber (fSum f k)) = A (fun k' => y (fNumber (fSum f k'))) k) ∧
    (∀ A y ij, rowAction A y (fNumber (fPair ij)) = y (fNumber (fPair ij))) ∧
    (∀ A ∈ autC, rowAction A * rowAction (Ring.inverse A) = 1 ∧
      rowAction (Ring.inverse A) * rowAction A = 1) ∧
    (∀ A, AnalyticAt ℝ rowAction A) ∧
    (∀ p, originalF (sliceChart ξ p) = rowAction (groupChart p.1) (originalF (literalCfg ξ + p.2))) ∧
    (∀ p, originalF (sliceChart ξ p) = 0 ↔ originalF (literalCfg ξ + p.2) = 0) ∧
    originalF (literalCfg ξ) = 0 ∧
    -- 5. the full local orbit relation and the quotient germ
    (∃ W ∈ 𝓝 (literalCfg ξ), ∀ s ∈ W ∩ sliceSet ξ, ∀ t ∈ W ∩ sliceSet ξ,
      ∀ A ∈ autC, actC A s = t → s = t) ∧
    (∃ W : Set Cfg, IsOpen W ∧ literalCfg ξ ∈ W ∧ Topology.IsOpenEmbedding (sliceToOrbit ξ W)) :=
  ⟨mem_autC_iff, isCompact_autC, isClosed_autC, autC_eq_closed,
    fun _ hA => ⟨autC_unit hA, autC_trace hA, autC_pairing hA⟩,
    ⟨one_mem_autOf prodC, fun _ hA _ hB => mul_mem_autOf hA hB,
      fun _ hA => ⟨inverse_mem_autOf hA, mul_inverse_of_mem_autOf hA⟩⟩,
    derC_eq_map, finrank_derC, hasStrictFDerivAt_groupChart,
    analyticAt_groupChart, exists_groupChart_local,
    CKM.NativeIntrinsicTriality.span_literalPoint ξ hξ, actC_literalCfg_eq_iff ξ hξ,
    hasStrictFDerivAt_orbit ξ, orbitMapC_injective ξ hξ, orbitC_eq_orbitSpace ξ, finrank_orbitC ξ hξ,
    finrank_normalC ξ hξ, isCompl_orbitC_normalC ξ hξ, sliceDiff_apply ξ hξ,
    hasStrictFDerivAt_sliceChart ξ hξ, analyticAt_sliceChart ξ, slicePH_coe ξ hξ,
    zero_mem_slicePH_source ξ hξ, literalCfg_mem_slicePH_target ξ hξ,
    exists_analyticOnNhd_slicePH_symm ξ hξ,
    fun _ hA C => originalF_actC hA C, rowAction_id, rowAction_trace, rowAction_sum, rowAction_pair,
    fun _ hA => rowAction_inverse hA, analyticAt_rowAction, originalF_sliceChart ξ,
    originalF_sliceChart_eq_zero_iff ξ, originalF_literalCfg ξ hξ,
    exists_local_orbit_injective ξ hξ, exists_sliceToOrbit_isOpenEmbedding ξ hξ⟩

end CKM.NativeGroupSlice
