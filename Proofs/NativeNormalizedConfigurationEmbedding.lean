module
public import NativeNormalizedOriginalF
public import Mathlib.Analysis.Analytic.Constructions

@[expose] public section
noncomputable section
namespace CompactAlbert

open scoped Topology
open UnitaryErrorBases.ThreeCycleNormalized
open NativePolynomial NativePolynomial.PartialAction
open NativePolynomial.ConfigurationResiduals
open QuadraticCertificate.ExactCKMConfiguration

/-- The linear part of literal insertion: zero at the twelve anchors. -/
def nativeCompletionInsertionLinear : (Fin 9 → Fin 3 → Fin 27 → ℝ) →L[ℝ] Configuration ℝ where
  toFun U i := if hi : i.val < 12 then 0 else
    U ⟨i.val / 3 - 4, by omega⟩ ⟨i.val % 3, by omega⟩
  map_add' U V := by
    funext i
    by_cases hi : i.val < 12 <;> simp [hi]
  map_smul' a U := by
    funext i
    by_cases hi : i.val < 12 <;> simp [hi]
  cont := by
    apply continuous_pi
    intro i
    by_cases hi : i.val < 12
    · simpa only [dite_eq_left hi] using (continuous_const : Continuous (fun _ : Fin 9 → Fin 3 → Fin 27 → ℝ => (0 : Fin 27 → ℝ)))
    · simpa only [dite_eq_right hi, Function.comp_def] using!
        (continuous_apply (⟨i.val % 3, by omega⟩ : Fin 3)).comp
          (continuous_apply (⟨i.val / 3 - 4, by omega⟩ : Fin 9))

/-- The fixed native anchor coordinates, with zero outside the first twelve. -/
def nativeAnchorCoordinates : Configuration ℝ :=
  fun i => if i.val < 12 then upperCoordinates (nativePoint i) else 0

/-- Exact affine insertion into the original point-first configuration space. -/
def insertNativeAnchorCoordinates (U : Fin 9 → Fin 3 → Fin 27 → ℝ) : Configuration ℝ :=
  nativeAnchorCoordinates + nativeCompletionInsertionLinear U

/-- Continuous linear readout at the literal outside-point labels. -/
def nativeCompletionReadout : Configuration ℝ →L[ℝ] (Fin 9 → Fin 3 → Fin 27 → ℝ) :=
  ContinuousLinearMap.pi fun r => ContinuousLinearMap.pi fun k =>
    ContinuousLinearMap.proj (⟨12 + 3 * r.val + k.val, by omega⟩ : Fin 39)

theorem nativeCompletionInsertionLinear_completion (U : Fin 9 → Fin 3 → Fin 27 → ℝ)
    (r : Fin 9) (k : Fin 3) :
    nativeCompletionInsertionLinear U ⟨12 + 3 * r.val + k.val, by omega⟩ = U r k := by
  have hi : ¬ 12 + 3 * r.val + k.val < 12 := by omega
  change (if h : 12 + 3 * r.val + k.val < 12 then 0 else
    U ⟨(12 + 3 * r.val + k.val) / 3 - 4, by omega⟩
      ⟨(12 + 3 * r.val + k.val) % 3, by omega⟩) = U r k
  rw [dite_eq_right hi]
  congr 1 <;> apply Fin.ext <;> dsimp <;> omega

theorem insertNativeAnchorCoordinates_anchor (U : Fin 9 → Fin 3 → Fin 27 → ℝ)
    (i : Fin 39) (hi : i.val < 12) :
    insertNativeAnchorCoordinates U i = upperCoordinates (nativePoint i) := by
  simp [insertNativeAnchorCoordinates, nativeAnchorCoordinates, nativeCompletionInsertionLinear, hi]

theorem insertNativeAnchorCoordinates_completion (U : Fin 9 → Fin 3 → Fin 27 → ℝ)
    (r : Fin 9) (k : Fin 3) :
    insertNativeAnchorCoordinates U ⟨12 + 3 * r.val + k.val, by omega⟩ = U r k := by
  have hi : ¬ 12 + 3 * r.val + k.val < 12 := by omega
  change nativeAnchorCoordinates _ + nativeCompletionInsertionLinear U _ = U r k
  rw [nativeCompletionInsertionLinear_completion]
  simp [nativeAnchorCoordinates, hi]

theorem nativeCompletionReadout_linear_leftInverse :
    Function.LeftInverse nativeCompletionReadout nativeCompletionInsertionLinear := by
  intro U
  funext r k
  exact nativeCompletionInsertionLinear_completion U r k

theorem nativeCompletionReadout_insertion_leftInverse :
    Function.LeftInverse nativeCompletionReadout insertNativeAnchorCoordinates := by
  intro U
  funext r k
  exact insertNativeAnchorCoordinates_completion U r k

theorem continuous_insertNativeAnchorCoordinates : Continuous insertNativeAnchorCoordinates :=
  continuous_const.add nativeCompletionInsertionLinear.continuous

theorem isClosedEmbedding_insertNativeAnchorCoordinates :
    Topology.IsClosedEmbedding insertNativeAnchorCoordinates :=
  nativeCompletionReadout_insertion_leftInverse.isClosedEmbedding
    nativeCompletionReadout.continuous continuous_insertNativeAnchorCoordinates

/-- Exact binding uses only the accepted anchor and completion readouts. -/
theorem insertNativeAnchorCoordinates_nativeNormalizedProjectiveFamily
    (x : SpecialUnitaryCenterQuotient × (Circle × Circle)) :
    insertNativeAnchorCoordinates (nativeNormalizedProjectiveFamily x) =
      nativeNormalizedProjectiveConfiguration x := by
  funext i
  by_cases hi : i.val < 12
  · rw [insertNativeAnchorCoordinates_anchor _ i hi,
      nativeNormalizedProjectiveConfiguration_anchor x i hi]
  · let r : Fin 9 := ⟨i.val / 3 - 4, by omega⟩
    let k : Fin 3 := ⟨i.val % 3, by omega⟩
    have he : (⟨12 + 3 * r.val + k.val, by omega⟩ : Fin 39) = i := by
      apply Fin.ext
      dsimp [r, k]
      omega
    rw [← he, insertNativeAnchorCoordinates_completion,
      nativeNormalizedProjectiveConfiguration_completion]

theorem isClosedEmbedding_nativeNormalizedProjectiveConfiguration :
    Topology.IsClosedEmbedding nativeNormalizedProjectiveConfiguration := by
  have h := isClosedEmbedding_insertNativeAnchorCoordinates.comp
    isClosedEmbedding_nativeNormalizedProjectiveFamily
  simpa only [Function.comp_def, insertNativeAnchorCoordinates_nativeNormalizedProjectiveFamily] using h

theorem analyticAt_insertNativeAnchorCoordinates (U : Fin 9 → Fin 3 → Fin 27 → ℝ) :
    AnalyticAt ℝ insertNativeAnchorCoordinates U :=
  analyticAt_const.add (nativeCompletionInsertionLinear.analyticAt U)

theorem insertNativeAnchorCoordinates_hasFDerivAt (U : Fin 9 → Fin 3 → Fin 27 → ℝ) :
    HasFDerivAt insertNativeAnchorCoordinates nativeCompletionInsertionLinear U :=
  nativeCompletionInsertionLinear.hasFDerivAt.const_add nativeAnchorCoordinates

theorem insertNativeAnchorCoordinates_fderiv_injective (U : Fin 9 → Fin 3 → Fin 27 → ℝ) :
    Function.Injective (fderiv ℝ insertNativeAnchorCoordinates U) := by
  rw [(insertNativeAnchorCoordinates_hasFDerivAt U).fderiv]
  exact nativeCompletionReadout_linear_leftInverse.injective

/-- The original pack, with its unchanged point-first Fin1053 variable order. -/
def nativeConfigurationPackLinear : Configuration ℝ →L[ℝ] (Fin 1053 → ℝ) where
  toFun := pack
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by
    apply continuous_pi
    intro v
    exact (continuous_apply _).comp (continuous_apply _)

/-- Readout via the original variableIndex, rather than a second flattening convention. -/
def nativeConfigurationUnpackLinear : (Fin 1053 → ℝ) →L[ℝ] Configuration ℝ :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun c =>
    ContinuousLinearMap.proj (variableIndex i c)

theorem nativeConfigurationUnpackLinear_leftInverse :
    Function.LeftInverse nativeConfigurationUnpackLinear nativeConfigurationPackLinear := by
  intro C
  funext i c
  exact pack_variableIndex C i c

theorem isClosedEmbedding_nativeConfigurationPack : Topology.IsClosedEmbedding (pack (S := ℝ)) :=
  nativeConfigurationUnpackLinear_leftInverse.isClosedEmbedding
    nativeConfigurationUnpackLinear.continuous nativeConfigurationPackLinear.continuous

/-- Closed embedding into all 1053 original polynomial variables. -/
theorem isClosedEmbedding_pack_nativeNormalizedProjectiveConfiguration :
    Topology.IsClosedEmbedding (fun x => pack (nativeNormalizedProjectiveConfiguration x)) :=
  isClosedEmbedding_nativeConfigurationPack.comp
    isClosedEmbedding_nativeNormalizedProjectiveConfiguration

/-- The continuous-linear derivative of the literal packed affine insertion. -/
def packedNativeCompletionInsertionLinear :
    (Fin 9 → Fin 3 → Fin 27 → ℝ) →L[ℝ] (Fin 1053 → ℝ) :=
  nativeConfigurationPackLinear.comp nativeCompletionInsertionLinear

theorem analyticAt_pack_insertNativeAnchorCoordinates (U : Fin 9 → Fin 3 → Fin 27 → ℝ) :
    AnalyticAt ℝ (fun V => pack (insertNativeAnchorCoordinates V)) U :=
  nativeConfigurationPackLinear.analyticAt _ |>.comp (analyticAt_insertNativeAnchorCoordinates U)

theorem pack_insertNativeAnchorCoordinates_hasFDerivAt (U : Fin 9 → Fin 3 → Fin 27 → ℝ) :
    HasFDerivAt (fun V => pack (insertNativeAnchorCoordinates V))
      packedNativeCompletionInsertionLinear U :=
  nativeConfigurationPackLinear.hasFDerivAt.comp U (insertNativeAnchorCoordinates_hasFDerivAt U)

theorem packedNativeCompletionInsertionLinear_injective :
    Function.Injective packedNativeCompletionInsertionLinear :=
  nativeConfigurationUnpackLinear_leftInverse.injective.comp
    nativeCompletionReadout_linear_leftInverse.injective

end CompactAlbert
