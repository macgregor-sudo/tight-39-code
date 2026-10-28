module

public import BookNativeTangentBinding
public import BookNativeRealMapLinear
public import A5Rank
public import A5KLin
public import Mathlib.LinearAlgebra.Projection

@[expose] public section

/-!
Actual exact-seed Book directions projected into the actual normal kernel.
The remaining joint complement obligation is displayed explicitly below;
this file does not assert a Book/common-tangent equivalence.
-/
set_option Elab.async false
noncomputable section

namespace Option2.NativeStress.BookHT.NativeNormalKernelBridge

open TangentCoordinates CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open NativePolynomial QuadraticCertificate.ExactCKMConfiguration

/-- All twelve actual rational anchor phases are nonresonant. -/
theorem exactPhases_anchor_cube_ne_one (H : Fin 4) (j : UnitaryErrorBases.Index) :
    anchorPhases exactPhases H j ^ 3 ≠ 1 := by
  rw [Ne, Complex.ext_iff]
  fin_cases H <;> fin_cases j <;>
    norm_num [anchorPhases, exactPhases, pow_succ, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.inv_re, Complex.inv_im]

theorem exactPhases_good : IsGoodPhase exactPhases :=
  ⟨exactPhases_unit, exactPhases_anchor_cube_ne_one⟩

theorem exactPhases_native_dimensions :
    Module.finrank ℝ (fixQK exactPhases) = 4 ∧
      Module.finrank ℝ (tanN exactPhases) = 28 :=
  ⟨finrank_fixQK exactPhases_good, finrank_tanN exactPhases_good⟩

/-- Literal point-first unflattening of the supplied 1053 real coordinates. -/
def unpackNative : (Fin 1053 → ℝ) →L[ℝ] Cfg :=
  ContinuousLinearMap.pi fun p : Fin 39 =>
    ContinuousLinearMap.pi fun k : Fin 27 =>
      ContinuousLinearMap.proj (⟨27 * p.val + k.val, by omega⟩ : Fin 1053)

@[simp] theorem unpackNative_apply (x : Fin 1053 → ℝ) (p : Fin 39) (k : Fin 27) :
    unpackNative x p k = x ⟨27 * p.val + k.val, by omega⟩ := rfl

theorem pack_unpackNative (x : Fin 1053 → ℝ) : PartialAction.pack (unpackNative x) = x := by
  funext v
  change x ⟨27 * (v.val / 27) + v.val % 27, _⟩ = x v
  congr 1
  apply Fin.ext
  change 27 * (v.val / 27) + v.val % 27 = v.val
  omega

theorem unpackNative_pack (x : Cfg) : unpackNative (PartialAction.pack x) = x := by
  funext p k
  change x ⟨(27 * p.val + k.val) / 27, _⟩ ⟨(27 * p.val + k.val) % 27, _⟩ = x p k
  congr 1
  · apply Fin.ext
    change (27 * p.val + k.val) / 27 = p.val
    omega
  · apply Fin.ext
    change (27 * p.val + k.val) % 27 = k.val
    omega

theorem unpack_bookBase : unpackNative Option2.BookNativeBase.bookBase = literalCfg exactPhases := by
  rw [← TangentCoordinates.pack_literalCfg_exactPhases, unpackNative_pack]

/-- The unchanged Book realV, in the exact native derivative domain. -/
def bookDirection : Blocks →L[ℝ] Cfg := unpackNative.comp realVContinuousLinearMap

@[simp] theorem bookDirection_apply (z : Blocks) : bookDirection z = unpackNative (realV z) := rfl

theorem pack_bookDirection (z : Blocks) : PartialAction.pack (bookDirection z) = realV z :=
  pack_unpackNative (realV z)

theorem bookDirection_mem_tangent (z : Blocks) : bookDirection z ∈ tangentSpace exactPhases := by
  change fderiv ℝ AnalyticDerivative.originalF (literalCfg exactPhases) (bookDirection z) = 0
  rw [← packed_originalF_derivative, TangentCoordinates.pack_literalCfg_exactPhases,
    pack_bookDirection]
  exact realV_originalF_derivative_zero z

/-- The genuine normal projection along the actual native orbit tangent. -/
def normalProjection : Cfg →L[ℝ] normalC exactPhases :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Cfg) (F' := ↥(normalC exactPhases))
    ((normalC exactPhases).projectionOnto (orbitC exactPhases)
      (isCompl_orbitC_normalC exactPhases exactPhases_unit).symm)

theorem normalProjection_eq_zero_iff (x : Cfg) :
    normalProjection x = 0 ↔ x ∈ orbitC exactPhases :=
  Submodule.projectionOnto_apply_eq_zero_iff
    (isCompl_orbitC_normalC exactPhases exactPhases_unit).symm

@[simp] theorem normalProjection_normal (n : normalC exactPhases) :
    normalProjection (n : Cfg) = n :=
  Submodule.projectionOnto_apply_left
    (isCompl_orbitC_normalC exactPhases exactPhases_unit).symm n

theorem sub_normalProjection_mem_orbit (x : Cfg) :
    x - (normalProjection x : Cfg) ∈ orbitC exactPhases :=
  Submodule.sub_projection_mem
    (isCompl_orbitC_normalC exactPhases exactPhases_unit).symm x

theorem normalProjection_mem_tangent {x : Cfg} (hx : x ∈ tangentSpace exactPhases) :
    (normalProjection x : Cfg) ∈ tangentSpace exactPhases := by
  have h := (tangentSpace exactPhases).sub_mem hx
    (klin_orbitC_le exactPhases_unit (sub_normalProjection_mem_orbit x))
  simpa only [sub_sub_cancel] using h

/-- Actual projected Book directions, now valued in the genuine normal kernel. -/
def projectedBook : Blocks →L[ℝ] tanN exactPhases :=
  ((normalC exactPhases).subtypeL.comp (normalProjection.comp bookDirection)).codRestrict
    (tanN exactPhases) (fun z =>
      ⟨normalProjection_mem_tangent (bookDirection_mem_tangent z),
        (normalProjection (bookDirection z)).property⟩)

@[simp] theorem projectedBook_coe (z : Blocks) :
    (projectedBook z : Cfg) = (normalProjection (unpackNative (realV z)) : Cfg) := rfl

def commonInclusion : fixQK exactPhases →L[ℝ] tanN exactPhases :=
  (fixQK exactPhases).subtypeL.codRestrict (tanN exactPhases) (fun c => c.property.1.1)

/-- The actual intended Book/common-tangent map; bijectivity remains to be proved. -/
def bookCommonMap : (fixQK exactPhases × Blocks) →L[ℝ] tanN exactPhases :=
  commonInclusion.coprod projectedBook

theorem bookCommonMap_coe (c : fixQK exactPhases) (z : Blocks) :
    (bookCommonMap (c, z) : Cfg) =
      (c : Cfg) + (normalProjection (unpackNative (realV z)) : Cfg) := rfl

/-- A projected Book direction is common precisely when its native lift is orbit-plus-common. -/
theorem projectedBook_mem_common_iff (z : Blocks) :
    (projectedBook z : Cfg) ∈ fixQK exactPhases ↔
      bookDirection z ∈ orbitC exactPhases ⊔ fixQK exactPhases := by
  constructor
  · intro hz
    have ho := sub_normalProjection_mem_orbit (bookDirection z)
    have hc : (normalProjection (bookDirection z) : Cfg) ∈ fixQK exactPhases := hz
    have h := Submodule.add_mem_sup ho hc
    simpa only [sub_add_cancel] using h
  · intro hz
    obtain ⟨o, ho, c, hc, hsum⟩ := Submodule.mem_sup.1 hz
    have hno : normalProjection o = 0 := (normalProjection_eq_zero_iff o).2 ho
    have hnc : normalProjection c = ⟨c, hc.1.1.2⟩ := normalProjection_normal ⟨c, hc.1.1.2⟩
    have he : normalProjection (bookDirection z) = ⟨c, hc.1.1.2⟩ := by
      rw [← hsum, map_add, hno, hnc, zero_add]
    change (normalProjection (bookDirection z) : Cfg) ∈ fixQK exactPhases
    rw [he]
    exact hc

/-- Exact remaining injectivity obligation, not assumed and not an equivalence claim. -/
theorem bookCommonMap_injective_iff_native_separation :
    Function.Injective bookCommonMap ↔
      ∀ z : Blocks, bookDirection z ∈ orbitC exactPhases ⊔ fixQK exactPhases → z = 0 := by
  constructor
  · intro hi z hz
    have hc := (projectedBook_mem_common_iff z).2 hz
    let c : fixQK exactPhases := ⟨-(projectedBook z : Cfg), (fixQK exactPhases).neg_mem hc⟩
    have hm : bookCommonMap (c, z) = 0 := by
      apply Subtype.ext
      change -(projectedBook z : Cfg) + (projectedBook z : Cfg) = 0
      exact neg_add_cancel _
    have hp : (c, z) = 0 := hi (hm.trans (map_zero bookCommonMap).symm)
    exact congrArg Prod.snd hp
  · intro hsep
    refine (injective_iff_map_eq_zero bookCommonMap).2 ?_
    rintro ⟨c, z⟩ hz
    have he : (c : Cfg) + (projectedBook z : Cfg) = 0 := congrArg Subtype.val hz
    have hc : (projectedBook z : Cfg) ∈ fixQK exactPhases := by
      rw [eq_neg_of_add_eq_zero_right he]
      exact (fixQK exactPhases).neg_mem c.property
    have hz0 := hsep z ((projectedBook_mem_common_iff z).1 hc)
    subst z
    have hc0 : c = 0 := by
      apply Subtype.ext
      simpa only [map_zero, Submodule.coe_zero, add_zero] using he
    exact Prod.ext hc0 rfl

/-- Simultaneous left/right family parameters, before taking the genuine normal projection. -/
def simultaneousParameters : (Fin 8 → ℝ) →L[ℝ] PreParam :=
  (ContinuousLinearMap.id ℝ (Fin 8 → ℝ)).prod
    ((ContinuousLinearMap.id ℝ (Fin 8 → ℝ)).prod 0)

def projectedSimultaneousFamily (H : Fin 4) : (Fin 8 → ℝ) →L[ℝ] normalC exactPhases :=
  normalProjection.comp ((preDer exactPhases exactPhases_unit H).comp simultaneousParameters)

theorem projectedSimultaneousFamily_apply (H : Fin 4) (X : Fin 8 → ℝ) :
    projectedSimultaneousFamily H X =
      normalProjection (preVar exactPhases exactPhases_unit H (X, X, 0)) := by
  change normalProjection (preDer exactPhases exactPhases_unit H (X, X, 0)) = _
  rw [preDer_apply]

/-- Actual A5 raw-kernel characterization proves each family injective modulo orbit. -/
theorem projectedSimultaneousFamily_injective (H : Fin 4) :
    Function.Injective (projectedSimultaneousFamily H) := by
  refine (injective_iff_map_eq_zero _).2 ?_
  intro X hX
  have hm : preDer exactPhases exactPhases_unit H (X, X, 0) ∈ orbitC exactPhases :=
    (normalProjection_eq_zero_iff _).1 hX
  obtain ⟨D, hD, hDvalue⟩ := hm
  have hraw : rawDer exactPhases exactPhases_unit H
      (⟨-D, derC.neg_mem hD⟩, (X, X, 0)) = 0 := by
    rw [rawDer_apply]
    change orbitMapC exactPhases (-D) + preDer exactPhases exactPhases_unit H (X, X, 0) = 0
    have hv : orbitMapC exactPhases D = preDer exactPhases exactPhases_unit H (X, X, 0) := hDvalue
    rw [map_neg, hv, neg_add_cancel]
  obtain ⟨k, -, hparam⟩ := (rawDer_eq_zero_iff exactPhases_unit H _).1 hraw
  exact congrArg Prod.fst hparam

/-- The actual second family parameter is an orbit direction, so normal projection removes it. -/
theorem projectedSimultaneousFamily_eq_left (H : Fin 4) (X : Fin 8 → ℝ) :
    projectedSimultaneousFamily H X =
      normalProjection (preVar exactPhases exactPhases_unit H (X, 0, 0)) := by
  have hright : normalProjection (preDer exactPhases exactPhases_unit H (0, X, 0)) = 0 := by
    apply (normalProjection_eq_zero_iff _).2
    have he := orbitMapC_gaugeDer exactPhases_unit H X
    rw [eq_neg_of_add_eq_zero_right he]
    exact (orbitC exactPhases).neg_mem ⟨gaugeDer H X, gaugeDer_mem_derC H X, rfl⟩
  change normalProjection (preDer exactPhases exactPhases_unit H (X, X, 0)) = _
  rw [show (X, X, (0 : Fin 2 → ℝ)) = (X, 0, 0) + (0, X, 0) by simp,
    map_add, map_add, hright, add_zero, preDer_apply]

/-- Exact supplied D6 real column, with original labels, after the actual normal projection. -/
theorem projected_d6_real_family (b : Fin 24) :
    normalProjection (unpackNative (fun v => (d6Column b v).re)) =
      projectedSimultaneousFamily (d6Sheet b) (rootRealParam ⟨b.val % 6, by omega⟩) := by
  rw [projectedSimultaneousFamily_apply]
  congr 1
  funext p k
  exact d6Column_re_preVar_point b p k

theorem projected_d6_imag_family (b : Fin 24) :
    normalProjection (unpackNative (fun v => (d6Column b v).im)) =
      projectedSimultaneousFamily (d6Sheet b) (rootImagParam ⟨b.val % 6, by omega⟩) := by
  rw [projectedSimultaneousFamily_apply]
  congr 1
  funext p k
  exact d6Column_im_preVar_point b p k

end Option2.NativeStress.BookHT.NativeNormalKernelBridge

#check Option2.NativeStress.BookHT.NativeNormalKernelBridge.exactPhases_good
#check Option2.NativeStress.BookHT.NativeNormalKernelBridge.projectedBook
#check Option2.NativeStress.BookHT.NativeNormalKernelBridge.bookCommonMap_injective_iff_native_separation
#check Option2.NativeStress.BookHT.NativeNormalKernelBridge.projectedSimultaneousFamily_injective
#print axioms Option2.NativeStress.BookHT.NativeNormalKernelBridge.exactPhases_good
#print axioms Option2.NativeStress.BookHT.NativeNormalKernelBridge.projectedBook
#print axioms Option2.NativeStress.BookHT.NativeNormalKernelBridge.bookCommonMap_injective_iff_native_separation
#print axioms Option2.NativeStress.BookHT.NativeNormalKernelBridge.projectedSimultaneousFamily_injective
#print axioms Option2.NativeStress.BookHT.NativeNormalKernelBridge.projectedSimultaneousFamily_eq_left
