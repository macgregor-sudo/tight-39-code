module

public import A5Gauge

@[expose] public section

/-!
# The pointwise quartet fixer is the right gauge (piece FIXER)

`rightDer Z : (a, B) ↦ (0, B Z)` is a Jordan derivation for `Z ∈ su(3)` (derivative at `t = 0` of
the accepted automorphisms `nativeRightMultiply (exp (t Z))`, or directly from the product formula).
A derivation vanishing on the twelve quartet points of anchor `H` vanishes on their real span, which
is the whole fixed subalgebra `anchorFixedAlg H` (for anchor 0: `{B = 0} ≅ H₃(ℂ)`, spanned by a
complete quartet; transported by `anchorΨ`), so it lies in A4's eight-dimensional `pointwiseFactor H`;
the injective eight-dimensional right gauge `gaugeDer H` lies there too, hence fills it.
Classical: Yokota, arXiv:0902.0431, proof of Thm 1.9.4 and Thm 2.12.2 (fixer convention swapped).
-/

noncomputable section

open CKM.NativeFirstOrder CKM.NativeGroupSlice CompactAlbert UnitaryErrorBases
open scoped Matrix Topology

namespace CKM.NativeFourFamily

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## The right derivation in Tits coordinates -/

/-- `rightDer Z` acts as `(a, B) ↦ (0, B Z)` on Tits matrix pairs. -/
theorem fixer_rightDer_pair (Z : TitsComplexMatrix) (x : Glennie.Albert) :
    nativeTitsMatrixPair (rightDer Z x) = (0, (nativeTitsMatrixPair x).2 * Z) := by
  rw [rightDer, LinearMap.sub_apply, map_sub, nativeRightMultiply_pair, nativeRightMultiply_pair,
    Prod.mk_sub_mk, sub_self, Matrix.mul_zero, sub_zero]

theorem fixer_rightDer_add (Z Z' : TitsComplexMatrix) :
    rightDer (Z + Z') = rightDer Z + rightDer Z' := by
  apply LinearMap.ext
  intro x
  apply nativeTitsMatrixPair_injective
  rw [LinearMap.add_apply, map_add, fixer_rightDer_pair, fixer_rightDer_pair, fixer_rightDer_pair,
    Prod.mk_add_mk, add_zero, Matrix.mul_add]

theorem fixer_rightDer_smul (c : ℝ) (Z : TitsComplexMatrix) :
    rightDer (c • Z) = c • rightDer Z := by
  apply LinearMap.ext
  intro x
  apply nativeTitsMatrixPair_injective
  rw [LinearMap.smul_apply, map_smul, fixer_rightDer_pair, fixer_rightDer_pair, Prod.smul_mk,
    smul_zero, Matrix.mul_smul]

theorem rightDer_includeHermitianMatrix (Z : TitsComplexMatrix)
    (a : {a : TitsComplexMatrix // a.IsHermitian}) : rightDer Z (includeHermitianMatrix a) = 0 := by
  rw [rightDer, LinearMap.sub_apply, nativeRightMultiply_includeHermitianMatrix,
    nativeRightMultiply_includeHermitianMatrix, sub_self]

theorem rightDer_complementaryPoint (Z U : TitsComplexMatrix) :
    rightDer Z (nativeComplementaryPoint U) = hiddenVec (U * Z) := by
  apply nativeTitsMatrixPair_injective
  rw [fixer_rightDer_pair, nativeComplementaryPoint_pair, hiddenVec, Elim.mkPoint_pair]
  simp only [Matrix.smul_mul]

/-- Polarized adjugate identity for `3 × 3` matrices: the simultaneous right variation of the
polarization of `adj` by `Z` is left multiplication by `tr Z • 1 - Z` (infinitesimal form of
`adj (X Y) = adj Y adj X`). -/
theorem fixer_adj_polar {R : Type*} [CommRing R] (B D Z : Matrix (Fin 3) (Fin 3) R) :
    (B * Z + D).adjugate - (B * Z).adjugate - D.adjugate +
        ((B + D * Z).adjugate - B.adjugate - (D * Z).adjugate) =
      (Z.trace • (1 : Matrix (Fin 3) (Fin 3) R) - Z) *
        ((B + D).adjugate - B.adjugate - D.adjugate) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [Matrix.adjugate_fin_three, Matrix.mul_apply, Fin.sum_univ_three, Matrix.trace_fin_three,
    Matrix.one_apply] <;> ring

/-- `rightDer Z` is a Jordan derivation for traceless skew-Hermitian `Z`, checked directly on the
accepted second Tits product formula `native_tits_product_pair`. -/
theorem fixer_rightDer_mem_jordanDerivations {Z : TitsComplexMatrix} (hZ : Zᴴ = -Z)
    (htr : Z.trace = 0) : rightDer Z ∈ CKM.NativeDerivationTriality.jordanDerivations := by
  rw [CKM.NativeDerivationTriality.mem_jordanDerivations]
  intro x y
  have hprod : ∀ u v : Glennie.Albert, nativeTitsMatrixPair (Glennie.jordan u v) =
      compactSecondTitsProduct (nativeTitsMatrixPair u) (nativeTitsMatrixPair v) :=
    native_tits_product_pair
  apply nativeTitsMatrixPair_injective
  rw [map_add, hprod, hprod, fixer_rightDer_pair, fixer_rightDer_pair, fixer_rightDer_pair, hprod]
  obtain ⟨a, B⟩ := nativeTitsMatrixPair x
  obtain ⟨c, D⟩ := nativeTitsMatrixPair y
  simp only [compactSecondTitsProduct, compactSecondTitsProductComplex,
    compactSecondTitsProductHidden, Prod.mk_add_mk]
  have key : ((B * Z + D).adjugateᴴ - (B * Z).adjugateᴴ - D.adjugateᴴ) +
      ((B + D * Z).adjugateᴴ - B.adjugateᴴ - (D * Z).adjugateᴴ) =
      ((B + D).adjugateᴴ - B.adjugateᴴ - D.adjugateᴴ) * Z := by
    have h := congrArg Matrix.conjTranspose (fixer_adj_polar B D Z)
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      htr, zero_smul, zero_sub, Matrix.conjTranspose_neg, hZ, neg_neg] at h
    exact h
  refine Prod.ext ?_ ?_
  · simp only [Matrix.conjTranspose_mul, hZ, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_zero,
      Matrix.zero_mul, Matrix.mul_assoc, Matrix.trace_neg, Complex.neg_re, Complex.ofReal_neg,
      neg_smul, add_zero, zero_add, zero_sub, sub_neg_eq_add]
    module
  · simp only [Matrix.trace_zero, Complex.zero_re, Complex.ofReal_zero, zero_smul, sub_zero,
      Matrix.zero_mul, add_zero, zero_add]
    rw [Matrix.smul_mul, Matrix.add_mul, Matrix.add_mul, ← key, Matrix.mul_assoc, Matrix.mul_assoc]
    module

/-! ## Linearity, membership and injectivity of the gauge -/

theorem fixer_suMat_add (k k' : Fin 8 → ℝ) : suMat (k + k') = suMat k + suMat k' := by
  simp only [suMat, Pi.add_apply, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]

theorem fixer_suMat_smul (c : ℝ) (k : Fin 8 → ℝ) : suMat (c • k) = c • suMat k := by
  simp only [suMat, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Finset.smul_sum, mul_smul,
    Complex.coe_smul]

theorem fixer_rightDer_suMat_mem (k : Fin 8 → ℝ) :
    rightDer (suMat k) ∈ CKM.NativeDerivationTriality.jordanDerivations :=
  fixer_rightDer_mem_jordanDerivations (suMat_conjTranspose k) (suMat_trace k)

theorem fixer_gauge_symm (H : Fin 4) (k : Fin 8 → ℝ) :
    coordEnd.symm (gaugeDer H k) = anchorΨinv H * rightDer (suMat k) * anchorΨ H := by
  rw [gaugeDer, AlgEquiv.symm_apply_apply]
  rfl

theorem fixer_gauge_mem_jordanDerivations (H : Fin 4) (k : Fin 8 → ℝ) :
    coordEnd.symm (gaugeDer H k) ∈ CKM.NativeDerivationTriality.jordanDerivations := by
  rw [fixer_gauge_symm]
  exact CKM.NativeIntrinsicTriality.pwf_conj_mem_jordanDerivations (anchorΨ_isNativeAut H)
    (anchorΨinv_isNativeAut H) (anchorΨinv_comp_anchorΨ H) (fixer_rightDer_suMat_mem k)

theorem gaugeDer_mem_derC (H : Fin 4) (k : Fin 8 → ℝ) : gaugeDer H k ∈ derC :=
  (mem_derC_iff _).mpr (fixer_gauge_mem_jordanDerivations H k)

theorem gaugeDer_add (H : Fin 4) (k k' : Fin 8 → ℝ) :
    gaugeDer H (k + k') = gaugeDer H k + gaugeDer H k' := by
  rw [gaugeDer, gaugeDer, gaugeDer, fixer_suMat_add, fixer_rightDer_add, LinearMap.add_comp,
    LinearMap.comp_add, map_add]

theorem gaugeDer_smul (H : Fin 4) (c : ℝ) (k : Fin 8 → ℝ) : gaugeDer H (c • k) = c • gaugeDer H k := by
  rw [gaugeDer, gaugeDer, fixer_suMat_smul, fixer_rightDer_smul, LinearMap.smul_comp,
    LinearMap.comp_smul, map_smul]

theorem fixer_anchorΨ_anchorΨinv_apply (H : Fin 4) (x : Glennie.Albert) :
    anchorΨ H (anchorΨinv H x) = x :=
  LinearMap.congr_fun (anchorΨ_comp_anchorΨinv H) x

theorem fixer_anchorΨinv_anchorΨ_apply (H : Fin 4) (x : Glennie.Albert) :
    anchorΨinv H (anchorΨ H x) = x :=
  LinearMap.congr_fun (anchorΨinv_comp_anchorΨ H) x

theorem fixer_hiddenVec_injective : Function.Injective hiddenVec := by
  intro U V h
  have hp := congrArg (fun x => (nativeTitsMatrixPair x).2) h
  simp only [hiddenVec, Elim.mkPoint_pair] at hp
  exact smul_right_injective _ (by norm_num : (1 / 3 : ℂ) ≠ 0) hp

theorem gaugeDer_injective (H : Fin 4) : Function.Injective (gaugeDer H) := by
  intro k k' h
  have h1 := congrArg coordEnd.symm h
  rw [fixer_gauge_symm, fixer_gauge_symm] at h1
  have h2 := LinearMap.congr_fun h1 (anchorΨinv H (nativeComplementaryPoint 1))
  simp only [Module.End.mul_apply, fixer_anchorΨ_anchorΨinv_apply] at h2
  have h3 := congrArg (anchorΨ H) h2
  rw [fixer_anchorΨ_anchorΨinv_apply, fixer_anchorΨ_anchorΨinv_apply,
    rightDer_complementaryPoint, rightDer_complementaryPoint, Matrix.one_mul,
    Matrix.one_mul] at h3
  exact suMat_injective (fixer_hiddenVec_injective h3)

/-! ## The quartet spans the visible subalgebra -/

theorem fixer_trace_mul_real {a P : TitsComplexMatrix} (ha : a.IsHermitian) (hP : P.IsHermitian) :
    (((a * P).trace.re : ℝ) : ℂ) = (a * P).trace := by
  rw [← Complex.conj_eq_iff_re]
  change star (a * P).trace = (a * P).trace
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hP.eq, ha.eq, Matrix.trace_mul_comm]

theorem fixer_std_succ (k t : Fin 3) :
    (stdQuartet k.succ t).val = UnitaryErrorBases.ComplexQuartet.phaseProjector k t := by
  fin_cases k <;> rfl

theorem fixer_std_zero (t : Fin 3) :
    (stdQuartet 0 t).val = UnitaryErrorBases.ComplexQuartet.coordinateProjector t := rfl

/-- Coefficients of a matrix in the standard quartet (readouts, corrected on the coordinate frame). -/
def fixer_stdCoeff (a : TitsComplexMatrix) (k : Fin 4) (t : Fin 3) : ℝ :=
  (a * (stdQuartet k t).val).trace.re - if k = 0 then a.trace.re else 0

/-- Every Hermitian matrix is a real combination of the twelve standard quartet projectors
(complete set of mutually unbiased bases in `ℂ³`; the accepted `literal_quartet_reconstruction`).
Classical: Wootters–Fields, Ann. Phys. 191 (1989) 363, eq. (9). -/
theorem fixer_span_std (a : TitsComplexMatrix) (ha : a.IsHermitian) :
    ∃ c : Fin 4 → Fin 3 → ℝ, a = ∑ k, ∑ t, c k t • (stdQuartet k t).val := by
  refine ⟨fixer_stdCoeff a, ?_⟩
  have hrec := UnitaryErrorBases.ComplexQuartet.literal_quartet_reconstruction a
  have hrec' : (∑ t : Fin 3, (a * UnitaryErrorBases.ComplexQuartet.coordinateProjector t).trace •
      UnitaryErrorBases.ComplexQuartet.coordinateProjector t) +
      (∑ s : Fin 3, ∑ t : Fin 3, (a * UnitaryErrorBases.ComplexQuartet.phaseProjector s t).trace •
        UnitaryErrorBases.ComplexQuartet.phaseProjector s t) = a + a.trace • 1 := hrec
  have hsum := UnitaryErrorBases.ComplexQuartet.coordinateProjector_sum
  have htr : ((a.trace.re : ℝ) : ℂ) = a.trace := by
    simpa using fixer_trace_mul_real ha Matrix.isHermitian_one
  have h0 : ∀ t, fixer_stdCoeff a 0 t • (stdQuartet 0 t).val =
      (a * UnitaryErrorBases.ComplexQuartet.coordinateProjector t).trace •
        UnitaryErrorBases.ComplexQuartet.coordinateProjector t -
      a.trace • UnitaryErrorBases.ComplexQuartet.coordinateProjector t := by
    intro t
    simp only [fixer_stdCoeff, ↓reduceIte]
    rw [sub_smul, ← Complex.coe_smul, ← Complex.coe_smul,
      fixer_trace_mul_real ha (stdQuartet 0 t).2, htr, fixer_std_zero]
  have hs : ∀ (k : Fin 3) t, fixer_stdCoeff a k.succ t • (stdQuartet k.succ t).val =
      (a * UnitaryErrorBases.ComplexQuartet.phaseProjector k t).trace •
        UnitaryErrorBases.ComplexQuartet.phaseProjector k t := by
    intro k t
    simp only [fixer_stdCoeff, Fin.succ_ne_zero, ↓reduceIte, sub_zero]
    rw [← Complex.coe_smul,
      fixer_trace_mul_real ha (stdQuartet k.succ t).2, fixer_std_succ]
  rw [Fin.sum_univ_succ]
  simp only [h0, hs, Finset.sum_sub_distrib, ← Finset.smul_sum, hsum]
  rw [sub_add_eq_add_sub, hrec', add_sub_cancel_right]

/-- The conjugated quartet of every anchor still spans the Hermitian matrices over `ℝ`. -/
theorem fixer_span_anchor {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) (a : TitsComplexMatrix)
    (ha : a.IsHermitian) :
    ∃ c : Fin 4 → Fin 3 → ℝ, a = ∑ k, ∑ t, c k t • (anchorQuartet ξ H k t).val := by
  set g := quartetConj ξ H
  have hg : g * gᴴ = 1 := quartetConj_unitary hξ H
  have hg' : gᴴ * g = 1 := mul_eq_one_comm.mp hg
  obtain ⟨c, hc⟩ := fixer_span_std (gᴴ * a * g) (Matrix.isHermitian_conjTranspose_mul_mul g ha)
  refine ⟨c, ?_⟩
  have e : a = g * (gᴴ * a * g) * gᴴ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg, Matrix.one_mul, Matrix.mul_assoc, hg,
      Matrix.mul_one]
  rw [e, hc, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [anchorQuartet_val, Matrix.mul_smul, Matrix.smul_mul]

/-- A real-linear map vanishing on the twelve quartet points of anchor `H` vanishes on the whole
visible subalgebra `{B = 0}`. -/
theorem fixer_vanish_visible {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4)
    (E : Glennie.Albert →ₗ[ℝ] Glennie.Albert)
    (hE : ∀ k t, E (includeHermitianMatrix (anchorQuartet ξ H k t)) = 0)
    (a : {a : TitsComplexMatrix // a.IsHermitian}) : E (includeHermitianMatrix a) = 0 := by
  obtain ⟨c, hc⟩ := fixer_span_anchor hξ H a.val a.2
  have hx : includeHermitianMatrix a =
      ∑ k, ∑ t, c k t • includeHermitianMatrix (anchorQuartet ξ H k t) := by
    apply nativeTitsMatrixPair_injective
    simp only [map_sum, map_smul, includeHermitianMatrix_pair]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_sum, Prod.smul_fst]
      exact hc
    · simp only [Prod.snd_sum, Prod.smul_snd, smul_zero, Finset.sum_const_zero]
  rw [hx, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [map_smul, hE, smul_zero]

/-- Points fixed by `R0` (right multiplication by `ω`) have zero hidden part. -/
theorem fixer_R0_fixed (x : Glennie.Albert) (hx : R0 x = x) :
    ∃ a : {a : TitsComplexMatrix // a.IsHermitian}, x = includeHermitianMatrix a := by
  have hp := congrArg nativeTitsMatrixPair hx
  rw [R0, nativeRightMultiply_pair] at hp
  have hB : (nativeTitsMatrixPair x).2 = 0 := by
    have h2 := congrArg Prod.snd hp
    simp only [Matrix.mul_smul, Matrix.mul_one] at h2
    have h3 : (UnitaryErrorBases.ThreeCycleFourier.omega - 1) • (nativeTitsMatrixPair x).2 = 0 := by
      rw [sub_smul, one_smul, h2, sub_self]
    exact (smul_eq_zero.mp h3).resolve_left
      (sub_ne_zero.mpr CKM.NativeIntrinsicTriality.krep_omega_ne_one)
  refine ⟨⟨(nativeTitsMatrixPair x).1, hermitianMatrix_isHermitian (toTitsCoordinates x)⟩, ?_⟩
  apply nativeTitsMatrixPair_injective
  rw [includeHermitianMatrix_pair, ← hB]

/-- The anchor-`H` fixed subalgebra is carried by `anchorΨ H` into `{B = 0}`. -/
theorem fixer_anchorFixed (H : Fin 4) (x : Glennie.Albert)
    (hx : x ∈ CKM.NativeIntrinsicTriality.anchorFixedAlg H) :
    ∃ a : {a : TitsComplexMatrix // a.IsHermitian}, anchorΨ H x = includeHermitianMatrix a := by
  rw [CKM.NativeIntrinsicTriality.anchorFixedAlg, mem_fixedSpace] at hx
  apply fixer_R0_fixed
  have h := LinearMap.congr_fun (anchorΨ_conj H) x
  simp only [LinearMap.comp_apply, hx] at h
  exact h.symm

/-! ## The quartet fixer -/

theorem fixer_quartet_point {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) (k : Fin 4)
    (t : Fin 3) :
    anchorΨ H (literalPoint ξ (quartetLabel H ⟨3 * k.val + t.val, by omega⟩)) =
      includeHermitianMatrix (anchorQuartet ξ H k t) := by
  have h := anchor_form hξ H ⟨3 * k.val + t.val, by omega⟩
  refine (h.trans ?_)
  have hlt : 3 * k.val + t.val < 12 := by omega
  simp only [stdAnchored, hlt, ↓reduceDIte]
  congr 2 <;> apply Fin.ext <;> dsimp only <;> omega

theorem fixer_mem_quartetFixer {ξ₀ : Fin 4 → ℂ} (H : Fin 4) (D : CEnd) :
    D ∈ quartetFixer ξ₀ H ↔ D ∈ derC ∧ ∀ j, D (literalCfg ξ₀ (quartetLabel H j)) = 0 := by
  simp only [quartetFixer, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.apply_apply]

theorem fixer_symm_apply_eq_zero (D : CEnd) (y : Glennie.Albert)
    (h : D (NativePolynomial.upperCoordinates y) = 0) : coordEnd.symm D y = 0 := by
  rw [coordEnd_symm_apply, h]
  exact (Glennie.Albert.extExplicit 0 (NativePolynomial.fromUpperCoordinates 0) rfl rfl rfl rfl rfl
    rfl).symm

theorem fixer_quartet_mem_pwf {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) (D : CEnd)
    (hD : D ∈ quartetFixer ξ₀ H) :
    coordEnd.symm D ∈ CKM.NativeIntrinsicTriality.pointwiseFactor H := by
  rw [fixer_mem_quartetFixer] at hD
  rw [CKM.NativeIntrinsicTriality.mem_pointwiseFactor]
  refine ⟨(mem_derC_iff D).mp hD.1, fun x hx => ?_⟩
  obtain ⟨a, ha⟩ := fixer_anchorFixed H x hx
  have hxa : x = anchorΨinv H (includeHermitianMatrix a) := by
    rw [← ha, fixer_anchorΨinv_anchorΨ_apply]
  rw [hxa]
  refine fixer_vanish_visible hξ₀ H (coordEnd.symm D ∘ₗ anchorΨinv H) (fun k t => ?_) a
  rw [LinearMap.comp_apply, ← fixer_quartet_point hξ₀ H k t, fixer_anchorΨinv_anchorΨ_apply]
  exact fixer_symm_apply_eq_zero D _ (hD.2 _)

theorem fixer_gauge_mem_pwf (H : Fin 4) (k : Fin 8 → ℝ) :
    coordEnd.symm (gaugeDer H k) ∈ CKM.NativeIntrinsicTriality.pointwiseFactor H := by
  rw [CKM.NativeIntrinsicTriality.mem_pointwiseFactor]
  refine ⟨fixer_gauge_mem_jordanDerivations H k, fun x hx => ?_⟩
  obtain ⟨a, ha⟩ := fixer_anchorFixed H x hx
  rw [fixer_gauge_symm, Module.End.mul_apply, Module.End.mul_apply, ha,
    rightDer_includeHermitianMatrix, map_zero]

/-- The gauge as a linear map into A4's pointwise factor. -/
def fixer_gaugePwf (H : Fin 4) :
    (Fin 8 → ℝ) →ₗ[ℝ] ↥(CKM.NativeIntrinsicTriality.pointwiseFactor H) where
  toFun k := ⟨coordEnd.symm (gaugeDer H k), fixer_gauge_mem_pwf H k⟩
  map_add' k k' := Subtype.ext (by simp only [gaugeDer_add, map_add]; rfl)
  map_smul' c k := Subtype.ext (by simp only [gaugeDer_smul, map_smul]; rfl)

theorem fixer_gaugePwf_surjective (H : Fin 4) : Function.Surjective (fixer_gaugePwf H) := by
  have hinj : Function.Injective (fixer_gaugePwf H) := by
    intro k k' h
    have h1 := congrArg Subtype.val h
    exact gaugeDer_injective H (coordEnd.symm.injective h1)
  have hfin : FiniteDimensional ℝ ↥(CKM.NativeIntrinsicTriality.pointwiseFactor H) :=
    Module.finite_of_finrank_pos (by rw [CKM.NativeIntrinsicTriality.finrank_pointwiseFactor]; norm_num)
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [CKM.NativeIntrinsicTriality.finrank_pointwiseFactor, Module.finrank_fin_fun])).mp hinj

theorem mem_quartetFixer_iff {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) (D : CEnd) :
    D ∈ quartetFixer ξ₀ H ↔ ∃ k, D = gaugeDer H k := by
  constructor
  · intro hD
    obtain ⟨k, hk⟩ := fixer_gaugePwf_surjective H ⟨_, fixer_quartet_mem_pwf hξ₀ H D hD⟩
    refine ⟨k, ?_⟩
    have h1 := congrArg Subtype.val hk
    exact (coordEnd.symm.injective h1).symm
  · rintro ⟨k, rfl⟩
    rw [fixer_mem_quartetFixer]
    refine ⟨gaugeDer_mem_derC H k, fun j => ?_⟩
    have hj : j = ⟨3 * (⟨j.val / 3, by omega⟩ : Fin 4).val + (⟨j.val % 3, by omega⟩ : Fin 3).val,
        by omega⟩ := by
      apply Fin.ext; simp only; omega
    rw [hj, gaugeDer]
    change coordEnd _ (NativePolynomial.upperCoordinates (literalPoint ξ₀ _)) = 0
    rw [coordEnd_apply, NativePolynomial.fromUpperCoordinates_upperCoordinates, LinearMap.comp_apply,
      LinearMap.comp_apply, fixer_quartet_point hξ₀, rightDer_includeHermitianMatrix, map_zero]
    exact map_zero NativePolynomial.upperCoordinateEquiv

/-- The gauge as a linear map into coordinate endomorphisms. -/
def fixer_gaugeLin (H : Fin 4) : (Fin 8 → ℝ) →ₗ[ℝ] CEnd where
  toFun := gaugeDer H
  map_add' := gaugeDer_add H
  map_smul' := gaugeDer_smul H

theorem finrank_quartetFixer {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    Module.finrank ℝ ↥(quartetFixer ξ₀ H) = 8 := by
  have heq : quartetFixer ξ₀ H = LinearMap.range (fixer_gaugeLin H) := by
    ext D
    rw [mem_quartetFixer_iff hξ₀, LinearMap.mem_range]
    exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩
  rw [heq, LinearMap.finrank_range_of_inj (gaugeDer_injective H), Module.finrank_fin_fun]

end CKM.NativeFourFamily

#print axioms CKM.NativeFourFamily.rightDer_includeHermitianMatrix
#print axioms CKM.NativeFourFamily.rightDer_complementaryPoint
#print axioms CKM.NativeFourFamily.gaugeDer_mem_derC
#print axioms CKM.NativeFourFamily.gaugeDer_add
#print axioms CKM.NativeFourFamily.gaugeDer_smul
#print axioms CKM.NativeFourFamily.gaugeDer_injective
#print axioms CKM.NativeFourFamily.mem_quartetFixer_iff
#print axioms CKM.NativeFourFamily.finrank_quartetFixer
#print axioms CKM.NativeFourFamily.fixer_rightDer_mem_jordanDerivations
#print axioms CKM.NativeFourFamily.fixer_adj_polar
#print axioms CKM.NativeFourFamily.fixer_span_std
