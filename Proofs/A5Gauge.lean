module

public import A5Defs

@[expose] public section

/-!
# Per-anchor gauge data at every phase (piece GAUGE)

Assembles A3's four bindings into the uniform A5 form: the binding transport and its inverse, the
conjugation and shift compatibility, the full `form` with the hidden matrices written through
`hidFamily ξ H 1 1 d_H(ξ)` (A3's gauge lemmas `anchor0W_gauge`, `W1_eq`, `anchor2W` (by
definition), `W3_gauge`), unitarity and determinants of the gauge factors, the quartet as a diagonal
unitary conjugate of the standard quartet, and exact invariance of every raw-family configuration under
the compensated anchor generator (from A3's `R0_stdAnchored`, for every hidden family).
-/

noncomputable section

open CKM.NativeFirstOrder CKM.NativeGroupSlice CompactAlbert UnitaryErrorBases
open scoped Matrix Topology

namespace CKM.NativeFourFamily

/-! ## Helpers (piece GAUGE) -/

private theorem gauge_isNativeAut_id :
    IsNativeAut (LinearMap.id : Glennie.Albert →ₗ[ℝ] Glennie.Albert) :=
  ⟨fun _ _ => by simp only [LinearMap.id_apply], fun _ => by rw [LinearMap.id_apply]⟩

private theorem gauge_chi_cube (a : Index) : UnitaryErrorBases.ThreeCycleFourier.character a ^ 3 = 1 := by
  show (UnitaryErrorBases.ThreeCycleFourier.omega ^ a.val) ^ 3 = 1
  rw [← pow_mul, mul_comm, pow_mul, Anchor0.omega_cube, one_pow]

theorem anchorΨinv_comp_anchorΨ (H : Fin 4) : anchorΨinv H ∘ₗ anchorΨ H = LinearMap.id := by
  match H with
  | 0 => exact LinearMap.id_comp _
  | 1 => exact transportT_comp_transportTinv 0
  | 2 => exact transportT_comp_transportTinv 1
  | 3 => exact transportT_comp_transportTinv 2

theorem anchorΨ_comp_anchorΨinv (H : Fin 4) : anchorΨ H ∘ₗ anchorΨinv H = LinearMap.id := by
  match H with
  | 0 => exact LinearMap.id_comp _
  | 1 => exact transportTinv_comp_transportT 0
  | 2 => exact transportTinv_comp_transportT 1
  | 3 => exact transportTinv_comp_transportT 2

private theorem gauge_Ψinv_Ψ (H : Fin 4) (x : Glennie.Albert) : anchorΨinv H (anchorΨ H x) = x := by
  have h := LinearMap.congr_fun (anchorΨinv_comp_anchorΨ H) x
  rwa [LinearMap.comp_apply, LinearMap.id_apply] at h

private theorem gauge_Ψ_Ψinv (H : Fin 4) (x : Glennie.Albert) : anchorΨ H (anchorΨinv H x) = x := by
  have h := LinearMap.congr_fun (anchorΨ_comp_anchorΨinv H) x
  rwa [LinearMap.comp_apply, LinearMap.id_apply] at h

theorem anchorΨ_isNativeAut (H : Fin 4) : IsNativeAut (anchorΨ H) := by
  match H with
  | 0 => exact gauge_isNativeAut_id
  | 1 => exact transportTinv_isNativeAut 0
  | 2 => exact transportTinv_isNativeAut 1
  | 3 => exact transportTinv_isNativeAut 2

theorem anchorΨinv_isNativeAut (H : Fin 4) : IsNativeAut (anchorΨinv H) := by
  match H with
  | 0 => exact gauge_isNativeAut_id
  | 1 => exact transportT_isNativeAut 0
  | 2 => exact transportT_isNativeAut 1
  | 3 => exact transportT_isNativeAut 2

theorem anchorΨ_conj (H : Fin 4) : anchorΨ H ∘ₗ anchorGenerator H = R0 ∘ₗ anchorΨ H := by
  match H with
  | 0 =>
    show LinearMap.id ∘ₗ R0 = R0 ∘ₗ LinearMap.id
    rw [LinearMap.id_comp, LinearMap.comp_id]
  | 1 =>
    show transportTinv 0 ∘ₗ (transportT 0 ∘ₗ R0 ∘ₗ transportTinv 0) = R0 ∘ₗ transportTinv 0
    rw [← LinearMap.comp_assoc, transportTinv_comp_transportT, LinearMap.id_comp]
  | 2 => exact transportTinv_one_conj
  | 3 => exact transportTinv_two_conj

/-- `ρ_H Ψ_H⁻¹ = Ψ_H⁻¹ R0`, pointwise. -/
private theorem gauge_gen_Ψinv (H : Fin 4) (x : Glennie.Albert) :
    anchorGenerator H (anchorΨinv H x) = anchorΨinv H (R0 x) := by
  have h := LinearMap.congr_fun (anchorΨ_conj H) (anchorΨinv H x)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, gauge_Ψ_Ψinv] at h
  rw [← h, gauge_Ψinv_Ψ]

theorem anchorRelabel_shift (H : Fin 4) (i : Fin 39) :
    outcomeShift (anchorShift H) (anchorRelabel H i) = anchorRelabel H (stdShift i) := by
  match H with
  | 0 => exact Anchor0.anchor0_shift_compat i
  | 1 => exact Anchor1.shift_compat1 i
  | 2 => exact Anchor2.anchor2_shift_compat i
  | 3 => exact Anchor3.shift_compat3 i

/-- The hidden family at `g = h = 1` and the anchor's phase triple is A3's hidden family. -/
private theorem gauge_hid0 {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) :
    hidFamily ξ 0 1 1 (anchorTriple ξ hξ 0) = Anchor0.anchor0W ξ := by
  funext l
  rw [Anchor0.anchor0W_gauge ξ hξ l]
  show Anchor0.gaugeC l • (1 * Anchor0.gaugeL ξ * monomialFamily (anchorTriple ξ hξ 0) (Anchor0.gaugeσ l) *
    Anchor0.gaugeR ξ * (1 : Mat)ᴴ) = _
  rw [Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul]

private theorem gauge_hid1 {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) :
    hidFamily ξ 1 1 1 (anchorTriple ξ hξ 1) = Anchor1.W1 ξ hξ := by
  funext l
  rw [Anchor1.W1_eq ξ hξ l]
  show (1 : ℂ) • (1 * Anchor1.asMat (Anchor1.Lg ξ) * monomialFamily (anchorTriple ξ hξ 1) (Anchor1.sigma1 l) *
    Anchor1.asMat (Anchor1.Rg ξ) * (1 : Mat)ᴴ) = _
  rw [Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul]

private theorem gauge_hid2 {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) :
    hidFamily ξ 2 1 1 (anchorTriple ξ hξ 2) = Anchor2.anchor2W ξ hξ := by
  funext l
  show Anchor2.gaugeC l • (1 * Anchor2.gaugeL ξ * monomialFamily (anchorTriple ξ hξ 2) l *
    Anchor2.gaugeR ξ * (1 : Mat)ᴴ) = Anchor2.gaugeC l •
      (Anchor2.gaugeL ξ * monomialFamily (anchorTriple ξ hξ 2) l * Anchor2.gaugeR ξ)
  rw [Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul]

private theorem gauge_hid3 {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) :
    hidFamily ξ 3 1 1 (anchorTriple ξ hξ 3) = Anchor3.W3 ξ := by
  funext l
  rw [Anchor3.W3_gauge ξ hξ l]
  show Anchor3.gaugeC3 l • (1 * Anchor3.gaugeL3 * monomialFamily (anchorTriple ξ hξ 3) (Anchor3.gaugeσ3 l) *
    (1 : Mat) * (1 : Mat)ᴴ) = _
  rw [Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul]

theorem anchor_form {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) (i : Fin 39) :
    anchorΨ H (literalPoint ξ (anchorRelabel H i)) =
      stdAnchored (anchorQuartet ξ H) (hidFamily ξ H 1 1 (anchorTriple ξ hξ H)) i := by
  match H with
  | 0 =>
    rw [gauge_hid0 hξ]
    exact Anchor0.anchor0_form ξ hξ i
  | 1 =>
    rw [gauge_hid1 hξ]
    show transportTinv 0 (literalPoint ξ (pointRelabel Anchor1.fperm1 Anchor1.tau1 i)) =
      stdAnchored Anchor1.q1 (Anchor1.W1 ξ hξ) i
    obtain ⟨⟨F, a⟩, rfl⟩ := (finProdFinEquiv : Fin 13 × Fin 3 ≃ Fin 39).surjective i
    rw [← Anchor1.framePointIndex_eq_finProd, pointRelabel_framePointIndex]
    exact Anchor1.form_frame ξ hξ F a
  | 2 =>
    rw [gauge_hid2 hξ]
    exact Anchor2.anchor2_form ξ hξ i
  | 3 =>
    rw [gauge_hid3 hξ]
    exact Anchor3.form3 ξ hξ i

theorem prePoint_base {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) :
    prePoint ξ H 1 1 (anchorTriple ξ hξ H) = literalPoint ξ := by
  funext i
  show anchorΨinv H (stdAnchored (anchorQuartet ξ H) (hidFamily ξ H 1 1 (anchorTriple ξ hξ H))
    ((anchorRelabel H).symm i)) = literalPoint ξ i
  rw [← anchor_form hξ H ((anchorRelabel H).symm i), Equiv.apply_symm_apply, gauge_Ψinv_Ψ]

theorem preCfg_base {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) :
    preCfg ξ H 1 1 (anchorTriple ξ hξ H) = literalCfg ξ := by
  funext i
  show NativePolynomial.upperCoordinates (prePoint ξ H 1 1 (anchorTriple ξ hξ H) i) =
    NativePolynomial.upperCoordinates (literalPoint ξ i)
  rw [prePoint_base hξ H]

private theorem gauge_torusPhase_zero (d₀ : PhaseTriple) : torusPhase d₀ 0 = d₀ := by
  apply Subtype.ext
  funext j
  have h : torusAngles 0 j = 0 := by
    rcases Anchor0.indexCases j with rfl | rfl | rfl <;> simp [torusAngles]
  show d₀.val j * Complex.exp ((torusAngles 0 j : ℂ) * Complex.I) = d₀.val j
  rw [h, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]

theorem preMap_zero {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) :
    preMap ξ hξ H 0 = literalCfg ξ := by
  show preCfg ξ H (suExp 0) (suExp 0) (torusPhase (anchorTriple ξ hξ H) 0) = literalCfg ξ
  rw [suExp_zero, gauge_torusPhase_zero]
  exact preCfg_base hξ H

theorem gaugeLeft_unitary {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) :
    (gaugeLeft ξ H)ᴴ * gaugeLeft ξ H = 1 := by
  match H with
  | 0 => exact Anchor0.gaugeL_unitary ξ hξ
  | 1 => exact Anchor1.Lg_unitary ξ hξ
  | 2 => exact Anchor2.gaugeL_unitary ξ hξ
  | 3 => exact Anchor3.gaugeL3_unitary

theorem gaugeRight_unitary {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) :
    gaugeRight ξ H * (gaugeRight ξ H)ᴴ = 1 := by
  match H with
  | 0 => exact Anchor0.gaugeR_unitary ξ hξ
  | 1 => exact Anchor1.Rg_unitary ξ hξ
  | 2 => exact Anchor2.gaugeR_unitary ξ hξ
  | 3 => exact Anchor3.one_unitary3

theorem gauge_det {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) :
    (gaugeLeft ξ H).det * (gaugeRight ξ H).det = 1 := by
  match H with
  | 0 =>
    have h2 := Anchor0.ne_zero_of_unit _ (hξ 2)
    have h3 := Anchor0.ne_zero_of_unit _ (hξ 3)
    have eL : (Anchor0.gaugeL ξ).det = ξ 2 / ξ 3 := by
      have dM : Matrix.det (!![0, 0, ξ 2; 0, -(ξ 3)⁻¹, 0; 1, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ) = ξ 2 / ξ 3 := by
        rw [Matrix.det_fin_three]
        simp
        field_simp
      have hM : Anchor0.gaugeL ξ = !![0, 0, ξ 2; 0, -(ξ 3)⁻¹, 0; 1, 0, 0] := by
        ext i j; fin_cases i <;> fin_cases j <;> rfl
      rw [hM]
      exact dM
    have eR : (Anchor0.gaugeR ξ).det = ξ 3 / ξ 2 := by
      have dM : Matrix.det (!![1, 0, 0; 0, ξ 3, 0; 0, 0, (ξ 2)⁻¹] : Matrix (Fin 3) (Fin 3) ℂ) = ξ 3 / ξ 2 := by
        rw [Matrix.det_fin_three]
        simp
        field_simp
      have hM : Anchor0.gaugeR ξ = !![1, 0, 0; 0, ξ 3, 0; 0, 0, (ξ 2)⁻¹] := by
        ext i j; fin_cases i <;> fin_cases j <;> rfl
      rw [hM]
      exact dM
    show (Anchor0.gaugeL ξ).det * (Anchor0.gaugeR ξ).det = 1
    rw [eL, eR]
    field_simp
  | 1 => exact Anchor1.Lg_Rg_det ξ hξ
  | 2 => exact Anchor2.gaugeL_det_mul_gaugeR_det ξ hξ
  | 3 =>
    show Anchor3.gaugeL3.det * (1 : Mat).det = 1
    rw [Matrix.det_one, mul_one]
    have dM : Matrix.det (!![0, -1, 0; -1, 0, 0; 0, 0, -1] : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
      rw [Matrix.det_fin_three]
      simp
    have hM : Anchor3.gaugeL3 = !![0, -1, 0; -1, 0, 0; 0, 0, -1] := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [hM]
    exact dM

theorem gaugeScalar_normSq (H : Fin 4) (l : Label) : Complex.normSq (gaugeScalar H l) = 1 := by
  match H with
  | 0 => exact Anchor0.gaugeC_normSq l
  | 1 => exact map_one Complex.normSq
  | 2 => exact Anchor2.gaugeC_normSq l
  | 3 => exact Anchor3.gaugeC3_normSq l

theorem gaugeScalar_cube (H : Fin 4) (l : Label) : gaugeScalar H l ^ 3 = 1 := by
  match H with
  | 0 => exact gauge_chi_cube _
  | 1 => exact one_pow 3
  | 2 => exact Anchor2.gaugeC_cube l
  | 3 =>
    show Anchor3.gaugeC3 l ^ 3 = 1
    unfold Anchor3.gaugeC3
    split_ifs
    · exact gauge_chi_cube _
    · exact gauge_chi_cube _
    · exact one_pow 3

theorem anchorQuartet_val (ξ : Fin 4 → ℂ) (H : Fin 4) (k : Fin 4) (t : Fin 3) :
    (anchorQuartet ξ H k t).val = quartetConj ξ H * (stdQuartet k t).val * (quartetConj ξ H)ᴴ := by
  match H with
  | 0 =>
    show (stdQuartet k t).val = (1 : TitsComplexMatrix) * (stdQuartet k t).val * (1 : TitsComplexMatrix)ᴴ
    rw [Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul]
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl

theorem quartetConj_unitary {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) :
    quartetConj ξ H * (quartetConj ξ H)ᴴ = 1 := by
  match H with
  | 0 =>
    show (1 : TitsComplexMatrix) * (1 : TitsComplexMatrix)ᴴ = 1
    rw [Matrix.conjTranspose_one, Matrix.mul_one]
  | 1 => exact Anchor1.gQ_unitary
  | 2 => exact Anchor2.g2_unitary ξ hξ
  | 3 => exact Anchor3.g3_unitary ξ hξ

/-- Every raw-family configuration is fixed by the compensated generator of its anchor. -/
theorem kAct_preCfg (ξ₀ : Fin 4 → ℂ) (H : Fin 4) (g h : Mat) (d : PhaseTriple) :
    kAct H (preCfg ξ₀ H g h d) = preCfg ξ₀ H g h d := by
  have hdec : ∀ u : Cfg, (∀ i, decodeVariation u i = prePoint ξ₀ H g h d i) →
      decodeVariation u = decodeVariation (preCfg ξ₀ H g h d) := by
    intro u hu
    funext i
    rw [hu i]
    exact (NativePolynomial.upperCoordinateEquiv.symm_apply_apply _).symm
  apply decodeVariation.injective
  apply hdec
  intro i
  rw [kAct, CKM.NativeIntrinsicTriality.decodeVariation_confGen, compensated_apply]
  obtain ⟨k, rfl⟩ := (anchorRelabel H).surjective i
  rw [anchorRelabel_shift]
  have hp : ∀ j, decodeVariation (preCfg ξ₀ H g h d) j = prePoint ξ₀ H g h d j := fun j =>
    NativePolynomial.upperCoordinateEquiv.symm_apply_apply _
  rw [hp]
  show anchorGenerator H (anchorΨinv H (stdAnchored (anchorQuartet ξ₀ H) (hidFamily ξ₀ H g h d)
      ((anchorRelabel H).symm (anchorRelabel H (stdShift k))))) =
    anchorΨinv H (stdAnchored (anchorQuartet ξ₀ H) (hidFamily ξ₀ H g h d)
      ((anchorRelabel H).symm (anchorRelabel H k)))
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, gauge_gen_Ψinv, R0_stdAnchored]

end CKM.NativeFourFamily

#print axioms CKM.NativeFourFamily.anchorΨinv_comp_anchorΨ
#print axioms CKM.NativeFourFamily.anchorΨ_comp_anchorΨinv
#print axioms CKM.NativeFourFamily.anchorΨ_isNativeAut
#print axioms CKM.NativeFourFamily.anchorΨinv_isNativeAut
#print axioms CKM.NativeFourFamily.anchorΨ_conj
#print axioms CKM.NativeFourFamily.anchorRelabel_shift
#print axioms CKM.NativeFourFamily.anchor_form
#print axioms CKM.NativeFourFamily.prePoint_base
#print axioms CKM.NativeFourFamily.preCfg_base
#print axioms CKM.NativeFourFamily.preMap_zero
#print axioms CKM.NativeFourFamily.gaugeLeft_unitary
#print axioms CKM.NativeFourFamily.gaugeRight_unitary
#print axioms CKM.NativeFourFamily.gauge_det
#print axioms CKM.NativeFourFamily.gaugeScalar_normSq
#print axioms CKM.NativeFourFamily.gaugeScalar_cube
#print axioms CKM.NativeFourFamily.anchorQuartet_val
#print axioms CKM.NativeFourFamily.quartetConj_unitary
#print axioms CKM.NativeFourFamily.kAct_preCfg
