module

public import BookNativeNormalKernelBridge
public import A5SliceB

@[expose] public section

/-! Strengthened actual four-anchor compensation. The unchanged first-party
A5Comp witness and per-anchor identities are reproduced with the Cartan support
retained in the public conclusion; no stronger statement is extracted from an
opaque weaker existential. Accepted sources remain untouched. -/
set_option Elab.async false
noncomputable section
open CKM.NativeFirstOrder CKM.NativeGroupSlice CompactAlbert UnitaryErrorBases
open scoped Matrix Topology
namespace CKM.NativeFourFamily.CartanSuccessor

theorem comp_of_data_cartan {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4)
    (Nv Nw Nβ : Fin 3 → Fin 4 → ℤ) (Ne : Fin 2 → Fin 4 → ℤ) (κ κ' : (Fin 4 → ℝ) → ℂ)
    (hβ : ∀ a, Nβ 0 a + Nβ 1 a + Nβ 2 a = 0)
    (hdet : ∀ a, Nv 0 a + Nv 1 a + Nv 2 a = Nw 0 a + Nw 1 a + Nw 2 a)
    (hQ : ∀ θ, compPhDiag (compLin Nv θ) * quartetConj ξ₀ H = quartetConj (commonPhase ξ₀ θ) H)
    (hL : ∀ θ, compM (compPhDiag (compLin Nv θ)) * compM (compPhDiag (compLin Nβ θ)) *
      gaugeLeft ξ₀ H = κ θ • gaugeLeft (commonPhase ξ₀ θ) H)
    (hR : ∀ θ, gaugeRight ξ₀ H * compM (compPhDiag (compLin (-Nw) θ)) =
      κ' θ • gaugeRight (commonPhase ξ₀ θ) H)
    (hκ : ∀ θ, κ θ * κ' θ = 1)
    (hd : ∀ θ j, anchorPhases ξ₀ H j *
      Complex.exp (((torusAngles (compLin Ne θ) j : ℝ) : ℂ) * Complex.I) =
        anchorPhases (commonPhase ξ₀ θ) H j) :
    ∃ (A : (Fin 4 → ℝ) → CEnd) (k : (Fin 4 → ℝ) → Fin 8 → ℝ) (e : (Fin 4 → ℝ) → Fin 2 → ℝ),
      AnalyticAt ℝ A 0 ∧ A 0 = 1 ∧ (∀ θ, A θ ∈ autC) ∧
      AnalyticAt ℝ k 0 ∧ k 0 = 0 ∧ AnalyticAt ℝ e 0 ∧ e 0 = 0 ∧
      (∀ θ m, m ≠ 2 → m ≠ 7 → k θ m = 0) ∧
      ∀ θ, literalCfg (commonPhase ξ₀ θ) = actC (A θ) (preMap ξ₀ hξ₀ H (k θ, 0, e θ)) := by
  have hβsum : ∀ θ, compLin Nβ θ 0 + compLin Nβ θ 1 + compLin Nβ θ 2 = 0 := fun θ => by
    rw [compLin_sum3]
    simp [hβ]
  refine ⟨fun θ => coordEnd (anchorΨinv H ∘ₗ
      titsTwoSided (compPhDiag (compLin Nv θ)) (compPhDiag (compLin Nw θ)) ∘ₗ anchorΨ H),
    fun θ => cartanCoord (compLin Nβ θ), compLin Ne,
    comp_analyticAt_A H (compLin_analyticAt Nv 0) (compLin_analyticAt Nw 0), ?_, fun θ => ?_,
    ?_, ?_, compLin_analyticAt Ne 0, compLin_zero Ne, ?_, fun θ => ?_⟩
  · simp only [compLin_zero, compPhDiag_zero, titsTwoSided_one, LinearMap.id_comp,
      anchorΨinv_comp_anchorΨ]
    exact map_one coordEnd
  · refine comp_mem_autC H (compPhDiag_unitary _) (compPhDiag_unitary _) ?_
    rw [compPhDiag_det, compPhDiag_det, compLin_sum3, compLin_sum3]
    simp only [hdet]
  · exact (LinearMap.toContinuousLinearMap compCartanL).analyticAt _ |>.comp
      (compLin_analyticAt Nβ 0)
  · simp [compLin_zero, cartanCoord]
  · intro θ m hm2 hm7
    have h2 : (2 : Fin 8) ≠ m := fun h => hm2 h.symm
    have h7 : (7 : Fin 8) ≠ m := fun h => hm7 h.symm
    simp [cartanCoord, h2, h7]
  · have hξ := isUnitPhase_commonPhase hξ₀ θ
    have htor : torusPhase (anchorTriple ξ₀ hξ₀ H) (compLin Ne θ) =
        anchorTriple (commonPhase ξ₀ θ) hξ H :=
      Subtype.ext (funext fun j => hd θ j)
    unfold preMap
    simp only
    rw [suExp_zero, suExp_cartanCoord _ (hβsum θ), htor]
    have hR' : gaugeRight ξ₀ H * (compM (compPhDiag (compLin Nw θ)))ᴴ =
        κ' θ • gaugeRight (commonPhase ξ₀ θ) H := by
      rw [← hR θ, compLin_neg]
      congr 1
      exact compPhDiag_conjTranspose _
    exact comp_cfg (v := compM (compPhDiag (compLin Nv θ))) (w := compM (compPhDiag (compLin Nw θ)))
      (g := compM (compPhDiag (compLin Nβ θ))) hξ H (compPhDiag_unitary _) (hQ θ) (hL θ) hR' (hκ θ)

theorem comp_anchor0_cartan {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) :
    ∃ (A : (Fin 4 → ℝ) → CEnd) (k : (Fin 4 → ℝ) → Fin 8 → ℝ) (e : (Fin 4 → ℝ) → Fin 2 → ℝ),
      AnalyticAt ℝ A 0 ∧ A 0 = 1 ∧ (∀ θ, A θ ∈ autC) ∧
      AnalyticAt ℝ k 0 ∧ k 0 = 0 ∧ AnalyticAt ℝ e 0 ∧ e 0 = 0 ∧
      (∀ θ m, m ≠ 2 → m ≠ 7 → k θ m = 0) ∧
      ∀ θ, literalCfg (commonPhase ξ₀ θ) = actC (A θ) (preMap ξ₀ hξ₀ 0 (k θ, 0, e θ)) := by
  have h0 : ξ₀ 0 ≠ 0 := fun h => by simpa [h] using hξ₀ 0
  have h1 : ξ₀ 1 ≠ 0 := fun h => by simpa [h] using hξ₀ 1
  have h2 : ξ₀ 2 ≠ 0 := fun h => by simpa [h] using hξ₀ 2
  have h3 : ξ₀ 3 ≠ 0 := fun h => by simpa [h] using hξ₀ 3
  refine comp_of_data_cartan hξ₀ 0 ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
    ![![0, 0, -1, 1], ![0, 0, -1, -2], ![0, 0, 2, 1]]
    ![![0, 0, 2, 1], ![0, 0, -1, -2], ![0, 0, -1, 1]]
    ![![3, 3, -3, 0], ![-3, 0, 0, -3]]
    (fun θ => compF θ 3 * (compF θ 2)⁻¹) (fun θ => compF θ 2 * (compF θ 3)⁻¹)
    (by decide) (by decide) (fun θ => ?_) (fun θ => ?_) (fun θ => ?_) (fun θ => ?_) (fun θ j => ?_)
  all_goals have F0 := compF_ne_zero θ 0
  all_goals have F1 := compF_ne_zero θ 1
  all_goals have F2 := compF_ne_zero θ 2
  all_goals have F3 := compF_ne_zero θ 3
  · rw [compLin_zero_rows, compPhDiag_zero, one_mul]
    rfl
  · ext i j
    rw [comp_left_entry]
    rcases Anchor0.indexCases i with rfl | rfl | rfl <;>
      rcases Anchor0.indexCases j with rfl | rfl | rfl <;>
      simp [gaugeLeft, Anchor0.gaugeL, Fin.prod_univ_four, commonPhase_compF] <;> field_simp
  · ext i j
    rw [comp_right_entry]
    rcases Anchor0.indexCases i with rfl | rfl | rfl <;>
      rcases Anchor0.indexCases j with rfl | rfl | rfl <;>
      simp [gaugeRight, Anchor0.gaugeR, Fin.prod_univ_four, commonPhase_compF] <;> field_simp
  · field_simp
  · rw [comp_torus_exp]
    rcases Anchor0.indexCases j with rfl | rfl | rfl <;>
      simp [anchorPhases, Fin.prod_univ_four, commonPhase_compF] <;> field_simp

theorem comp_anchor1_cartan {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) :
    ∃ (A : (Fin 4 → ℝ) → CEnd) (k : (Fin 4 → ℝ) → Fin 8 → ℝ) (e : (Fin 4 → ℝ) → Fin 2 → ℝ),
      AnalyticAt ℝ A 0 ∧ A 0 = 1 ∧ (∀ θ, A θ ∈ autC) ∧
      AnalyticAt ℝ k 0 ∧ k 0 = 0 ∧ AnalyticAt ℝ e 0 ∧ e 0 = 0 ∧
      (∀ θ m, m ≠ 2 → m ≠ 7 → k θ m = 0) ∧
      ∀ θ, literalCfg (commonPhase ξ₀ θ) = actC (A θ) (preMap ξ₀ hξ₀ 1 (k θ, 0, e θ)) := by
  have h0 : ξ₀ 0 ≠ 0 := fun h => by simpa [h] using hξ₀ 0
  have h1 : ξ₀ 1 ≠ 0 := fun h => by simpa [h] using hξ₀ 1
  have h2 : ξ₀ 2 ≠ 0 := fun h => by simpa [h] using hξ₀ 2
  have h3 : ξ₀ 3 ≠ 0 := fun h => by simpa [h] using hξ₀ 3
  refine comp_of_data_cartan hξ₀ 1 ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
    ![![1, -1, 0, 0], ![1, 2, 0, 0], ![-2, -1, 0, 0]]
    ![![-2, -1, 0, 0], ![1, 2, 0, 0], ![1, -1, 0, 0]]
    ![![3, 0, 3, 3], ![0, 3, -3, 0]]
    (fun θ => compF θ 0 * (compF θ 1)⁻¹) (fun θ => compF θ 1 * (compF θ 0)⁻¹)
    (by decide) (by decide) (fun θ => ?_) (fun θ => ?_) (fun θ => ?_) (fun θ => ?_) (fun θ j => ?_)
  all_goals have F0 := compF_ne_zero θ 0
  all_goals have F1 := compF_ne_zero θ 1
  all_goals have F2 := compF_ne_zero θ 2
  all_goals have F3 := compF_ne_zero θ 3
  · rw [compLin_zero_rows, compPhDiag_zero, one_mul]
    rfl
  · show compPhDiag (compLin _ θ) * compPhDiag (compLin _ θ) * Anchor1.Lg ξ₀ =
      (compF θ 0 * (compF θ 1)⁻¹) • Anchor1.Lg (commonPhase ξ₀ θ)
    ext i j
    rw [comp_left_entryT, Matrix.smul_apply]
    fin_cases i <;> fin_cases j <;>
      simp [Anchor1.Lg, Fin.prod_univ_four, commonPhase_compF] <;> field_simp
  · show Anchor1.Rg ξ₀ * compPhDiag (compLin _ θ) =
      (compF θ 1 * (compF θ 0)⁻¹) • Anchor1.Rg (commonPhase ξ₀ θ)
    ext i j
    rw [comp_right_entryT, Matrix.smul_apply]
    fin_cases i <;> fin_cases j <;>
      simp [Anchor1.Rg, Fin.prod_univ_four, commonPhase_compF] <;> field_simp
  · field_simp
  · rw [comp_torus_exp]
    rcases Anchor0.indexCases j with rfl | rfl | rfl <;>
      simp [anchorPhases, Fin.prod_univ_four, commonPhase_compF] <;> field_simp

theorem comp_anchor2_cartan {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) :
    ∃ (A : (Fin 4 → ℝ) → CEnd) (k : (Fin 4 → ℝ) → Fin 8 → ℝ) (e : (Fin 4 → ℝ) → Fin 2 → ℝ),
      AnalyticAt ℝ A 0 ∧ A 0 = 1 ∧ (∀ θ, A θ ∈ autC) ∧
      AnalyticAt ℝ k 0 ∧ k 0 = 0 ∧ AnalyticAt ℝ e 0 ∧ e 0 = 0 ∧
      (∀ θ m, m ≠ 2 → m ≠ 7 → k θ m = 0) ∧
      ∀ θ, literalCfg (commonPhase ξ₀ θ) = actC (A θ) (preMap ξ₀ hξ₀ 2 (k θ, 0, e θ)) := by
  have h0 : ξ₀ 0 ≠ 0 := fun h => by simpa [h] using hξ₀ 0
  have h1 : ξ₀ 1 ≠ 0 := fun h => by simpa [h] using hξ₀ 1
  have h2 : ξ₀ 2 ≠ 0 := fun h => by simpa [h] using hξ₀ 2
  have h3 : ξ₀ 3 ≠ 0 := fun h => by simpa [h] using hξ₀ 3
  refine comp_of_data_cartan hξ₀ 2
    ![![0, 0, 0, 0], ![3, 0, 0, 0], ![0, -3, 0, 0]]
    ![![1, -1, 2, 1], ![1, -1, -1, 1], ![1, -1, -1, -2]]
    ![![1, -1, 2, 1], ![-2, -1, -1, -2], ![1, 2, -1, 1]]
    ![![0, 0, 3, 3], ![0, 0, -3, 0]]
    (fun θ => compF θ 0 * (compF θ 1)⁻¹ * compF θ 2 ^ 2 * compF θ 3)
    (fun θ => (compF θ 0)⁻¹ * compF θ 1 * (compF θ 2 ^ 2)⁻¹ * (compF θ 3)⁻¹)
    (by decide) (by decide) (fun θ => ?_) (fun θ => ?_) (fun θ => ?_) (fun θ => ?_) (fun θ j => ?_)
  all_goals have F0 := compF_ne_zero θ 0
  all_goals have F1 := compF_ne_zero θ 1
  all_goals have F2 := compF_ne_zero θ 2
  all_goals have F3 := compF_ne_zero θ 3
  · rw [compPhDiag_compLin]
    simp only [quartetConj, Anchor2.g2, Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    fin_cases j <;> simp [Fin.prod_univ_four, commonPhase_compF]
    field_simp
  · ext i j
    rw [comp_left_entry]
    rcases Anchor0.indexCases i with rfl | rfl | rfl <;>
      rcases Anchor0.indexCases j with rfl | rfl | rfl <;>
      simp [gaugeLeft, Anchor2.gaugeL, Anchor2.gaugeLv, Fin.prod_univ_four, commonPhase_compF] <;>
      field_simp
  · ext i j
    rw [comp_right_entry]
    rcases Anchor0.indexCases i with rfl | rfl | rfl <;>
      rcases Anchor0.indexCases j with rfl | rfl | rfl <;>
      simp [gaugeRight, Anchor2.gaugeR, Anchor2.gaugeRv, Fin.prod_univ_four, commonPhase_compF] <;>
      field_simp
  · field_simp
  · rw [comp_torus_exp]
    rcases Anchor0.indexCases j with rfl | rfl | rfl <;>
      simp [anchorPhases, Fin.prod_univ_four, commonPhase_compF] <;> field_simp

theorem comp_anchor3_cartan {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) :
    ∃ (A : (Fin 4 → ℝ) → CEnd) (k : (Fin 4 → ℝ) → Fin 8 → ℝ) (e : (Fin 4 → ℝ) → Fin 2 → ℝ),
      AnalyticAt ℝ A 0 ∧ A 0 = 1 ∧ (∀ θ, A θ ∈ autC) ∧
      AnalyticAt ℝ k 0 ∧ k 0 = 0 ∧ AnalyticAt ℝ e 0 ∧ e 0 = 0 ∧
      (∀ θ m, m ≠ 2 → m ≠ 7 → k θ m = 0) ∧
      ∀ θ, literalCfg (commonPhase ξ₀ θ) = actC (A θ) (preMap ξ₀ hξ₀ 3 (k θ, 0, e θ)) := by
  have h0 : ξ₀ 0 ≠ 0 := fun h => by simpa [h] using hξ₀ 0
  have h1 : ξ₀ 1 ≠ 0 := fun h => by simpa [h] using hξ₀ 1
  have h2 : ξ₀ 2 ≠ 0 := fun h => by simpa [h] using hξ₀ 2
  have h3 : ξ₀ 3 ≠ 0 := fun h => by simpa [h] using hξ₀ 3
  refine comp_of_data_cartan hξ₀ 3
    ![![0, 0, 0, 0], ![0, 0, -3, 0], ![0, 0, 0, 3]]
    ![![0, 0, -1, 1], ![0, 0, -1, 1], ![0, 0, -1, 1]]
    ![![0, 0, -1, 1], ![0, 0, 2, 1], ![0, 0, -1, -2]]
    ![![-3, 0, 0, 0], ![0, -3, 0, 0]]
    (fun θ => compF θ 3 * (compF θ 2)⁻¹) (fun θ => compF θ 2 * (compF θ 3)⁻¹)
    (by decide) (by decide) (fun θ => ?_) (fun θ => ?_) (fun θ => ?_) (fun θ => ?_) (fun θ j => ?_)
  all_goals have F0 := compF_ne_zero θ 0
  all_goals have F1 := compF_ne_zero θ 1
  all_goals have F2 := compF_ne_zero θ 2
  all_goals have F3 := compF_ne_zero θ 3
  · rw [compPhDiag_compLin]
    simp only [quartetConj, Anchor3.g3, Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    fin_cases j <;> simp [Anchor3.gD, Fin.prod_univ_four, commonPhase_compF]
    field_simp
  · ext i j
    rw [comp_left_entry]
    rcases Anchor0.indexCases i with rfl | rfl | rfl <;>
      rcases Anchor0.indexCases j with rfl | rfl | rfl <;>
      simp [gaugeLeft, Anchor3.gaugeL3, Fin.prod_univ_four] <;> field_simp
  · ext i j
    rw [comp_right_entry]
    rcases Anchor0.indexCases i with rfl | rfl | rfl <;>
      rcases Anchor0.indexCases j with rfl | rfl | rfl <;>
      simp [gaugeRight, Fin.prod_univ_four]
  · field_simp
  · rw [comp_torus_exp]
    rcases Anchor0.indexCases j with rfl | rfl | rfl <;>
      simp [anchorPhases, Fin.prod_univ_four, commonPhase_compF] <;> field_simp

theorem exists_compensation_cartan {ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) :
    ∃ (A : (Fin 4 → ℝ) → CEnd) (k : (Fin 4 → ℝ) → Fin 8 → ℝ)
      (e : (Fin 4 → ℝ) → Fin 2 → ℝ),
      AnalyticAt ℝ A 0 ∧ A 0 = 1 ∧ (∀ θ, A θ ∈ autC) ∧
      AnalyticAt ℝ k 0 ∧ k 0 = 0 ∧ AnalyticAt ℝ e 0 ∧ e 0 = 0 ∧
      (∀ θ m, m ≠ 2 → m ≠ 7 → k θ m = 0) ∧
      ∀ θ, literalCfg (commonPhase ξ θ) = actC (A θ) (preMap ξ hξ H (k θ, 0, e θ)) := by
  fin_cases H
  · exact comp_anchor0_cartan hξ
  · exact comp_anchor1_cartan hξ
  · exact comp_anchor2_cartan hξ
  · exact comp_anchor3_cartan hξ

/-- Cartan support survives the actual derivative, without an assumed derivative formula. -/
theorem fderiv_cartan_support {k : (Fin 4 → ℝ) → Fin 8 → ℝ}
    (hk : AnalyticAt ℝ k 0)
    (hs : ∀ θ m, m ≠ 2 → m ≠ 7 → k θ m = 0)
    (θ : Fin 4 → ℝ) (m : Fin 8) (hm2 : m ≠ 2) (hm7 : m ≠ 7) :
    fderiv ℝ k 0 θ m = 0 := by
  have hproj : HasFDerivAt (fun y : Fin 8 → ℝ => y m)
      (ContinuousLinearMap.proj m : (Fin 8 → ℝ) →L[ℝ] ℝ) (k 0) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := Fin 8 → ℝ) (F := ℝ)
      (ContinuousLinearMap.proj m)
  have hp : HasFDerivAt (fun x => k x m)
      ((ContinuousLinearMap.proj m : (Fin 8 → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ k 0)) 0 :=
    hproj.comp 0 hk.differentiableAt.hasFDerivAt
  have he : (fun x => k x m) = fun _ : Fin 4 → ℝ => (0 : ℝ) :=
    funext fun x => hs x m hm2 hm7
  rw [he] at hp
  have hz := hp.unique (hasFDerivAt_const (0 : ℝ) (0 : Fin 4 → ℝ))
  exact congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] ℝ => L θ) hz

end CKM.NativeFourFamily.CartanSuccessor
#check @CKM.NativeFourFamily.CartanSuccessor.exists_compensation_cartan
#print axioms CKM.NativeFourFamily.CartanSuccessor.exists_compensation_cartan
#print axioms CKM.NativeFourFamily.CartanSuccessor.fderiv_cartan_support
