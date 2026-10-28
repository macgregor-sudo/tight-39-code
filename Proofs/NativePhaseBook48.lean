module

public import HTPhaseCompleteHPhase
public import HTPhaseCompleteTValue
public import NativePhaseComplexCommonDeletion
public import NativePhaseStressAnnihilation
public import NativePhaseDictionaryKernel

@[expose] public section

/-! The actual 48 Book rows from native phase stresses. H orientation and every
signed conjugate partner are retained. No additional value or desired-span premise is introduced. -/

noncomputable section
set_option maxRecDepth 2000
namespace Option2.NativeStress.PhaseBook48A6
open MvPolynomial PolynomialJets Matrix
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open AnalyticDerivative AnchorSupport HTPhaseComplete
open PhasePivotA6 PhaseRankA6 PhaseHilbertA6 PhaseStressAnnihilationA6
open PhaseComplexCommonDeletionA6 PhaseRealPolynomialExtA6
open PhaseBookComplexificationA6 PhaseBookDictionaryChangeA6 PhaseDictionaryKernelA6
open PhaseRawBookA6 PhaseCommonHessianA6 PhaseQuadraticCoefficientA6
open BookHT NativePolynomial NativePolynomial.ConfigurationResiduals
open BookHT.NativeNormalKernelBridge (unpackNative pack_unpackNative)
open scoped BigOperators ComplexConjugate

def Annihilates (ξ : Fin 4 → ℂ) (w : Weights) : Prop :=
  ∀ j : Fin 1053, ∑ r : Fin 2184, w r * nativeJ ξ r j = 0

private theorem ann_of_packed_equilibrium (ξ : Fin 4 → ℂ) (w : Weights)
    (h : (stressCovector w).comp
      (fderiv ℝ Option2.NativeStress.originalF (Pxi ξ)) = 0) : Annihilates ξ w := by
  intro j
  have hj := congrArg (fun L : (Fin 1053 → ℝ) →L[ℝ] ℂ => L (Pi.single j 1)) h
  have he (r : Fin 2184) : equationLinearMatrix
      (AnchorSupport.translatedRow (fun v => ((Pxi ξ v : ℝ) : ℂ))) r j = nativeJ ξ r j := rfl
  simpa only [ContinuousLinearMap.comp_apply, _root_.zero_apply, stressCovector_apply,
    fderiv_single_cast, he] using hj

private theorem ann_scale (ξ : Fin 4 → ℂ) (w : Weights) (c : ℂ)
    (h : Annihilates ξ w) : Annihilates ξ (fun r => c * w r) := by
  intro j
  simp only [mul_assoc, ← Finset.mul_sum, h j, mul_zero]

private theorem ann_conj (ξ : Fin 4 → ℂ) (w : Weights)
    (h : Annihilates ξ w) : Annihilates ξ (fun r => conj (w r)) := by
  have hJ (r : Fin 2184) (j : Fin 1053) : conj (nativeJ ξ r j) = nativeJ ξ r j := by
    rw [← realJ_map_complex]
    exact Complex.conj_ofReal _
  intro j
  have hj := congrArg conj (h j)
  simpa only [map_sum, map_mul, hJ, map_zero] using hj

private theorem stress_scale (c : ℂ) (w : Weights) (y : RealResiduals) :
    stressCovector (fun r => c * w r) y = c * stressCovector w y := by
  simp only [stressCovector_apply, Finset.mul_sum, mul_assoc]

private theorem stress_conj (w : Weights) (y : RealResiduals) :
    stressCovector (fun r => conj (w r)) y = conj (stressCovector w y) := by
  simp only [stressCovector_apply, map_sum, map_mul, Complex.conj_ofReal]

def Represents (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (j : Fin 48) (w : Weights) : Prop :=
  Annihilates ξ w ∧ ∀ z : Blocks,
    stressCovector w (Option2.NativeStress.originalF (Pxi ξ + Vxi ξ hξ z)) =
      eval (Dictionary.realCoordinates z) (Dictionary.quadric j)

private theorem H_value (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 4) (a : Fin 3)
    (z : Blocks) :
    stressCovector (ellH ξ hξ i a) (Option2.NativeStress.originalF (Pxi ξ + Vxi ξ hξ z)) =
      Dictionary.selectedH (Dictionary.realCoordinates z) i a := by
  have h := congrArg (fun b : Blocks => (b i).ofLp a) (H_reproduction_phase ξ hξ z)
  rw [Dictionary.selectedH_eq_Book]
  simpa only [residualHxi, residualOf_apply, stressCovector_apply] using h

private theorem H_representative (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (i : Fin 4) (a : Fin 3) :
    ∃ w : Weights, Represents ξ hξ (NativeH.hSpec i a).quadricIndex w := by
  let w := ellH ξ hξ i a
  have ha : Annihilates ξ w := ann_of_packed_equilibrium ξ w (H_equilibrium ξ hξ i a)
  have hv := H_value ξ hξ i a
  cases hc : (NativeH.hSpec i a).conjugated <;> cases hn : (NativeH.hSpec i a).negated
  · refine ⟨w, ha, ?_⟩
    intro z
    simpa only [Dictionary.selectedH, hc, hn, Bool.false_eq_true, ite_false] using hv z
  · refine ⟨(fun r => (-1 : ℂ) * w r), ann_scale ξ w (-1) ha, ?_⟩
    intro z
    rw [stress_scale]
    have h := hv z
    simp only [Dictionary.selectedH, hc, hn, Bool.false_eq_true, ite_false, ite_true] at h
    rw [h]
    ring
  · refine ⟨(fun r => conj (w r)), ann_conj ξ w ha, ?_⟩
    intro z
    rw [stress_conj]
    have h := hv z
    simp only [Dictionary.selectedH, hc, hn, Bool.false_eq_true, ite_false, ite_true] at h
    rw [h]
    simp
  · refine ⟨(fun r => (-1 : ℂ) * conj (w r)), ann_scale ξ _ (-1) (ann_conj ξ w ha), ?_⟩
    intro z
    rw [stress_scale, stress_conj]
    have h := hv z
    simp only [Dictionary.selectedH, hc, hn, ite_true] at h
    rw [h]
    simp

private theorem T_representative (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (i : Fin 4) (a : Fin 3) :
    Represents ξ hξ (Dictionary.tIndex i a) (ellT ξ hξ i a) := by
  refine ⟨ann_of_packed_equilibrium ξ _ (T_equilibrium ξ hξ i a), ?_⟩
  intro z
  rw [stressCovector_apply, T_reproduction_rows, Dictionary.selectedT_eq_Book]

private theorem partner_sign (j : Fin 48) :
    ((Dictionary.quadricBar j).2 : ℂ) * ((Dictionary.quadricBar j).2 : ℂ) = 1 := by
  have h : (Dictionary.quadricBar j).2 * (Dictionary.quadricBar j).2 = 1 := by
    fin_cases j <;> decide
  exact_mod_cast h

private theorem partner_representative (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (j : Fin 48) (w : Weights) (h : Represents ξ hξ j w) :
    Represents ξ hξ (Dictionary.quadricBar j).1
      (fun r => ((Dictionary.quadricBar j).2 : ℂ) * conj (w r)) := by
  refine ⟨ann_scale ξ _ _ (ann_conj ξ w h.1), ?_⟩
  intro z
  rw [stress_scale, stress_conj, h.2, Dictionary.realCoordinates_conjugate_quadric,
    ← mul_assoc, partner_sign, one_mul]

/-- All 48 literal Dictionary labels, including both signs/conjugate partners. -/
theorem all48_representatives (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (j : Fin 48) :
    ∃ w : Weights, Represents ξ hξ j w := by
  obtain ⟨i,a,hj⟩ := Dictionary.representatives_cover j
  obtain ⟨w,hw⟩ := H_representative ξ hξ i a
  rcases hj with hj | hj | hj | hj
  · exact ⟨w, hj ▸ hw⟩
  · exact ⟨_, hj ▸ partner_representative ξ hξ _ w hw⟩
  · exact ⟨_, hj ▸ T_representative ξ hξ i a⟩
  · exact ⟨_, hj ▸ partner_representative ξ hξ _ _ (T_representative ξ hξ i a)⟩

private theorem eval_packed_row (x : Fin 1053 → ℝ) (r : Fin 2184) :
    eval (fun j => (x j : ℂ)) (row r) = (Option2.NativeStress.originalF x r : ℂ) := by
  rw [NativeH.Reproduction.originalF_complex]
  unfold AnchorSupport.row
  rw [QuarticCertificate.RowBridge.eval_fRow]

private theorem book_quadric_value (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (w : Weights) (ha : Annihilates ξ w) (z : Blocks) :
    eval (fun j => ((Vxi ξ hξ z j : ℝ) : ℂ))
      (equationAnnihilatorQuadric (nativeRows ξ) w) =
      stressCovector w (Option2.NativeStress.originalF (Pxi ξ + Vxi ξ hξ z)) := by
  have hP : ∀ r, eval (Xc ξ) (row r) = 0 := by
    intro r
    rw [eval_packed_row]
    have hr : Option2.NativeStress.originalF (Pxi ξ) r = 0 := literalCfg_all_original_F ξ hξ r
    rw [hr, Complex.ofReal_zero]
  have h := contractedF_add_eq_quadratic (Xc ξ) w hP ha
    (fun j => ((Vxi ξ hξ z j : ℝ) : ℂ))
  have hs : Xc ξ + (fun j => ((Vxi ξ hξ z j : ℝ) : ℂ)) =
      (fun j => (((Pxi ξ + Vxi ξ hξ z) j : ℝ) : ℂ)) := by
    funext j
    simp only [Pi.add_apply, Complex.ofReal_add, Xc]
  rw [hs] at h
  have hr : nativeRows ξ = AnchorSupport.translatedRow (Xc ξ) := rfl
  rw [contractedQuadratic, ← hr] at h
  simpa only [contractedF, eval_packed_row, stressCovector_apply] using h.symm

private theorem eval_linSubst {σ τ : Type*} [Fintype τ]
    (A : Matrix σ τ ℂ) (P : MvPolynomial σ ℂ) (x : τ → ℂ) :
    eval x (ChainMid.linSubst A P) = eval (A *ᵥ x) P := by
  unfold ChainMid.linSubst
  change eval x (eval₂ C (fun j => ∑ t, C (A j t)*X t) P) = _
  rw [← MvPolynomial.eval_assoc]
  apply congrArg (fun v : σ → ℂ => eval v P)
  funext j
  simp [Function.comp_apply, Matrix.mulVec, dotProduct]

private theorem stressHessian_apply (ξ : Fin 4 → ℂ)
    (ell : (Fin 2184 → ℝ) →L[ℝ] ℂ) (u v : Cfg) :
    stressHessian ξ ell u v =
      ell (fderiv ℝ (fderiv ℝ AnalyticDerivative.originalF) (literalCfg ξ) u v) := rfl

set_option maxRecDepth 2000 in
private theorem zero_common_book_value {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)
    (w : Weights) (ha : Annihilates ξ w) (z : Blocks) :
    realEval (Sum.elim (fun _ : Fin 56 => 0) (bookRealEquiv z)) (pulledbackQuadric hξ w) =
      stressCovector w (Option2.NativeStress.originalF (Pxi ξ + Vxi ξ hξ.1 z)) := by
  rw [realEval_pulledback]
  have hm : realModelCoordinates hξ (Sum.elim (fun _ : Fin 56 => 0) (bookRealEquiv z)) =
      (((0 : orbitC ξ),(0 : fixQK ξ)),z) := by
    change ((commonRealEquiv hξ).symm 0, bookRealEquiv.symm (bookRealEquiv z)) = _
    rw [map_zero, LinearEquiv.symm_apply_apply]
    rfl
  rw [hm, rawBookEquiv_book, stressHessian_apply, ← native_quadratic_coefficient]
  have hp : complexPack (unpackNative (Vxi ξ hξ.1 z)) =
      (fun j => ((Vxi ξ hξ.1 z j : ℝ) : ℂ)) := by
    unfold complexPack
    rw [pack_unpackNative]
  rw [hp]
  exact book_quadric_value ξ hξ.1 w ha z

def entryDictionaryQuadric (j : Fin 48) : A6Polynomial :=
  ChainMid.linSubst dictionaryCoordinatesMatrix
    (rename (Sum.inr : Fin 24 → DictionaryCoordinateIndex) (Dictionary.quadric j))

private theorem entryDictionary_eval (j : Fin 48) (c : Fin 56 → ℝ) (z : Blocks) :
    realEval (Sum.elim c (bookRealEquiv z)) (entryDictionaryQuadric j) =
      eval (Dictionary.realCoordinates z) (Dictionary.quadric j) := by
  rw [realEval, entryDictionaryQuadric, eval_linSubst, dictionaryCoordinatesMatrix,
    LinearMap.toMatrix'_mulVec]
  have hx : (fun k => ((Sum.elim c (bookRealEquiv z) k : ℝ) : ℂ)) =
      Sum.elim (fun i => (c i : ℂ)) (fun p => ((bookRealEquiv z p : ℝ) : ℂ)) := by
    funext k
    cases k <;> rfl
  rw [hx]
  change eval (dictionaryCoordinatesChange
    (Sum.elim (fun i => (c i : ℂ)) (fun p => ((bookRealEquiv z p : ℝ) : ℂ))))
    (rename (Sum.inr : Fin 24 → DictionaryCoordinateIndex) (Dictionary.quadric j)) = _
  rw [dictionaryCoordinatesChange_realCoordinates, eval_rename]
  rfl

set_option maxRecDepth 2000 in
private theorem representative_entry_identity {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)
    (j : Fin 48) (w : Weights) (hw : Represents ξ hξ.1 j w) :
    pulledbackQuadric hξ w = entryDictionaryQuadric j := by
  apply polynomial_ext_real
  intro x
  let c : Fin 56 → ℝ := fun i => x (.inl i)
  let z := bookRealEquiv.symm (fun p => x (.inr p))
  have hx : x = Sum.elim c (bookRealEquiv z) := by
    funext k
    cases k with
    | inl i => rfl
    | inr p => exact (congrFun (bookRealEquiv.apply_symm_apply (fun p => x (.inr p))) p).symm
  rw [hx, realEval_pulledback_book_only hξ w (native_jacobian_annihilation ξ w hw.1),
    zero_common_book_value hξ w hw.1, hw.2, entryDictionary_eval]

private theorem subst_comp {ρ σ τ : Type*} [Fintype σ] [Fintype τ]
    (A : Matrix ρ σ ℂ) (B : Matrix σ τ ℂ) (P : MvPolynomial ρ ℂ) :
    ChainMid.linSubst B (ChainMid.linSubst A P) = ChainMid.linSubst (A*B) P :=
  congrArg (fun f => f P) (ChainMid.linSubst_comp B A)

private theorem representative_dictionary_identity {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ)
    (j : Fin 48) (w : Weights) (hw : Represents ξ hξ.1 j w) :
    ChainMid.linSubst (nativeDictionaryComplexMatrix hξ)
        (equationAnnihilatorQuadric (nativeRows ξ) w) =
      rename (Sum.inr : Fin 24 → DictionaryCoordinateIndex) (Dictionary.quadric j) := by
  have h := congrArg (ChainMid.linSubst dictionaryCoordinatesInverseMatrix)
    (representative_entry_identity hξ j w hw)
  simpa only [pulledbackQuadric, entryDictionaryQuadric, subst_comp,
    dictionaryCoordinatesMatrix_mul_inverse, ChainMid.linSubst_one, AlgHom.id_apply,
    nativeDictionaryComplexMatrix] using h

/-- Actual weights for every one of the 48 unchanged Dictionary rows, with
all native columns annihilated and exact complex polynomial identities. -/
theorem native_book48 {ξ : Fin 4 → ℂ} (hξ : IsGoodPhase ξ) :
    ∃ w : Fin 48 → Weights,
      (∀ s, Annihilates ξ (w s)) ∧
      ∀ s, ChainMid.linSubst (nativeDictionaryComplexMatrix hξ)
        (equationAnnihilatorQuadric (nativeRows ξ) (w s)) =
        rename (Sum.inr : Fin 24 → DictionaryCoordinateIndex) (Dictionary.quadric s) := by
  choose w hw using all48_representatives ξ hξ.1
  exact ⟨w, fun s => (hw s).1, fun s => representative_dictionary_identity hξ s (w s) (hw s)⟩

/-- D6 with the actual normalized kernel and inverse coordinate matrices.
Each target is itself a transformed native stress quadric, hence lies in their span. -/
theorem native_book48_D6 (u : PhasePivotLocusA6.NativePhaseTorus)
    (hξ : IsGoodPhase u.1) (hp : u ∈ PhasePivotLocusA6.nativePivotLocus) :
    ∃ (B : Matrix (Fin 1053) (Fin 80) ℂ) (piv : Fin 80 → Fin 1053)
      (M : Matrix (Fin 80) DictionaryCoordinateIndex ℂ)
      (N : Matrix DictionaryCoordinateIndex (Fin 80) ℂ) (w : Fin 48 → Weights),
      SliceLemmas.IsPivot B piv ∧
      (∀ r t, ∑ j, nativeJ u.1 r j * B j t = 0) ∧ M*N=1 ∧ N*M=1 ∧
      (∀ s, Annihilates u.1 (w s)) ∧
      ∀ k, rename (Sum.inr : Fin 24 → DictionaryCoordinateIndex) (Dictionary.quadric k) ∈
        Submodule.span ℂ (Set.range fun s =>
          ChainMid.linSubst M (ChainMid.restrictedQuadric B (nativeRows u.1) w s)) := by
  obtain ⟨B,piv,M,N,hB,hJB,_,hBM,hMN,hNM⟩ := native_dictionary_change u hξ hp
  obtain ⟨w,hw,hq⟩ := native_book48 hξ
  refine ⟨B,piv,M,N,w,hB,hJB,hMN,hNM,hw,?_⟩
  intro k
  apply Submodule.subset_span
  refine ⟨k, ?_⟩
  change ChainMid.linSubst M
    (ChainMid.linSubst B (equationAnnihilatorQuadric (nativeRows u.1) (w k))) = _
  rw [subst_comp, hBM, hq]

#print axioms Option2.NativeStress.PhaseBook48A6.all48_representatives
#print axioms Option2.NativeStress.PhaseBook48A6.native_book48
#print axioms Option2.NativeStress.PhaseBook48A6.native_book48_D6

end Option2.NativeStress.PhaseBook48A6
