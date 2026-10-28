module

public import HTPhaseCompleteHRoot
public import HTPhaseCompleteHValue
public import HTPCValReduce

@[expose] public section

/-!
# The H value at every unit phase, every quartet (first-party)

`H_reproduction_phase ξ hξ z : residualHxi ξ hξ (originalF (Pxi ξ + Vxi ξ hξ z)) = BookHT.H z` for every unit `ξ`
(resonant included), with the actual `Vxi`, the transported covectors `ellH` (HTPhaseCompleteHPack) and the
unchanged Book model. Chain, per component `(i, a)`, `y = realCoordinates z`, `U = ξ / exactPhases`, `E = d_i(U)⁻¹`:
1. `value_reduce` (VALUE, gauge lemma at `Pξ`): `Σ ellRaw·F(Pξ + Vξ z) = Σ ellRaw·Q(N(y)·Pξ)`; its column hypothesis is
   `ellRaw_col` (from `ellRaw_equilibrium` through the accepted derivative `originalF_hasFDerivAt`).
2. `quad_transport`: `Σ ellRaw·Q(w) = qH(E·w)` (row covariance + accepted anchor line identity).
3. `anchor_root`: `qH(E·N(y)Pξ) = qH(N(χ·y)·P)`, `χ_j = U^{rootExp i j}` (E·Pξ = P on the quartet states; root property
   `root_N`); the non-anchor states never enter (`qH_anchor_congr`).
4. `base_reduce` (gauge lemma at the base, COMPLEX coefficients) and `kop_base`: `qH(N(y')P) = qH(V y')`.
5. `hom_V_book`: `homogeneousH(V y') = Σ_{t ∈ hBook i a} c_t y'_p y'_q` for COMPLEX `y'` (accepted fixed-seed Kronecker
   identity `component_identity` with the accepted checks `hCheck`, `hBound`).
6. `bookSum_weight` + kernel check `bookW`: every Book term has `rootExp p + rootExp q = cExp i a`, so the factor
   `U^{cExp}` cancels the normalisation of `ellH`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

noncomputable section

namespace Option2.NativeStress.HTPhaseComplete

open scoped BigOperators
open MvPolynomial NativePolynomial QuarticCertificate.RowBridge ConfigurationResidualIndices
open NativePolynomial.ConfigurationResiduals PolynomialJets AnchorSupport
open Option2.NativeStress.HTPhaseKron CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open Option2.NativeStress.BookHT Option2.NativeStress.BookHT.TangentCoordinates
open QuadraticCertificate.ExactCKMConfiguration

/-! ## 1. Column equilibrium of the transported weights -/

theorem fderiv_single_cast (C : Fin 1053 → ℝ) (r : Fin 2184) (c : Fin 1053) :
    (((fderiv ℝ Option2.NativeStress.originalF C (Pi.single c 1)) r : ℝ) : ℂ) =
      equationLinearMatrix (translatedRow (fun v => ((C v : ℝ) : ℂ))) r c := by
  rw [(NativeT.originalF_hasFDerivAt C).fderiv, ← NativeT.original_column_cast]
  congr 1
  simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem ellRaw_col (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 4) (a : Fin 3) (c : Fin 1053) :
    ∑ r, ellRaw ξ hξ i a r * equationLinearMatrix (translatedRow (Xc ξ)) r c = 0 := by
  have h := congrArg (fun L : (Fin 1053 → ℝ) →L[ℝ] ℂ => L (Pi.single c 1)) (ellRaw_equilibrium ξ hξ i a)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
    AnalyticDerivative.stressCovector_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [fderiv_single_cast]

theorem ellRaw_colJ (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 4) (a : Fin 3) (c : Fin 1053) :
    ∑ r, ellRaw ξ hξ i a r * jacobianEntry (1/2 : ℂ) (1/3 : ℂ) r (Xc ξ) c = 0 := by
  rw [← ellRaw_col ξ hξ i a c]
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  exact (equationLinearMatrix_translate_fRow _ _ _ r c).symm

/-! ## 2. Transport of the quadratic part -/

theorem quad_transport (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 4) (a : Fin 3) (w : Fin 1053 → ℂ) :
    ∑ r, ellRaw ξ hξ i a r * quadraticPartValue (1/2 : ℂ) r w =
      eval (stateAct (invCartan (Ux ξ hξ) i) w) (qH i a) := by
  have h1 := contractedF_transport (Ux ξ hξ) i a (Xc ξ + (1 : ℂ) • w)
  rw [stateAct_add] at h1
  have h2 := contractedF_line_eq_quadratic_at_anchor Pbase (NativeH.weightC i a) i Pbase_solution
    (Pbase_equilibrium i a) (NativeH.hasAnchorSupport Pbase i a) _ (transported_anchor ξ hξ i)
    (stateAct (invCartan (Ux ξ hξ) i) w) 1
  rw [one_pow, one_mul] at h2
  have h3 : contractedF (ellRaw ξ hξ i a) (Xc ξ + (1 : ℂ) • w) =
      ∑ r, ellRaw ξ hξ i a r * quadraticPartValue (1/2 : ℂ) r w := by
    unfold contractedF
    simp only [one_smul, row, eval_fRow, NativeH.Reproduction.rowValue_add, F_at_literal ξ hξ, zero_add,
      mul_add, Finset.sum_add_distrib]
    have hl : ∑ r, ellRaw ξ hξ i a r * ∑ c, jacobianEntry (1/2 : ℂ) (1/3 : ℂ) r (Xc ξ) c * w c = 0 := by
      simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro c _
      rw [← Finset.sum_mul, ellRaw_colJ, zero_mul]
    rw [hl, zero_add]
  rw [← h3, qH]
  rw [ellRaw] at h3 ⊢
  rw [h1]
  exact h2

/-! ## 3. Anchors and the root property -/

theorem invCartan_root (U : Fin 4 → ℂˣ) (i : Fin 4) (j : Fin 24) (s : Fin 27 → ℂ) :
    invCartan U i (nLin j s) = mono U (rootExp i j) • nLin j (invCartan U i s) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by fin_cases i <;> simp
  rcases hi with rfl | rfl | rfl | rfl
  · rw [invCartan_low U 0 (Or.inl rfl), invCartan_low U 0 (Or.inl rfl)]
    simp [rootExp, mono_zero]
  · rw [invCartan_low U 1 (Or.inr rfl), invCartan_low U 1 (Or.inr rfl)]
    simp [rootExp, mono_zero]
  · exact root_N U 2 (Or.inl rfl) j s
  · exact root_N U 3 (Or.inr rfl) j s

theorem nLin_apply (j : Fin 24) (s : Fin 27 → ℂ) (m : Fin 27) : nLin j s m = ∑ n, nEnt j m n * s n := rfl

theorem mv_nOp (y : Fin 24 → ℂ) (s : Fin 27 → ℂ) : mv (nOp Q12.toComplex y) s = ∑ j, y j • nLin j s := by
  funext m
  simp only [mv, nOp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, nLin_apply, Finset.sum_mul,
    Finset.mul_sum, nEnt]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun n _ => by ring

theorem unpackC_opApply (M : Fin 27 → Fin 27 → ℂ) (X : Fin 1053 → ℂ) (k : Fin 39) :
    unpackC (opApply M X) k = mv M (unpackC X k) := by
  funext c
  have hv : (⟨27 * k.val + c.val, by omega⟩ : Fin 1053) = variableIndex k c :=
    Fin.ext (by simp [variableIndex_val])
  simp only [unpackC, hv, opApply_vi, mv, sv]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [show variableIndex k n = (⟨27 * k.val + n.val, by omega⟩ : Fin 1053) from Fin.ext (variableIndex_val k n)]

theorem stateAct_state (g : (Fin 27 → ℂ) →ₗ[ℂ] (Fin 27 → ℂ)) (X : Fin 1053 → ℂ) (k : Fin 39) (c : Fin 27) :
    stateAct g X ⟨27 * k.val + c.val, by omega⟩ = g (unpackC X k) c := by
  change g (unpackC X ⟨(27 * k.val + c.val) / 27, by omega⟩) ⟨(27 * k.val + c.val) % 27, by omega⟩ = _
  have e1 : (⟨(27 * k.val + c.val) / 27, by omega⟩ : Fin 39) = k :=
    Fin.ext (show (27 * k.val + c.val) / 27 = k.val by omega)
  have e2 : (⟨(27 * k.val + c.val) % 27, by omega⟩ : Fin 27) = c :=
    Fin.ext (show (27 * k.val + c.val) % 27 = c.val by omega)
  rw [e1, e2]

theorem unpackC_stateAct (g : (Fin 27 → ℂ) →ₗ[ℂ] (Fin 27 → ℂ)) (X : Fin 1053 → ℂ) (k : Fin 39) :
    unpackC (stateAct g X) k = g (unpackC X k) := by
  funext c; exact stateAct_state g X k c

theorem ambient_state (Y : Fin 1053 → ℂ) (v : Fin 1053) :
    Y v = unpackC Y ⟨v.val / 27, by omega⟩ ⟨v.val % 27, by omega⟩ := by
  simp only [unpackC]; congr 1; exact Fin.ext (show v.val = 27 * (v.val / 27) + v.val % 27 by omega)

theorem anchor_root (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 4) (a : Fin 3) (y : Fin 24 → ℂ) :
    eval (stateAct (invCartan (Ux ξ hξ) i) (opApply (nOp Q12.toComplex y) (Xc ξ))) (qH i a) =
      eval (opApply (nOp Q12.toComplex (fun j => mono (Ux ξ hξ) (rootExp i j) * y j)) Pbase) (qH i a) := by
  apply qH_anchor_congr
  intro v hv
  have hk : v.val / 27 < 39 := by omega
  have hst : invCartan (Ux ξ hξ) i (unpackC (Xc ξ) ⟨v.val / 27, hk⟩) = unpackC Pbase ⟨v.val / 27, hk⟩ := by
    funext c
    have hv' : AnchorCoordinate i ⟨27 * (v.val / 27) + c.val, by omega⟩ := by
      unfold AnchorCoordinate at hv ⊢; simp only; omega
    have h := transported_anchor ξ hξ i _ hv'
    rw [show (fun w => ((NativePolynomial.PartialAction.pack (literalCfg ξ) w : ℝ) : ℂ)) = Xc ξ from rfl,
      show (⟨27 * (v.val / 27) + c.val, by omega⟩ : Fin 1053) =
        ⟨27 * (⟨v.val / 27, hk⟩ : Fin 39).val + c.val, by omega⟩ from rfl, stateAct_state] at h
    rw [h]; rfl
  rw [ambient_state (stateAct _ _) v, ambient_state (opApply _ Pbase) v, unpackC_stateAct,
    unpackC_opApply, unpackC_opApply, mv_nOp, mv_nOp, map_sum]
  simp only [map_smul, invCartan_root, hst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => by ring

/-! ## 4. The base: `qH = homogeneousH`, complex-coefficient base reduction, `K(y)·P = V y` -/

theorem Pbase_rows (r : Fin 2184) : rowValue (1/2 : ℂ) (1/3 : ℂ) r Pbase = 0 :=
  F_at_literal exactPhases exactPhases_unit r

theorem Pbase_colJ (i : Fin 4) (a : Fin 3) (c : Fin 1053) :
    ∑ r, NativeH.weightC i a r * jacobianEntry (1/2 : ℂ) (1/3 : ℂ) r Pbase c = 0 := by
  rw [← Pbase_equilibrium i a c]
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  exact (equationLinearMatrix_translate_fRow _ _ _ r c).symm

theorem qH_eq_hom (i : Fin 4) (a : Fin 3) (x : Fin 1053 → ℂ) :
    eval x (qH i a) = NativeH.Reproduction.homogeneousH i a x := by
  rw [qH, ← contractedF_add_eq_quadratic Pbase _ Pbase_solution (Pbase_equilibrium i a)]
  unfold contractedF NativeH.Reproduction.homogeneousH
  simp only [row, eval_fRow, NativeH.Reproduction.rowValue_add, Pbase_rows, zero_add, mul_add,
    Finset.sum_add_distrib]
  have hl : ∑ r, NativeH.weightC i a r * ∑ c, jacobianEntry (1/2 : ℂ) (1/3 : ℂ) r Pbase c * x c = 0 := by
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro c _
    rw [← Finset.sum_mul, Pbase_colJ, zero_mul]
  rw [hl, zero_add]

/-- Rows of the original Jacobian annihilate a real kernel vector (accepted derivative bridge). -/
theorem rows_of_kernel (ξ : Fin 4 → ℂ) (W : Fin 1053 → ℝ)
    (h : fderiv ℝ Option2.NativeStress.originalF (Pxi ξ) W = 0) (r : Fin 2184) :
    ∑ c, jacobianEntry (1/2 : ℂ) (1/3 : ℂ) r (Xc ξ) c * ((W c : ℝ) : ℂ) = 0 := by
  rw [(NativeT.originalF_hasFDerivAt (Pxi ξ)).fderiv] at h
  have hr := congrFun h r
  simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    Pi.zero_apply] at hr
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_zero, jac_cast] at hc
  exact hc

theorem kWeight_split (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (j : Fin 24) (v : Fin 1053) :
    kWeight ξ j v = ((colRe ξ hξ j v : ℝ) : ℂ) + ((colIm ξ hξ j v : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · rw [kWeight_re, colRe_native]; simp
  · rw [kWeight_im, colIm_native]; simp

/-- Each complex column `K_j · literalCfg ξ` is tangent at `Pξ` (accepted `preVar_mem_original_kernel`). -/
theorem kWeight_tangent (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (j : Fin 24) (r : Fin 2184) :
    ∑ c, jacobianEntry (1/2 : ℂ) (1/3 : ℂ) r (Xc ξ) c * kWeight ξ j c = 0 := by
  have h1 := rows_of_kernel ξ (colRe ξ hξ j) (by rw [colRe]; exact preVar_mem_original_kernel hξ _ _) r
  have h2 := rows_of_kernel ξ (colIm ξ hξ j) (by rw [colIm]; exact preVar_mem_original_kernel hξ _ _) r
  simp only [kWeight_split ξ hξ, mul_add, Finset.sum_add_distrib, ← mul_assoc]
  rw [h1, ← Finset.sum_mul, h2, zero_mul, add_zero]

/-- `K(y)` with complex coefficients. -/
def Kop (y : Fin 24 → ℂ) : Fin 27 → Fin 27 → ℂ := fun k c => ∑ j, y j * Q12.toComplex (kMat j k c)

theorem opApply_Kop (ξ : Fin 4 → ℂ) (y : Fin 24 → ℂ) (v : Fin 1053) :
    opApply (Kop y) (Xc ξ) v = ∑ j, y j * kWeight ξ j v := by
  unfold kWeight opApply Kop
  simp only [Xc_vi, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc]; rfl

theorem nOp_sub (ξ : Fin 4 → ℂ) (y : Fin 24 → ℂ) :
    opApply (dirDer Q12.toComplex y) (Xc ξ) - opApply (Kop y) (Xc ξ) =
      opApply (nOp Q12.toComplex y) (Xc ξ) := by
  funext v
  simp only [Pi.sub_apply, opApply, dirDer, nOp, Kop, ← Finset.sum_sub_distrib, ← sub_mul]
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [aMat, kMat_eq_kZ, nZ, map_sub, map_mul, map_mul, map_sub]
  ring

/-- **Base reduction with complex coefficients** (gauge lemma at the base). -/
theorem base_reduce (i : Fin 4) (a : Fin 3) (y : Fin 24 → ℂ) :
    NativeH.Reproduction.homogeneousH i a (opApply (nOp Q12.toComplex y) Pbase) =
      NativeH.Reproduction.homogeneousH i a (opApply (Kop y) Pbase) := by
  have hD := dirDer_props Q12.toComplex y
  have hv : ∀ r, ∑ c, jacobianEntry (1/2 : ℂ) (1/3 : ℂ) r Pbase c * opApply (Kop y) Pbase c = 0 := by
    intro r
    change ∑ c, jacobianEntry (1/2 : ℂ) (1/3 : ℂ) r (Xc exactPhases) c *
      opApply (Kop y) (Xc exactPhases) c = 0
    simp only [opApply_Kop, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    have := kWeight_tangent exactPhases exactPhases_unit j r
    rw [show (∑ c, jacobianEntry (1/2 : ℂ) (1/3 : ℂ) r (Xc exactPhases) c * (y j * kWeight exactPhases j c)) =
      y j * ∑ c, jacobianEntry (1/2 : ℂ) (1/3 : ℂ) r (Xc exactPhases) c * kWeight exactPhases j c by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun c _ => by ring, this, mul_zero]
  have g := gauge (1/2 : ℂ) (1/3 : ℂ) (by norm_num) (dirDer Q12.toComplex y) hD.1 hD.2.1 hD.2.2.1 hD.2.2.2
    Pbase (opApply (Kop y) Pbase) (NativeH.weightC i a) Pbase_rows (Pbase_colJ i a) hv
  rw [show opApply (dirDer Q12.toComplex y) Pbase - opApply (Kop y) Pbase =
    opApply (nOp Q12.toComplex y) Pbase from nOp_sub exactPhases y] at g
  unfold NativeH.Reproduction.homogeneousH
  exact g

/-- At the base, `K(y)·P` is the accepted Book direction `V y` (complex coefficients). -/
theorem kop_base (y : Fin 24 → ℂ) : opApply (Kop y) Pbase = V y := by
  funext u
  change opApply (Kop y) (Xc exactPhases) u = _
  rw [opApply_Kop]
  change _ = ∑ j, y j * eigenColumn j u
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [kWeight_split exactPhases exactPhases_unit, colRe_exactPhases, colIm_exactPhases]
  simp only [eigenColumn]
  exact Complex.re_add_im _

/-! ## 5. Book values with complex coefficients and their weights -/

/-- The Book quadratic of a term list. -/
def bookSum (l : List (Fin 24 × Fin 24 × ℤ)) (y : Fin 24 → ℂ) : ℂ :=
  (l.map fun t => (t.2.2 : ℂ) * (y t.1 * y t.2.1)).sum

theorem hom_V_gen (i : Fin 4) (a : Fin 3)
    (hval : HTRouteKron.hValue i a = HTRouteKron.hBookValue i a)
    (hB : 2 * (HTRouteKron.BE (HTRouteKron.denLcm (NativeH.rawEntries i a)) (NativeH.hSpec i a)
      (NativeH.rawEntries i a) + HTRouteKron.BB (HTRouteKron.fullScale (HTRouteKron.denLcm
        (NativeH.rawEntries i a))) (HTRouteKron.hBook i a)) < 2 ^ HTRouteKron.width)
    (y : Fin 24 → ℂ) :
    NativeH.Reproduction.homogeneousH i a (V y) = bookSum (HTRouteKron.hBook i a) y := by
  have key := HTRouteKron.component_identity _ _ _ _ _ HTRouteKron.columns_sorted HTRouteKron.gol_sidon
    hval hB HTRouteKron.toC y
  rw [HTRouteKron.engR_toC _ _ _ (HTRouteKron.denLcm_dvd _), HTRouteKron.bookR_scale] at key
  rw [NativeH.Reproduction.homogeneousH_sparse]
  have hne := HTRouteKron.fullScale_ne_zero (NativeH.rawEntries i a)
  simp only [Int.cast_natCast] at key
  exact mul_left_cancel₀ hne key

/-- **Book H with complex coefficients** from the accepted fixed-seed Kronecker checks. -/
theorem hom_V_book (i : Fin 4) (a : Fin 3) (y : Fin 24 → ℂ) :
    NativeH.Reproduction.homogeneousH i a (V y) = bookSum (HTRouteKron.hBook i a) y := by
  fin_cases i <;> fin_cases a
  exacts [hom_V_gen 0 0 HTRouteKron.hCheck00 HTRouteKron.hBound00 y,
    hom_V_gen 0 1 HTRouteKron.hCheck01 HTRouteKron.hBound01 y,
    hom_V_gen 0 2 HTRouteKron.hCheck02 HTRouteKron.hBound02 y,
    hom_V_gen 1 0 HTRouteKron.hCheck10 HTRouteKron.hBound10 y,
    hom_V_gen 1 1 HTRouteKron.hCheck11 HTRouteKron.hBound11 y,
    hom_V_gen 1 2 HTRouteKron.hCheck12 HTRouteKron.hBound12 y,
    hom_V_gen 2 0 HTRouteKron.hCheck20 HTRouteKron.hBound20 y,
    hom_V_gen 2 1 HTRouteKron.hCheck21 HTRouteKron.hBound21 y,
    hom_V_gen 2 2 HTRouteKron.hCheck22 HTRouteKron.hBound22 y,
    hom_V_gen 3 0 HTRouteKron.hCheck30 HTRouteKron.hBound30 y,
    hom_V_gen 3 1 HTRouteKron.hCheck31 HTRouteKron.hBound31 y,
    hom_V_gen 3 2 HTRouteKron.hCheck32 HTRouteKron.hBound32 y]

/-- Weight check: every Book term `(p, q)` of component `(i, a)` has `rootExp p + rootExp q = cExp i a`. -/
def bookW (i : Fin 4) (a : Fin 3) : Bool :=
  (HTRouteKron.hBook i a).all fun t => decide (Ex.add (rootExp i t.1) (rootExp i t.2.1) = cExp i a)

theorem bookW_all (i : Fin 4) (a : Fin 3) : bookW i a = true := by
  fin_cases i <;> fin_cases a <;> decide +kernel

theorem bookSum_weight (U : Fin 4 → ℂˣ) (i : Fin 4) (a : Fin 3) (l : List (Fin 24 × Fin 24 × ℤ))
    (hl : (l.all fun t => decide (Ex.add (rootExp i t.1) (rootExp i t.2.1) = cExp i a)) = true)
    (y : Fin 24 → ℂ) :
    bookSum l (fun j => mono U (rootExp i j) * y j) = mono U (cExp i a) * bookSum l y := by
  induction l with
  | nil => simp [bookSum]
  | cons t l ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
    simp only [bookSum, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih hl.2, mul_add]
    congr 1
    rw [← hl.1, ← mono_mul]
    ring

/-! ## 6. The value at every unit phase -/

/-- **H reproduction at every unit phase**: every quartet, resonant phases included. -/
theorem H_reproduction_phase (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (z : BookHT.Blocks) :
    residualHxi ξ hξ (Option2.NativeStress.originalF (Pxi ξ + Vxi ξ hξ z)) = BookHT.H z := by
  funext i
  apply PiLp.ext
  intro a
  rw [residualHxi, residualOf_apply]
  simp only [ellH, mul_assoc]
  rw [← Finset.mul_sum, value_reduce ξ hξ (ellRaw ξ hξ i a) (ellRaw_col ξ hξ i a) z, quad_transport,
    anchor_root, qH_eq_hom, base_reduce, kop_base, hom_V_book,
    bookSum_weight (Ux ξ hξ) i a _ (bookW_all i a), ← mul_assoc, mul_comm (mono _ (Ex.neg _)),
    mono_mul_neg, one_mul]
  exact HTRouteKron.hBook_sum i a z

end Option2.NativeStress.HTPhaseComplete

end

#print axioms Option2.NativeStress.HTPhaseComplete.ellRaw_col
#print axioms Option2.NativeStress.HTPhaseComplete.quad_transport
#print axioms Option2.NativeStress.HTPhaseComplete.invCartan_root
#print axioms Option2.NativeStress.HTPhaseComplete.anchor_root
#print axioms Option2.NativeStress.HTPhaseComplete.qH_eq_hom
#print axioms Option2.NativeStress.HTPhaseComplete.base_reduce
#print axioms Option2.NativeStress.HTPhaseComplete.kop_base
#print axioms Option2.NativeStress.HTPhaseComplete.hom_V_book
#print axioms Option2.NativeStress.HTPhaseComplete.bookW_all
#print axioms Option2.NativeStress.HTPhaseComplete.H_reproduction_phase
