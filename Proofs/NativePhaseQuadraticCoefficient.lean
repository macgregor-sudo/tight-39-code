module

public import NativePhaseQuadraticBinding
public import OriginalResidualSmoothnessV2
public import StressHessianPullback

@[expose] public section

/-! Actual degree-two polynomial coefficient versus the real ambient Hessian.
No stress annihilation, solution, phase, support or reproduction hypothesis is used.
The unrestricted affine-line expansion retains its constant and linear terms. -/

noncomputable section
namespace Option2.NativeStress.PhaseQuadraticCoefficientA6
open MvPolynomial PolynomialJets
open AnalyticDerivative AnchorSupport CKM.NativeFirstOrder
open scoped BigOperators Topology

private theorem quadratic_decomposition {σ : Type*} (p : MvPolynomial σ ℂ)
    (hp : p.totalDegree ≤ 2) :
    p = C (p.coeff 0) + homogeneousComponent 1 p + homogeneousComponent 2 p := by
  classical
  ext d
  change p.coeff d = (C (p.coeff 0)).coeff d +
    (homogeneousComponent 1 p).coeff d + (homogeneousComponent 2 p).coeff d
  rw [coeff_homogeneousComponent, coeff_homogeneousComponent, coeff_C]
  by_cases h0 : Finsupp.degree d = 0
  · have hd : d = 0 := (Finsupp.degree_eq_zero_iff d).mp h0
    subst d
    simp
  · have hd : d ≠ 0 := fun h => h0 (by simp [h])
    by_cases h1 : Finsupp.degree d = 1
    · simp [Ne.symm hd, h1]
    · by_cases h2 : Finsupp.degree d = 2
      · simp [Ne.symm hd, h2]
      · have hhigh : p.totalDegree < Finsupp.degree d := by omega
        have hz : p.coeff d = 0 := coeff_eq_zero_of_totalDegree_lt hhigh
        simp [Ne.symm hd, h1, h2, hz]

private theorem homogeneous_eval_smul {σ : Type*} (p : MvPolynomial σ ℂ)
    (d : ℕ) (hp : p.IsHomogeneous d) (v : σ → ℂ) (t : ℂ) :
    eval (t • v) p = t^d * eval v p := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hdeg : (∑ j ∈ e.support, e j) = d := (hp.degree_eq_sum_deg_support he).symm
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring

private theorem quadratic_eval_line {σ : Type*} (p : MvPolynomial σ ℂ)
    (hp : p.totalDegree ≤ 2) (v : σ → ℂ) (t : ℂ) :
    eval (t • v) p = p.coeff 0 + t * eval v (homogeneousComponent 1 p) +
      t^2 * eval v (homogeneousComponent 2 p) := by
  conv_lhs => rw [quadratic_decomposition p hp]
  simp only [map_add, eval_C,
    homogeneous_eval_smul _ 1 (homogeneousComponent_isHomogeneous 1 p),
    homogeneous_eval_smul _ 2 (homogeneousComponent_isHomogeneous 2 p), pow_one]

private theorem eval_translate_point (P v : Fin 1053 → ℂ) (p : Poly) :
    eval v (translate P p) = eval (P + v) p := by
  rw [translate, ← MvPolynomial.eval_assoc]
  have he : (eval v ∘ (fun j => X j + C (P j))) = P + v := by
    funext j
    simp only [Function.comp_apply, map_add, eval_X, eval_C, Pi.add_apply]
    exact add_comm _ _
  rw [he]

private theorem original_row_complex (P : RealConfiguration) (r : Fin 2184) :
    eval (complexPack P) (row r) = (originalF P r : ℂ) := by
  have hr : map Complex.ofRealHom
      (NativePolynomial.ConfigurationResiduals.fRow (1/2 : ℝ) (1/3 : ℝ) r) = row r := by
    simpa [row] using FourSheets.PointBridge.Rows.map_fRow
      Complex.ofRealHom (1/2 : ℝ) (1/3 : ℝ) r
  rw [← hr, eval_map]
  exact (eval₂_comp Complex.ofRealHom (NativePolynomial.PartialAction.pack P)
    (NativePolynomial.ConfigurationResiduals.fRow (1/2 : ℝ) (1/3 : ℝ) r)).symm

/-- The complete native affine-line expansion; its lower coefficients are retained. -/
theorem actual_stress_line_expansion (P v : RealConfiguration) (w : Weights) :
    ∃ a b : ℂ, ∀ t : ℝ,
      stressCovector w (originalF (P + t • v)) = a + (t : ℂ) * b +
        (t : ℂ)^2 * eval (complexPack v) (contractedQuadratic (complexPack P) w) := by
  classical
  let p := contractedPolynomial (complexPack P) w
  have hp : p.totalDegree ≤ 2 := by
    apply totalDegree_finsetSum_le
    intro r _
    exact (totalDegree_smul_le _ _).trans
      (NativePolynomial.ConfigurationResiduals.translated_fRow_totalDegree_le_two
        (1/2 : ℂ) (1/3 : ℂ) (complexPack P) r)
  have hq : homogeneousComponent 2 p = contractedQuadratic (complexPack P) w := by
    simp only [p, contractedPolynomial, contractedQuadratic, equationAnnihilatorQuadric,
      map_sum, map_smul]
  refine ⟨p.coeff 0, eval (complexPack v) (homogeneousComponent 1 p), ?_⟩
  intro t
  have hpack : complexPack (P + t • v) = complexPack P + (t : ℂ) • complexPack v := by
    funext j
    simp only [complexPack, NativePolynomial.PartialAction.pack, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul]
  have hline : stressCovector w (originalF (P + t • v)) = eval ((t : ℂ) • complexPack v) p := by
    simp only [stressCovector_apply, p, contractedPolynomial, map_sum, smul_eval,
      translatedRow, eval_translate_point, ← hpack, original_row_complex]
  rw [hline, quadratic_eval_line p hp, hq]

section Calculus
variable {E F Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

private theorem post_linear_hessian (f : E → F) (L : F →L[ℝ] Z)
    (hf : ContDiff ℝ 2 f) (P u v : E) :
    fderiv ℝ (fderiv ℝ (L ∘ f)) P u v = L (fderiv ℝ (fderiv ℝ f) P u v) := by
  have he : fderiv ℝ (L ∘ f) = fun x => L.comp (fderiv ℝ f x) := by
    funext x
    rw [fderiv_comp x L.differentiableAt (hf.differentiable (by norm_num) x), L.fderiv]
  rw [he]
  let T := ContinuousLinearMap.compL ℝ E F Z L
  change fderiv ℝ (T ∘ fderiv ℝ f) P u v = _
  rw [fderiv_comp P T.differentiableAt
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) P), T.fderiv]
  rfl

private theorem affine_line_hessian (f : E → F) (hf : ContDiff ℝ 2 f) (P v : E) :
    fderiv ℝ (fderiv ℝ (fun t : ℝ => f (P + t • v))) 0 1 1 =
      fderiv ℝ (fderiv ℝ f) P v v := by
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  let g : ℝ → E := fun t => P + L t
  have hd : fderiv ℝ g = fun _ => L := by
    funext t
    exact (fderiv_const_add P).trans L.fderiv
  have hg : ContDiff ℝ 2 g := contDiff_const.add L.contDiff
  have h := SupportedStress.HessianPullback.second_chain_rule_zero f g
    hf.contDiffAt hg.contDiffAt 1 1
  rw [hd, fderiv_fun_const] at h
  simpa only [g, L, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
    zero_smul, add_zero, one_smul, zero_apply, Pi.zero_apply, map_zero, zero_add,
    Function.comp_def] using h

end Calculus

private theorem quadratic_line_hessian (a b q : ℂ) :
    fderiv ℝ (fderiv ℝ (fun t : ℝ => a + (t : ℂ) * b + (t : ℂ)^2 * q)) 0 1 1 =
      2 * q := by
  let Lb : ℝ →L[ℝ] ℂ := (ContinuousLinearMap.id ℝ ℝ).smulRight b
  let Lq : ℝ →L[ℝ] ℂ := (ContinuousLinearMap.id ℝ ℝ).smulRight q
  have hd : fderiv ℝ (fun t : ℝ => a + (t : ℂ) * b + (t : ℂ)^2 * q) =
      fun t => Lb + t • (2 • Lq) := by
    funext t
    have hc : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
      have he : (fun s : ℝ => (s : ℂ)) = (Complex.ofRealCLM : ℝ → ℂ) := by
        funext s
        exact (Complex.ofRealCLM_apply s).symm
      rw [he]
      simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using
        (Complex.ofRealCLM.hasFDerivAt (x := t)).hasDerivAt
    have h : HasDerivAt (fun s : ℝ => a + (s : ℂ) * b + (s : ℂ)^2 * q)
        (1 * b + (2 : ℂ) * (t : ℂ)^(2-1) * 1 * q) t :=
      ((hc.mul_const b).const_add a).add ((hc.pow 2).mul_const q)
    rw [h.hasFDerivAt.fderiv]
    apply ContinuousLinearMap.ext
    intro s
    simp [Lb, Lq, ContinuousLinearMap.smulRight_apply, Complex.real_smul,
      ContinuousLinearMap.toSpanSingleton_apply]
    ring
  rw [hd, fderiv_const_add]
  change fderiv ℝ ((ContinuousLinearMap.id ℝ ℝ).smulRight (2 • Lq)) 0 1 1 = _
  rw [ContinuousLinearMap.fderiv]
  simp [Lq]

/-- Exact ambient Hessian normalization for every base and arbitrary complex weights. -/
theorem actual_quadratic_coefficient (P v : RealConfiguration) (w : Weights) :
    eval (complexPack v) (contractedQuadratic (complexPack P) w) =
      (1/2 : ℝ) • stressCovector w
        (fderiv ℝ (fderiv ℝ originalF) P v v) := by
  obtain ⟨a,b,he⟩ := actual_stress_line_expansion P v w
  have hf : ContDiff ℝ 2 (stressCovector w ∘ originalF) :=
    (stressCovector w).contDiff.comp (originalF_contDiff 2)
  have h := affine_line_hessian (stressCovector w ∘ originalF) hf P v
  have he' : (fun t : ℝ => (stressCovector w ∘ originalF) (P + t • v)) =
      (fun t : ℝ => a + (t : ℂ) * b + (t : ℂ)^2 *
        eval (complexPack v) (contractedQuadratic (complexPack P) w)) := funext he
  rw [he', quadratic_line_hessian,
    post_linear_hessian originalF (stressCovector w) (originalF_contDiff 2)] at h
  rw [← h, Complex.real_smul]
  norm_num
  ring

/-- The phase interface retains the original translated rows and native pack. -/
theorem native_quadratic_coefficient (ξ : Fin 4 → ℂ) (w : Fin 2184 → ℂ)
    (v : RealConfiguration) :
    eval (complexPack v) (equationAnnihilatorQuadric (PhaseHilbertA6.nativeRows ξ) w) =
      (1/2 : ℝ) • stressCovector w
        (fderiv ℝ (fderiv ℝ originalF) (literalCfg ξ) v v) :=
  actual_quadratic_coefficient (literalCfg ξ) v w

end Option2.NativeStress.PhaseQuadraticCoefficientA6
