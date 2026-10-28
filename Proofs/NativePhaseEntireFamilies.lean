module

public import NativePhaseEntireFamily

@[expose] public section

/-! The same explicit native entire extension, uniformly for the four fixed
anchor labels. This imports the passed real-coordinate, exponential and phase
support; it does not assert joint holomorphic phase dependence or branch rank. -/
noncomputable section
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
namespace Option2.NativeStress.PhaseEntireFamiliesA6
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CompactAlbert UnitaryErrorBases Matrix PhaseBookComplexificationA6 NativePolynomial
open PhaseEntireFamilyA6
open scoped BigOperators ComplexConjugate
variable (H : Fin 4)

def hiddenC (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (bar : Bool)
    (z : ParamIndex → ℂ) (l : Label) : Mat :=
  (if bar then conj (gaugeScalar H l) else gaugeScalar H l) •
    (NormedSpace.exp (suMatC bar z) *
      (if bar then (gaugeLeft ξ H).map conj else gaugeLeft ξ H) *
      monomialC (anchorTriple ξ hξ H) bar z (gaugeLabel H l) *
      (if bar then (gaugeRight ξ H).map conj else gaugeRight ξ H))

def packedPreLin : (HiddenIndex → ℝ) →ₗ[ℝ] (Fin 1053 → ℝ) :=
  (show Cfg →ₗ[ℝ] (Fin 1053 → ℝ) from
    { toFun := PartialAction.pack, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl }).comp
    ((faman_preLin H).toLinearMap.comp hiddenFromReal)

def hiddenCoordinates (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (z : ParamIndex → ℂ) (j : HiddenIndex) : ℂ :=
  if j.2.2.2 = 0 then
    (hiddenC H ξ hξ false z j.1 j.2.1 j.2.2.1 +
      hiddenC H ξ hξ true z j.1 j.2.1 j.2.2.1) / 2
  else
    (hiddenC H ξ hξ false z j.1 j.2.1 j.2.2.1 -
      hiddenC H ξ hξ true z j.1 j.2.1 j.2.2.1) / (2 * Complex.I)

def preExtension (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (z : ParamIndex → ℂ) :
    Fin 1053 → ℂ :=
  (fun k => ((PartialAction.pack (faman_preBase ξ H) k : ℝ) : ℂ)) +
    complexMap (packedPreLin H) (hiddenCoordinates H ξ hξ z)

section MatrixNorm
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem hiddenC_entire (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (bar : Bool)
    (l : Label) (i j : Index) : Differentiable ℂ (fun z => hiddenC H ξ hξ bar z l i j) := by
  have he := suExpC_entire bar
  have hm : Differentiable ℂ (fun z : ParamIndex → ℂ =>
      monomialC (anchorTriple ξ hξ H) bar z (gaugeLabel H l)) := by
    have hentry (i j : Index) : Differentiable ℂ (fun z : ParamIndex → ℂ =>
        monomialC (anchorTriple ξ hξ H) bar z (gaugeLabel H l) i j) := by
      unfold monomialC phaseC angleC
      split_ifs <;> fun_prop
    exact differentiable_pi.mpr fun i => differentiable_pi.mpr fun j => hentry i j
  change Differentiable ℂ ((matrixEntry i j) ∘ fun z =>
    (if bar then conj (gaugeScalar H l) else gaugeScalar H l) •
      (NormedSpace.exp (suMatC bar z) *
        (if bar then (gaugeLeft ξ H).map conj else gaugeLeft ξ H) *
        monomialC (anchorTriple ξ hξ H) bar z (gaugeLabel H l) *
        (if bar then (gaugeRight ξ H).map conj else gaugeRight ξ H)))
  have ht := ((he.mul_const (if bar then (gaugeLeft ξ H).map conj else gaugeLeft ξ H)).mul hm).mul_const
    (if bar then (gaugeRight ξ H).map conj else gaugeRight ξ H)
  convert (matrixEntry i j).differentiable.comp
    (ht.const_smul (if bar then conj (gaugeScalar H l) else gaugeScalar H l)) using 1

end MatrixNorm

theorem hiddenC_real (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (x : ParamIndex → ℝ) (l : Label) :
    hiddenC H ξ hξ false (fun k => (x k : ℂ)) l =
      hidFamily ξ H (suExp (realParam x).2.1) 1
        (torusPhase (anchorTriple ξ hξ H) (realParam x).2.2) l := by
  simp [hiddenC, suMatC_real, monomialC_real, hidFamily, suExp]

theorem hiddenC_bar_real (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (x : ParamIndex → ℝ) (l : Label) :
    hiddenC H ξ hξ true (fun k => (x k : ℂ)) l =
      (hidFamily ξ H (suExp (realParam x).2.1) 1
        (torusPhase (anchorTriple ξ hξ H) (realParam x).2.2) l).map conj := by
  simp only [hiddenC, ↓reduceIte, suMatC_bar_real, exp_map_conj, monomialC_bar_real,
    hidFamily, suExp, Matrix.conjTranspose_one, Matrix.mul_one]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
    Matrix.mul_apply, map_sum]
  have he := exp_map_conj (show Mat from suMat (realParam x).2.1)
  simp only [he, Matrix.map_apply]
  rfl

theorem hiddenCoordinates_real (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (x : ParamIndex → ℝ) :
    hiddenCoordinates H ξ hξ (fun k => (x k : ℂ)) = fun j : HiddenIndex =>
      ((if j.2.2.2 = 0 then
        (faman_hidEnt ξ H (suExp (realParam x).2.1) 1
          (torusPhase (anchorTriple ξ hξ H) (realParam x).2.2) j.1 j.2.1 j.2.2.1).re
      else (faman_hidEnt ξ H (suExp (realParam x).2.1) 1
          (torusPhase (anchorTriple ξ hξ H) (realParam x).2.2) j.1 j.2.1 j.2.2.1).im : ℝ) : ℂ) := by
  funext j
  simp only [hiddenCoordinates, hiddenC_real H, hiddenC_bar_real H, Matrix.map_apply, faman_hidEnt]
  split_ifs
  · apply Complex.ext <;> simp [Complex.div_re, Complex.div_im, Complex.normSq] <;> ring
  · apply Complex.ext <;> simp [Complex.div_re, Complex.div_im, Complex.normSq] <;> ring

theorem preExtension_real (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (x : ParamIndex → ℝ) :
    preExtension H ξ hξ (fun k => (x k : ℂ)) =
      fun k => ((PartialAction.pack (preMap ξ hξ H
        ((realParam x).2.1, 0, (realParam x).2.2)) k : ℝ) : ℂ) := by
  rw [preExtension, hiddenCoordinates_real H, complexMap_real]
  have hh (e : FamanEnt) : hiddenFromReal
      (fun j : HiddenIndex => if j.2.2.2 = 0 then (e j.1 j.2.1 j.2.2.1).re
        else (e j.1 j.2.1 j.2.2.1).im) = e := by
    ext l i j
    simp only [hiddenFromReal, LinearMap.coe_mk, AddHom.coe_mk, ↓reduceIte,
      show (1 : Fin 2) ≠ 0 by decide]
    rw [mul_comm Complex.I, Complex.re_add_im]
  simp only [packedPreLin, LinearMap.comp_apply, hh]
  funext k
  simp only [Pi.add_apply, ← Complex.ofReal_add, preMap, suExp_zero, faman_preCfg_eq]
  rfl

theorem preExtension_entire (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Differentiable ℂ (preExtension H ξ hξ) := by
  have hh : Differentiable ℂ (hiddenCoordinates H ξ hξ) := by
    apply differentiable_pi.mpr
    intro j
    unfold hiddenCoordinates
    split_ifs
    · simp only [div_eq_mul_inv]
      convert ((hiddenC_entire H ξ hξ false j.1 j.2.1 j.2.2.1).add
        (hiddenC_entire H ξ hξ true j.1 j.2.1 j.2.2.1)).mul_const ((2 : ℂ)⁻¹) using 1
    · simp only [div_eq_mul_inv]
      convert ((hiddenC_entire H ξ hξ false j.1 j.2.1 j.2.2.1).sub
        (hiddenC_entire H ξ hξ true j.1 j.2.1 j.2.2.1)).mul_const ((2 * Complex.I)⁻¹) using 1
  exact (differentiable_const _ : Differentiable ℂ
    (fun _ : ParamIndex → ℂ => fun k => ((PartialAction.pack (faman_preBase ξ H) k : ℝ) : ℂ))).add
      ((complexMap (packedPreLin H)).toContinuousLinearMap.differentiable.comp hh)

/-- The actual anchor-H exponential family in all 1053 complex coordinates. -/

def rawExtension (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (z : ParamIndex → ℂ) :
    Fin 1053 → ℂ :=
  PartialAction.pack (fun i => NormedSpace.exp (complexDer z)
    (fun j => preExtension H ξ hξ z (finProdFinEquiv (i,j))))

theorem rawExtension_entire (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Differentiable ℂ (rawExtension H ξ hξ) := by
  have hd : Differentiable ℂ complexDer := by unfold complexDer; fun_prop
  have he : Differentiable ℂ (fun z => NormedSpace.exp (complexDer z)) :=
    fun z => (NormedSpace.exp_analytic (𝕂 := ℂ) _).differentiableAt.comp z (hd z)
  have hp := preExtension_entire H ξ hξ
  apply differentiable_pi.mpr
  intro k
  unfold rawExtension PartialAction.pack
  have hu : Differentiable ℂ (fun z => fun j : Fin 27 =>
      preExtension H ξ hξ z (finProdFinEquiv ((@Fin.divNat 39 27 k),j))) := by
    apply differentiable_pi.mpr
    intro j
    exact (ContinuousLinearMap.proj (finProdFinEquiv ((@Fin.divNat 39 27 k),j))).differentiable.comp hp
  exact (ContinuousLinearMap.proj (@Fin.modNat 39 27 k)).differentiable.comp (he.clm_apply hu)

theorem rawExtension_real (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (x : ParamIndex → ℝ) :
    rawExtension H ξ hξ (fun k => (x k : ℂ)) =
      fun k => ((PartialAction.pack (rawMap62 ξ hξ H (realParam x)) k : ℝ) : ℂ) := by
  have hp (i : Fin 39) :
      (fun j => preExtension H ξ hξ (fun k => (x k : ℂ)) (finProdFinEquiv (i,j))) =
      fun j => ((preMap ξ hξ H ((realParam x).2.1,0,(realParam x).2.2) i j : ℝ) : ℂ) := by
    rw [preExtension_real H]
    funext j
    have hi := congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (i,j))
    have hj := congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (i,j))
    change (finProdFinEquiv (i,j)).divNat = i at hi
    change (finProdFinEquiv (i,j)).modNat = j at hj
    change ((preMap ξ hξ H ((realParam x).2.1,0,(realParam x).2.2)
      (finProdFinEquiv (i,j)).divNat (finProdFinEquiv (i,j)).modNat : ℝ) : ℂ) = _
    rw [hi, hj]
  let A : CEnd := groupChart (realDer x)
  have hA : NormedSpace.exp (complexDer (fun k => (x k : ℂ))) = endComplex A := by
    rw [complexDer_real, ← endComplex_exp]
    rfl
  have hAr (v : Fin 27 → ℝ) : endComplex A (fun j => (v j : ℂ)) =
      fun j => (A v j : ℂ) := complexMap_real A.toLinearMap v
  funext k
  simp only [rawExtension, PartialAction.pack, hA, hp, hAr]
  rfl

private theorem polynomial_entire {σ : Type*} [Fintype σ]
    (g : (ParamIndex → ℂ) → (σ → ℂ)) (hg : Differentiable ℂ g)
    (p : MvPolynomial σ ℂ) : Differentiable ℂ (fun z => MvPolynomial.eval (g z) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa only [MvPolynomial.eval_C] using (differentiable_const (c := a))
  | add p q hp hq =>
    simp only [map_add]
    convert hp.add hq using 1
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    convert hp.mul ((ContinuousLinearMap.proj i).differentiable.comp hg) using 1
    rfl

/-- Every original row vanishes globally on the explicit entire extension.
The proof uses its exact actual real-family restriction, never an assumed
complex automorphism or special-unitary property. -/

theorem rawExtension_original_rows (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (r : Fin 2184) (z : ParamIndex → ℂ) :
    MvPolynomial.eval (rawExtension H ξ hξ z)
      (NativePolynomial.ConfigurationResiduals.fRow (1/2 : ℂ) (1/3 : ℂ) r) = 0 := by
  apply EntireRealSliceA6.entire_zero_of_real_slice _
    (polynomial_entire _ (rawExtension_entire H ξ hξ) _) _ z
  intro x
  rw [rawExtension_real H]
  have h : AnalyticDerivative.originalF (rawMap62 ξ hξ H (realParam x)) = 0 :=
    originalF_rawMap hξ H _
  have hr := congrFun h r
  have he : MvPolynomial.eval
      (fun k => ((PartialAction.pack (rawMap62 ξ hξ H (realParam x)) k : ℝ) : ℂ))
      (ConfigurationResiduals.fRow (1/2 : ℂ) (1/3 : ℂ) r) =
      (originalF (PartialAction.pack (rawMap62 ξ hξ H (realParam x))) r : ℂ) := by
    rw [NativeH.Reproduction.originalF_complex, QuarticCertificate.RowBridge.eval_fRow]
  rw [he]
  exact_mod_cast hr

#print axioms Option2.NativeStress.PhaseEntireFamiliesA6.rawExtension_real
#print axioms Option2.NativeStress.PhaseEntireFamiliesA6.rawExtension_entire
#print axioms Option2.NativeStress.PhaseEntireFamiliesA6.rawExtension_original_rows
end Option2.NativeStress.PhaseEntireFamiliesA6
