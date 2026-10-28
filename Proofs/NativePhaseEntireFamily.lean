module

public import NativePhaseJetBound
public import NativeEntireRealSlice
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

/-! Explicit entire extension of the actual exponential raw family at anchor 0.
The phase is fixed. New complex parameters are never conjugated in the formulas:
the second hidden matrix expression conjugates coefficients only.  -/

noncomputable section
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
namespace Option2.NativeStress.PhaseEntireFamilyA6
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeFourFamily
open CompactAlbert UnitaryErrorBases Matrix PhaseBookComplexificationA6
open NativePolynomial
open scoped BigOperators ComplexConjugate

abbrev ParamIndex := Fin 52 ⊕ (Fin 8 ⊕ Fin 2)
abbrev CCoord := Fin 27 → ℂ
abbrev CEndC := CCoord →L[ℂ] CCoord

theorem complexMap_real {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (f : (m → ℝ) →ₗ[ℝ] (n → ℝ)) (x : m → ℝ) :
    complexMap f (fun i => (x i : ℂ)) = fun j => (f x j : ℂ) := by
  ext j
  apply Complex.ext
  · exact congrFun (complexMap_re f _) j
  · simpa only [Complex.ofReal_im, show (fun _ : m => (0 : ℝ)) = 0 from rfl,
      map_zero, Pi.zero_apply] using congrFun (complexMap_im f (fun i => (x i : ℂ))) j

@[simp] theorem complexMap_re_apply {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (f : (m → ℝ) →ₗ[ℝ] (n → ℝ)) (z : m → ℂ) (j : n) :
    (complexMap f z j).re = f (fun i => (z i).re) j := congrFun (complexMap_re f z) j

@[simp] theorem complexMap_im_apply {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (f : (m → ℝ) →ₗ[ℝ] (n → ℝ)) (z : m → ℂ) (j : n) :
    (complexMap f z j).im = f (fun i => (z i).im) j := congrFun (complexMap_im f z) j

def endComplexLin : CEnd →ₗ[ℝ] CEndC where
  toFun A := (complexMap A.toLinearMap).toContinuousLinearMap
  map_add' A B := by
    ext z j
    apply Complex.ext <;> simp
  map_smul' a A := by
    ext z j
    apply Complex.ext <;> simp [Complex.real_smul]

def endComplex : CEnd →+* CEndC where
  toFun := endComplexLin
  map_zero' := endComplexLin.map_zero
  map_add' := endComplexLin.map_add
  map_one' := by
    ext z j
    apply Complex.ext <;> simp [endComplexLin]
  map_mul' A B := by
    ext z j
    apply Complex.ext <;> simp [endComplexLin, complexMap_re, complexMap_im]

theorem endComplex_exp (A : CEnd) :
    endComplex (NormedSpace.exp A) = NormedSpace.exp (endComplex A) := by
  apply NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) endComplex
    endComplexLin.continuous_of_finiteDimensional
  rw [NormedSpace.expSeries_radius_eq_top]
  exact edist_lt_top _ _

def derivCoordinates : (Fin 52 → ℝ) ≃ₗ[ℝ] derC :=
  by
    letI : Module.Free ℝ derC := Module.Free.of_divisionRing ℝ derC
    exact LinearEquiv.ofFinrankEq _ _ (by simp [finrank_derC])

def derivBasis (j : Fin 52) : derC := derivCoordinates (Pi.single j 1)

def realDer (x : ParamIndex → ℝ) : derC := ∑ j, x (Sum.inl j) • derivBasis j

def realParam (x : ParamIndex → ℝ) : RawParam62 :=
  (realDer x, (fun j => x (Sum.inr (Sum.inl j))), fun j => x (Sum.inr (Sum.inr j)))

def complexDer (z : ParamIndex → ℂ) : CEndC :=
  ∑ j, z (Sum.inl j) • endComplex (derivBasis j : CEnd)

def suMatC (bar : Bool) (z : ParamIndex → ℂ) : Mat :=
  ∑ j, z (Sum.inr (Sum.inl j)) •
    if bar then (gellMann j).map conj else gellMann j

def angleC (z : ParamIndex → ℂ) : Index → ℂ :=
  fun j => if j = 0 then z (Sum.inr (Sum.inr 0)) else
    if j = 1 then z (Sum.inr (Sum.inr 1)) else
      -z (Sum.inr (Sum.inr 0)) - z (Sum.inr (Sum.inr 1))

def phaseC (d : PhaseTriple) (bar : Bool) (z : ParamIndex → ℂ) (j : Index) : ℂ :=
  if bar then conj (d.val j) * Complex.exp (-Complex.I * angleC z j)
  else d.val j * Complex.exp (Complex.I * angleC z j)

def monomialC (d : PhaseTriple) (bar : Bool) (z : ParamIndex → ℂ) (l : Label) : Mat :=
  fun i j =>
    (if i = j + l.2 then (if l.2 = 2 then phaseC d bar z j else 1) else 0) *
    (if bar then conj ((UnitaryErrorBases.omega ^ j.val) ^ l.1.val)
     else (UnitaryErrorBases.omega ^ j.val) ^ l.1.val)

def hiddenC (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (bar : Bool)
    (z : ParamIndex → ℂ) (l : Label) : Mat :=
  (if bar then conj (gaugeScalar 0 l) else gaugeScalar 0 l) •
    (NormedSpace.exp (suMatC bar z) *
      (if bar then (gaugeLeft ξ 0).map conj else gaugeLeft ξ 0) *
      monomialC (anchorTriple ξ hξ 0) bar z (gaugeLabel 0 l) *
      (if bar then (gaugeRight ξ 0).map conj else gaugeRight ξ 0))

abbrev HiddenIndex := Label × Index × Index × Fin 2

def hiddenFromReal : (HiddenIndex → ℝ) →ₗ[ℝ] FamanEnt where
  toFun x l i j := (x (l,i,j,0) : ℂ) + Complex.I * (x (l,i,j,1) : ℂ)
  map_add' _ _ := by ext; simp; ring
  map_smul' _ _ := by ext; simp; ring

def packedPreLin : (HiddenIndex → ℝ) →ₗ[ℝ] (Fin 1053 → ℝ) :=
  (show Cfg →ₗ[ℝ] (Fin 1053 → ℝ) from
    { toFun := PartialAction.pack, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl }).comp
    ((faman_preLin 0).toLinearMap.comp hiddenFromReal)

def hiddenCoordinates (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ)
    (z : ParamIndex → ℂ) (j : HiddenIndex) : ℂ :=
  if j.2.2.2 = 0 then
    (hiddenC ξ hξ false z j.1 j.2.1 j.2.2.1 +
      hiddenC ξ hξ true z j.1 j.2.1 j.2.2.1) / 2
  else
    (hiddenC ξ hξ false z j.1 j.2.1 j.2.2.1 -
      hiddenC ξ hξ true z j.1 j.2.1 j.2.2.1) / (2 * Complex.I)

def preExtension (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (z : ParamIndex → ℂ) :
    Fin 1053 → ℂ :=
  (fun k => ((PartialAction.pack (faman_preBase ξ 0) k : ℝ) : ℂ)) +
    complexMap packedPreLin (hiddenCoordinates ξ hξ z)

theorem complexDer_real (x : ParamIndex → ℝ) :
    complexDer (fun j => (x j : ℂ)) = endComplex (realDer x : CEnd) := by
  change (∑ j, (x (Sum.inl j) : ℂ) • endComplexLin (derivBasis j : CEnd)) =
    endComplexLin (↑(∑ j, x (Sum.inl j) • derivBasis j))
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
    Complex.coe_smul]
  apply Finset.sum_congr rfl
  intro j _
  ext v k
  rfl

theorem suMatC_real (x : ParamIndex → ℝ) :
    suMatC false (fun j => (x j : ℂ)) = suMat (realParam x).2.1 := by
  simp only [suMatC, Bool.false_eq_true, ↓reduceIte, suMat, realParam]

theorem suMatC_bar_real (x : ParamIndex → ℝ) :
    suMatC true (fun j => (x j : ℂ)) = (suMat (realParam x).2.1).map conj := by
  change (∑ j, (x (Sum.inr (Sum.inl j)) : ℂ) • (gellMann j).map conj) =
    (∑ j, (x (Sum.inr (Sum.inl j)) : ℂ) • gellMann j).map conj
  ext i j
  simp only [Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum,
    map_mul, Complex.conj_ofReal]

section MatrixNorm
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exp_map_conj (A : Mat) :
    NormedSpace.exp (A.map conj) = (NormedSpace.exp A).map conj := by
  symm
  apply NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ)
    ((starRingEnd ℂ).mapMatrix : Mat →+* Mat)
  · exact (show Mat →ₗ[ℝ] Mat from
      { toFun := fun M => M.map conj, map_add' := by intros; ext; simp,
        map_smul' := by intros; ext; simp [Complex.real_smul] }).continuous_of_finiteDimensional
  · rw [NormedSpace.expSeries_radius_eq_top]
    exact edist_lt_top _ _

def matrixEntry (i j : Index) : Mat →L[ℂ] ℂ :=
  (show Mat →ₗ[ℂ] ℂ from
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl }).toContinuousLinearMap

theorem suExpC_entire (bar : Bool) :
    Differentiable ℂ (fun z : ParamIndex → ℂ => NormedSpace.exp (suMatC bar z)) := by
  have h : Differentiable ℂ (suMatC bar) := by unfold suMatC; fun_prop
  intro z
  exact (NormedSpace.exp_analytic (𝕂 := ℂ) _).differentiableAt.comp z (h z)

theorem hiddenC_entire (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (bar : Bool)
    (l : Label) (i j : Index) : Differentiable ℂ (fun z => hiddenC ξ hξ bar z l i j) := by
  have he := suExpC_entire bar
  have hm : Differentiable ℂ (fun z : ParamIndex → ℂ =>
      monomialC (anchorTriple ξ hξ 0) bar z (gaugeLabel 0 l)) := by
    have hentry (i j : Index) : Differentiable ℂ (fun z : ParamIndex → ℂ =>
        monomialC (anchorTriple ξ hξ 0) bar z (gaugeLabel 0 l) i j) := by
      unfold monomialC phaseC angleC
      split_ifs <;> fun_prop
    exact differentiable_pi.mpr fun i => differentiable_pi.mpr fun j => hentry i j
  change Differentiable ℂ ((matrixEntry i j) ∘ fun z =>
    (if bar then conj (gaugeScalar 0 l) else gaugeScalar 0 l) •
      (NormedSpace.exp (suMatC bar z) *
        (if bar then (gaugeLeft ξ 0).map conj else gaugeLeft ξ 0) *
        monomialC (anchorTriple ξ hξ 0) bar z (gaugeLabel 0 l) *
        (if bar then (gaugeRight ξ 0).map conj else gaugeRight ξ 0)))
  have ht := ((he.mul_const (if bar then (gaugeLeft ξ 0).map conj else gaugeLeft ξ 0)).mul hm).mul_const
    (if bar then (gaugeRight ξ 0).map conj else gaugeRight ξ 0)
  convert (matrixEntry i j).differentiable.comp
    (ht.const_smul (if bar then conj (gaugeScalar 0 l) else gaugeScalar 0 l)) using 1

end MatrixNorm

theorem phaseC_real (d : PhaseTriple) (x : ParamIndex → ℝ) (j : Index) :
    phaseC d false (fun k => (x k : ℂ)) j = (torusPhase d (realParam x).2.2).val j := by
  have ha : angleC (fun k => (x k : ℂ)) j = (torusAngles (realParam x).2.2 j : ℂ) := by
    fin_cases j <;> simp [angleC, torusAngles, realParam]
  simp only [phaseC, Bool.false_eq_true, ↓reduceIte, torusPhase, ha, mul_comm Complex.I]

theorem phaseC_bar_real (d : PhaseTriple) (x : ParamIndex → ℝ) (j : Index) :
    phaseC d true (fun k => (x k : ℂ)) j = conj ((torusPhase d (realParam x).2.2).val j) := by
  have ha : angleC (fun k => (x k : ℂ)) j = (torusAngles (realParam x).2.2 j : ℂ) := by
    fin_cases j <;> simp [angleC, torusAngles, realParam]
  simp only [phaseC, ↓reduceIte, torusPhase, ha, map_mul, ← Complex.exp_conj,
    map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_mul, mul_comm Complex.I]

theorem monomialC_real (d : PhaseTriple) (x : ParamIndex → ℝ) (l : Label) :
    monomialC d false (fun k => (x k : ℂ)) l = monomialFamily (torusPhase d (realParam x).2.2) l := by
  ext i j
  rw [Anchor0.monomialFamily_apply]
  simp [monomialC, ThreeCycleFourier.phaseEntry, phaseC_real]

theorem monomialC_bar_real (d : PhaseTriple) (x : ParamIndex → ℝ) (l : Label) :
    monomialC d true (fun k => (x k : ℂ)) l =
      (monomialFamily (torusPhase d (realParam x).2.2) l).map conj := by
  ext i j
  rw [Matrix.map_apply, Anchor0.monomialFamily_apply]
  by_cases hb : l.2 = 2
  · simp only [monomialC, ↓reduceIte, ThreeCycleFourier.phaseEntry, hb, ↓reduceIte]
    split_ifs <;> simp [phaseC_bar_real]
  · simp only [monomialC, ↓reduceIte, ThreeCycleFourier.phaseEntry, hb, ↓reduceIte]
    split_ifs <;> simp

theorem hiddenC_real (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (x : ParamIndex → ℝ) (l : Label) :
    hiddenC ξ hξ false (fun k => (x k : ℂ)) l =
      hidFamily ξ 0 (suExp (realParam x).2.1) 1
        (torusPhase (anchorTriple ξ hξ 0) (realParam x).2.2) l := by
  simp [hiddenC, suMatC_real, monomialC_real, hidFamily, suExp]

theorem hiddenC_bar_real (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (x : ParamIndex → ℝ) (l : Label) :
    hiddenC ξ hξ true (fun k => (x k : ℂ)) l =
      (hidFamily ξ 0 (suExp (realParam x).2.1) 1
        (torusPhase (anchorTriple ξ hξ 0) (realParam x).2.2) l).map conj := by
  simp only [hiddenC, ↓reduceIte, suMatC_bar_real, exp_map_conj, monomialC_bar_real,
    hidFamily, suExp, Matrix.conjTranspose_one, Matrix.mul_one]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
    Matrix.mul_apply, map_sum]
  have he := exp_map_conj (show Mat from suMat (realParam x).2.1)
  simp only [he, Matrix.map_apply]
  rfl

theorem hiddenCoordinates_real (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (x : ParamIndex → ℝ) :
    hiddenCoordinates ξ hξ (fun k => (x k : ℂ)) = fun j : HiddenIndex =>
      ((if j.2.2.2 = 0 then
        (faman_hidEnt ξ 0 (suExp (realParam x).2.1) 1
          (torusPhase (anchorTriple ξ hξ 0) (realParam x).2.2) j.1 j.2.1 j.2.2.1).re
      else (faman_hidEnt ξ 0 (suExp (realParam x).2.1) 1
          (torusPhase (anchorTriple ξ hξ 0) (realParam x).2.2) j.1 j.2.1 j.2.2.1).im : ℝ) : ℂ) := by
  funext j
  simp only [hiddenCoordinates, hiddenC_real, hiddenC_bar_real, Matrix.map_apply, faman_hidEnt]
  split_ifs
  · apply Complex.ext <;> simp [Complex.div_re, Complex.div_im, Complex.normSq] <;> ring
  · apply Complex.ext <;> simp [Complex.div_re, Complex.div_im, Complex.normSq] <;> ring

theorem preExtension_real (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (x : ParamIndex → ℝ) :
    preExtension ξ hξ (fun k => (x k : ℂ)) =
      fun k => ((PartialAction.pack (preMap ξ hξ 0
        ((realParam x).2.1, 0, (realParam x).2.2)) k : ℝ) : ℂ) := by
  rw [preExtension, hiddenCoordinates_real, complexMap_real]
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
    Differentiable ℂ (preExtension ξ hξ) := by
  have hh : Differentiable ℂ (hiddenCoordinates ξ hξ) := by
    apply differentiable_pi.mpr
    intro j
    unfold hiddenCoordinates
    split_ifs
    · simp only [div_eq_mul_inv]
      convert ((hiddenC_entire ξ hξ false j.1 j.2.1 j.2.2.1).add
        (hiddenC_entire ξ hξ true j.1 j.2.1 j.2.2.1)).mul_const ((2 : ℂ)⁻¹) using 1
    · simp only [div_eq_mul_inv]
      convert ((hiddenC_entire ξ hξ false j.1 j.2.1 j.2.2.1).sub
        (hiddenC_entire ξ hξ true j.1 j.2.1 j.2.2.1)).mul_const ((2 * Complex.I)⁻¹) using 1
  exact (differentiable_const _ : Differentiable ℂ
    (fun _ : ParamIndex → ℂ => fun k => ((PartialAction.pack (faman_preBase ξ 0) k : ℝ) : ℂ))).add
      ((complexMap packedPreLin).toContinuousLinearMap.differentiable.comp hh)

/-- The actual anchor-0 exponential family in all 1053 complex coordinates. -/
def rawExtension (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (z : ParamIndex → ℂ) :
    Fin 1053 → ℂ :=
  PartialAction.pack (fun i => NormedSpace.exp (complexDer z)
    (fun j => preExtension ξ hξ z (finProdFinEquiv (i,j))))

theorem rawExtension_entire (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Differentiable ℂ (rawExtension ξ hξ) := by
  have hd : Differentiable ℂ complexDer := by unfold complexDer; fun_prop
  have he : Differentiable ℂ (fun z => NormedSpace.exp (complexDer z)) :=
    fun z => (NormedSpace.exp_analytic (𝕂 := ℂ) _).differentiableAt.comp z (hd z)
  have hp := preExtension_entire ξ hξ
  apply differentiable_pi.mpr
  intro k
  unfold rawExtension PartialAction.pack
  have hu : Differentiable ℂ (fun z => fun j : Fin 27 =>
      preExtension ξ hξ z (finProdFinEquiv ((@Fin.divNat 39 27 k),j))) := by
    apply differentiable_pi.mpr
    intro j
    exact (ContinuousLinearMap.proj (finProdFinEquiv ((@Fin.divNat 39 27 k),j))).differentiable.comp hp
  exact (ContinuousLinearMap.proj (@Fin.modNat 39 27 k)).differentiable.comp (he.clm_apply hu)

theorem rawExtension_real (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (x : ParamIndex → ℝ) :
    rawExtension ξ hξ (fun k => (x k : ℂ)) =
      fun k => ((PartialAction.pack (rawMap62 ξ hξ 0 (realParam x)) k : ℝ) : ℂ) := by
  have hp (i : Fin 39) :
      (fun j => preExtension ξ hξ (fun k => (x k : ℂ)) (finProdFinEquiv (i,j))) =
      fun j => ((preMap ξ hξ 0 ((realParam x).2.1,0,(realParam x).2.2) i j : ℝ) : ℂ) := by
    rw [preExtension_real]
    funext j
    have hi := congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (i,j))
    have hj := congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (i,j))
    change (finProdFinEquiv (i,j)).divNat = i at hi
    change (finProdFinEquiv (i,j)).modNat = j at hj
    change ((preMap ξ hξ 0 ((realParam x).2.1,0,(realParam x).2.2)
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
    MvPolynomial.eval (rawExtension ξ hξ z)
      (NativePolynomial.ConfigurationResiduals.fRow (1/2 : ℂ) (1/3 : ℂ) r) = 0 := by
  apply EntireRealSliceA6.entire_zero_of_real_slice _
    (polynomial_entire _ (rawExtension_entire ξ hξ) _) _ z
  intro x
  rw [rawExtension_real]
  have h : AnalyticDerivative.originalF (rawMap62 ξ hξ 0 (realParam x)) = 0 :=
    originalF_rawMap hξ 0 _
  have hr := congrFun h r
  have he : MvPolynomial.eval
      (fun k => ((PartialAction.pack (rawMap62 ξ hξ 0 (realParam x)) k : ℝ) : ℂ))
      (ConfigurationResiduals.fRow (1/2 : ℂ) (1/3 : ℂ) r) =
      (originalF (PartialAction.pack (rawMap62 ξ hξ 0 (realParam x))) r : ℂ) := by
    rw [NativeH.Reproduction.originalF_complex, QuarticCertificate.RowBridge.eval_fRow]
  rw [he]
  exact_mod_cast hr

#print axioms Option2.NativeStress.PhaseEntireFamilyA6.rawExtension_real
#print axioms Option2.NativeStress.PhaseEntireFamilyA6.rawExtension_entire
#print axioms Option2.NativeStress.PhaseEntireFamilyA6.rawExtension_original_rows

end Option2.NativeStress.PhaseEntireFamilyA6
