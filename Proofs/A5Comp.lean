module

public import A5Tits
public import A5Misc
public import A5SU3
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-!
# Explicit analytic compensations: the literal phase family lies in every raw family (piece COMP)

For each anchor, A3's binding at `ξ = ξ₀ · e^{iθ}` writes `P(ξ)` as the transport of
`stdAnchored (u(ξ) std u(ξ)ᴴ) (c • L(ξ) E(d_H(ξ)) R(ξ))`. With `v = u(ξ) u(ξ₀)⁻¹` (diagonal unitary)
the native automorphism `anchorΨinv H ∘ titsTwoSided v v ∘ anchorΨ H` moves the quartet back to
`u(ξ₀) std u(ξ₀)ᴴ`, and `vᴴ L(ξ) E R(ξ) v = g L(ξ₀) E R(ξ₀) hᴴ` with
`g = λ⁻¹ vᴴ L(ξ) L(ξ₀)⁻¹`, `hᴴ = λ R(ξ₀)⁻¹ R(ξ) v`, `λ³ = det (vᴴ L(ξ) L(ξ₀)⁻¹)`. All these matrices are
diagonal (or monomial) unitaries whose entries are `e^{i ℓ(θ)}` with `ℓ` integer-linear in `θ`, so
`g = suExp (cartanCoord β(θ))` exactly, with `λ = e^{i (Σℓ)/3}`; the right factor `h` is absorbed by
the accepted right action `nativeRightMultiply hᴴ` (which fixes the quartet), and
`d_H(ξ) = torusPhase d_H(ξ₀) (e(θ))` with `e` linear. The compensating group element is analytic,
lies in `autC` and is `1` at `θ = 0`.
-/

noncomputable section

open CKM.NativeFirstOrder CKM.NativeGroupSlice CompactAlbert UnitaryErrorBases
open scoped Matrix Topology

namespace CKM.NativeFourFamily

/-! ## Phase diagonals and integer-linear angles -/

/-- The diagonal unitary `diag (e^{i f₀}, e^{i f₁}, e^{i f₂})`. -/
def compPhDiag (f : Fin 3 → ℝ) : TitsComplexMatrix :=
  Matrix.diagonal fun j => Complex.exp (((f j : ℝ) : ℂ) * Complex.I)

theorem compPhDiag_zero : compPhDiag 0 = 1 := by
  simp [compPhDiag]

theorem compPhDiag_mul (f g : Fin 3 → ℝ) : compPhDiag f * compPhDiag g = compPhDiag (f + g) := by
  simp only [compPhDiag, Matrix.diagonal_mul_diagonal, Pi.add_apply, Complex.ofReal_add, add_mul,
    Complex.exp_add]

theorem compPhDiag_conjTranspose (f : Fin 3 → ℝ) : (compPhDiag f)ᴴ = compPhDiag (-f) := by
  rw [compPhDiag, Matrix.diagonal_conjTranspose, compPhDiag]
  congr 1
  funext j
  rw [Pi.star_apply, Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, Pi.neg_apply, Complex.ofReal_neg]
  congr 1
  ring

theorem compPhDiag_unitary (f : Fin 3 → ℝ) : compPhDiag f * (compPhDiag f)ᴴ = 1 := by
  rw [compPhDiag_conjTranspose, compPhDiag_mul, add_neg_cancel, compPhDiag_zero]

theorem compPhDiag_det (f : Fin 3 → ℝ) :
    (compPhDiag f).det = Complex.exp (((f 0 + f 1 + f 2 : ℝ) : ℂ) * Complex.I) := by
  rw [compPhDiag, Matrix.det_diagonal, Fin.prod_univ_three]
  simp only [Complex.ofReal_add, add_mul, Complex.exp_add]

/-- Angles `j ↦ ∑ₐ N j a · θ a / 3` with integer coefficients. -/
def compLin {n : ℕ} (N : Fin n → Fin 4 → ℤ) (θ : Fin 4 → ℝ) : Fin n → ℝ :=
  fun j => ∑ a, (N j a : ℝ) * (θ a / 3)

/-- `compLin N` as a linear map. -/
def compLinL {n : ℕ} (N : Fin n → Fin 4 → ℤ) : (Fin 4 → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun := compLin N
  map_add' x y := by
    funext j
    simp only [compLin, Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  map_smul' c x := by
    funext j
    simp only [compLin, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring

theorem compLin_analyticAt {n : ℕ} (N : Fin n → Fin 4 → ℤ) (θ₀ : Fin 4 → ℝ) :
    AnalyticAt ℝ (compLin N) θ₀ :=
  (LinearMap.toContinuousLinearMap (compLinL N)).analyticAt θ₀

theorem compLin_zero {n : ℕ} (N : Fin n → Fin 4 → ℤ) : compLin N 0 = 0 := by
  funext j
  simp [compLin]

theorem compLin_neg {n : ℕ} (N : Fin n → Fin 4 → ℤ) (θ : Fin 4 → ℝ) :
    compLin (-N) θ = -compLin N θ := by
  funext j
  simp [compLin, Finset.sum_neg_distrib]

theorem compLin_sum3 (N : Fin 3 → Fin 4 → ℤ) (θ : Fin 4 → ℝ) :
    compLin N θ 0 + compLin N θ 1 + compLin N θ 2 =
      ∑ a, ((N 0 a + N 1 a + N 2 a : ℤ) : ℝ) * (θ a / 3) := by
  simp only [compLin, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by push_cast; ring

/-- Cube roots of the phase variations. -/
def compF (θ : Fin 4 → ℝ) (a : Fin 4) : ℂ := Complex.exp (((θ a / 3 : ℝ) : ℂ) * Complex.I)

theorem compF_ne_zero (θ : Fin 4 → ℝ) (a : Fin 4) : compF θ a ≠ 0 := Complex.exp_ne_zero _

theorem compF_cube (θ : Fin 4 → ℝ) (a : Fin 4) :
    Complex.exp (((θ a : ℝ) : ℂ) * Complex.I) = compF θ a ^ 3 := by
  rw [compF, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem commonPhase_compF (ξ₀ : Fin 4 → ℂ) (θ : Fin 4 → ℝ) (a : Fin 4) :
    commonPhase ξ₀ θ a = ξ₀ a * compF θ a ^ 3 := by
  rw [commonPhase, compF_cube]

theorem compLin_exp {n : ℕ} (N : Fin n → Fin 4 → ℤ) (θ : Fin 4 → ℝ) (j : Fin n) :
    Complex.exp (((compLin N θ j : ℝ) : ℂ) * Complex.I) = ∏ a, compF θ a ^ (N j a) := by
  simp only [compLin, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [compF, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem compPhDiag_compLin (N : Fin 3 → Fin 4 → ℤ) (θ : Fin 4 → ℝ) :
    compPhDiag (compLin N θ) = Matrix.diagonal fun j => ∏ a, compF θ a ^ (N j a) := by
  rw [compPhDiag]
  congr 1
  funext j
  exact compLin_exp N θ j

theorem torusAngles_compLin (N : Fin 2 → Fin 4 → ℤ) (θ : Fin 4 → ℝ) :
    torusAngles (compLin N θ) = compLin ![N 0, N 1, -N 0 - N 1] θ := by
  funext j
  fin_cases j
  · rfl
  · rfl
  · simp only [torusAngles, compLin]
    simp
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring


/-! ## The transport of the anchored model -/

/-- Identity casts between the two spellings `Mat` (`ZMod 3` indices) and `TitsComplexMatrix`. -/
def compT (M : Mat) : TitsComplexMatrix := M

/-- See `compT`. -/
def compM (M : TitsComplexMatrix) : Mat := M

theorem comp_stdAnchored {v w : TitsComplexMatrix}
    (q q' : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian}) (W W' : Family)
    (hq : ∀ k t, (q' k t).val = v * (q k t).val * vᴴ)
    (hW : ∀ l (c : ℂ), titsTwoSided v w (nativeComplementaryPoint (c • W l)) =
      nativeComplementaryPoint (c • W' l)) (i : Fin 39) :
    titsTwoSided v w (stdAnchored q W i) = stdAnchored q' W' i := by
  unfold stdAnchored
  split_ifs with h
  · rw [titsTwoSided_includeHermitianMatrix]
    congr 1
    exact Subtype.ext (hq _ _).symm
  · exact hW _ _

theorem comp_hidFamily {ξ₀ ξ : Fin 4 → ℂ} (H : Fin 4) {v w g : Mat} {κ κ' : ℂ}
    (hL : v * g * gaugeLeft ξ₀ H = κ • gaugeLeft ξ H)
    (hR : gaugeRight ξ₀ H * wᴴ = κ' • gaugeRight ξ H) (hκ : κ * κ' = 1) (d : PhaseTriple)
    (l : Label) :
    hidFamily ξ H 1 1 d l = v * hidFamily ξ₀ H g 1 d l * wᴴ := by
  simp only [hidFamily, Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul]
  congr 1
  calc gaugeLeft ξ H * monomialFamily d (gaugeLabel H l) * gaugeRight ξ H
      = (κ * κ') • (gaugeLeft ξ H * monomialFamily d (gaugeLabel H l) * gaugeRight ξ H) := by
        rw [hκ, one_smul]
    _ = (v * g * gaugeLeft ξ₀ H) * monomialFamily d (gaugeLabel H l) *
          (gaugeRight ξ₀ H * wᴴ) := by
        rw [hL, hR, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    _ = v * (g * gaugeLeft ξ₀ H * monomialFamily d (gaugeLabel H l) * gaugeRight ξ₀ H) * wᴴ := by
        simp only [Matrix.mul_assoc]

theorem comp_point {ξ₀ ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) {v w g : Mat} {κ κ' : ℂ}
    (hv : compT v * (compT v)ᴴ = 1) (hQ : compT v * quartetConj ξ₀ H = quartetConj ξ H)
    (hL : v * g * gaugeLeft ξ₀ H = κ • gaugeLeft ξ H)
    (hR : gaugeRight ξ₀ H * wᴴ = κ' • gaugeRight ξ H) (hκ : κ * κ' = 1) (i : Fin 39) :
    literalPoint ξ i = (anchorΨinv H ∘ₗ titsTwoSided (compT v) (compT w) ∘ₗ anchorΨ H)
      (prePoint ξ₀ H g 1 (anchorTriple ξ hξ H) i) := by
  rw [← prePoint_base hξ H]
  have hc : ∀ y, anchorΨ H (anchorΨinv H y) = y := fun y =>
    LinearMap.congr_fun (anchorΨ_comp_anchorΨinv H) y
  simp only [prePoint, LinearMap.comp_apply, hc]
  congr 1
  refine (comp_stdAnchored _ _ _ _ (fun k t => ?_) (fun l c => ?_) _).symm
  · rw [anchorQuartet_val, anchorQuartet_val, ← hQ, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  · rw [comp_hidFamily H hL hR hκ _ l]
    refine (titsTwoSided_complementaryPoint hv (compT w)
      (compT (c • hidFamily ξ₀ H g 1 (anchorTriple ξ hξ H) l))).trans ?_
    congr 1
    rw [show compT (c • hidFamily ξ₀ H g 1 (anchorTriple ξ hξ H) l) =
      c • compT (hidFamily ξ₀ H g 1 (anchorTriple ξ hξ H) l) from rfl, Matrix.mul_smul,
      Matrix.smul_mul]
    rfl

theorem comp_cfg {ξ₀ ξ : Fin 4 → ℂ} (hξ : IsUnitPhase ξ) (H : Fin 4) {v w g : Mat} {κ κ' : ℂ}
    (hv : compT v * (compT v)ᴴ = 1) (hQ : compT v * quartetConj ξ₀ H = quartetConj ξ H)
    (hL : v * g * gaugeLeft ξ₀ H = κ • gaugeLeft ξ H)
    (hR : gaugeRight ξ₀ H * wᴴ = κ' • gaugeRight ξ H) (hκ : κ * κ' = 1) :
    literalCfg ξ = actC (coordEnd (anchorΨinv H ∘ₗ titsTwoSided (compT v) (compT w) ∘ₗ anchorΨ H))
      (preCfg ξ₀ H g 1 (anchorTriple ξ hξ H)) := by
  funext i
  rw [actC_apply, coordEnd_apply]
  simp only [preCfg, NativePolynomial.fromUpperCoordinates_upperCoordinates]
  exact congrArg NativePolynomial.upperCoordinates (comp_point hξ H hv hQ hL hR hκ i)

/-! ## Membership in `G` -/

theorem comp_mem_autC (H : Fin 4) {v w : TitsComplexMatrix} (hv : v * vᴴ = 1) (hw : w * wᴴ = 1)
    (hdet : v.det = w.det) :
    coordEnd (anchorΨinv H ∘ₗ titsTwoSided v w ∘ₗ anchorΨ H) ∈ autC := by
  rw [mem_autC_iff_isNativeAut, AlgEquiv.symm_apply_apply]
  refine ⟨?_, (anchorΨinv_isNativeAut H).comp
    ((titsTwoSided_isNativeAut hv hw hdet).comp (anchorΨ_isNativeAut H))⟩
  have h1 : ∀ y, anchorΨ H (anchorΨinv H y) = y := fun y =>
    LinearMap.congr_fun (anchorΨ_comp_anchorΨinv H) y
  have h2 : ∀ y, anchorΨinv H (anchorΨ H y) = y := fun y =>
    LinearMap.congr_fun (anchorΨinv_comp_anchorΨ H) y
  have hb : Function.Bijective (anchorΨ H) :=
    Function.bijective_iff_has_inverse.mpr ⟨anchorΨinv H, h2, h1⟩
  have hb' : Function.Bijective (anchorΨinv H) :=
    Function.bijective_iff_has_inverse.mpr ⟨anchorΨ H, h1, h2⟩
  rw [LinearMap.coe_comp, LinearMap.coe_comp]
  exact hb'.comp ((titsTwoSided_bijective hv hw).comp hb)

/-! ## Analyticity of the compensating group element -/

theorem comp_analyticAt_phase {f : (Fin 4 → ℝ) → ℝ} {θ₀ : Fin 4 → ℝ} (hf : AnalyticAt ℝ f θ₀) :
    AnalyticAt ℝ (fun θ => Complex.exp (((f θ : ℝ) : ℂ) * Complex.I)) θ₀ := by
  have h0 : AnalyticAt ℝ (fun θ => ((f θ : ℝ) : ℂ)) θ₀ :=
    (Complex.ofRealCLM.analyticAt _).comp hf
  have hc : AnalyticAt ℝ (fun θ => ((f θ : ℝ) : ℂ) * Complex.I) θ₀ := h0.mul analyticAt_const
  have he : AnalyticAt ℝ Complex.exp ((fun θ => ((f θ : ℝ) : ℂ) * Complex.I) θ₀) :=
    analyticAt_cexp.restrictScalars
  exact AnalyticAt.comp (g := Complex.exp) he hc

theorem comp_phDiag_entry (f g : Fin 3 → ℝ) (M : TitsComplexMatrix) (i j : Fin 3) :
    (compPhDiag f * M * compPhDiag g) i j =
      Complex.exp (((f i : ℝ) : ℂ) * Complex.I) * M i j * Complex.exp (((g j : ℝ) : ℂ) * Complex.I) := by
  simp only [compPhDiag, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem comp_analyticAt_entries {f g : (Fin 4 → ℝ) → Fin 3 → ℝ} {θ₀ : Fin 4 → ℝ}
    (hf : AnalyticAt ℝ f θ₀) (hg : AnalyticAt ℝ g θ₀) (M : TitsComplexMatrix) :
    AnalyticAt ℝ (fun θ => (fun i j => (compPhDiag (f θ) * M * compPhDiag (g θ)) i j :
      Fin 3 → Fin 3 → ℂ)) θ₀ := by
  refine analyticAt_pi_iff.mpr fun i => analyticAt_pi_iff.mpr fun j => ?_
  simp only [comp_phDiag_entry]
  exact ((comp_analyticAt_phase (analyticAt_pi_iff.mp hf i)).mul analyticAt_const).mul
    (comp_analyticAt_phase (analyticAt_pi_iff.mp hg j))

theorem comp_analyticAt_functional {fv fw : (Fin 4 → ℝ) → Fin 3 → ℝ} {θ₀ : Fin 4 → ℝ}
    (hfv : AnalyticAt ℝ fv θ₀) (hfw : AnalyticAt ℝ fw θ₀) (ℓ : Glennie.Albert →ₗ[ℝ] ℝ)
    (x : Glennie.Albert) :
    AnalyticAt ℝ (fun θ => ℓ (titsTwoSided (compPhDiag (fv θ)) (compPhDiag (fw θ)) x)) θ₀ := by
  obtain ⟨linv, hlinv⟩ := LinearMap.exists_leftInverse_of_injective
    (nativeTitsMatrixPair : Glennie.Albert →ₗ[ℝ] TitsMatrixPair)
    (LinearMap.ker_eq_bot.mpr nativeTitsMatrixPair_injective)
  let Λ : ((Fin 3 → Fin 3 → ℂ) × (Fin 3 → Fin 3 → ℂ)) →ₗ[ℝ] ℝ :=
    (ℓ ∘ₗ linv) ∘ₗ LinearMap.prodMap (Matrix.ofLinearEquiv ℝ).toLinearMap
      (Matrix.ofLinearEquiv ℝ).toLinearMap
  have hfun : (fun θ => ℓ (titsTwoSided (compPhDiag (fv θ)) (compPhDiag (fw θ)) x)) =
      fun θ => LinearMap.toContinuousLinearMap Λ
        ((fun i j => (compPhDiag (fv θ) * (nativeTitsMatrixPair x).1 *
            compPhDiag (-(fv θ))) i j : Fin 3 → Fin 3 → ℂ),
         (fun i j => (compPhDiag (fv θ) * (nativeTitsMatrixPair x).2 *
            compPhDiag (-(fw θ))) i j : Fin 3 → Fin 3 → ℂ)) := by
    funext θ
    have h := LinearMap.congr_fun hlinv (titsTwoSided (compPhDiag (fv θ)) (compPhDiag (fw θ)) x)
    rw [LinearMap.comp_apply, LinearMap.id_apply, titsTwoSided_pair,
      compPhDiag_conjTranspose, compPhDiag_conjTranspose] at h
    rw [← h]
    rfl
  rw [hfun]
  exact (LinearMap.toContinuousLinearMap Λ).analyticAt _ |>.comp
    ((comp_analyticAt_entries hfv hfv.neg _).prod (comp_analyticAt_entries hfv hfw.neg _))

theorem comp_analyticAt_A (H : Fin 4) {fv fw : (Fin 4 → ℝ) → Fin 3 → ℝ} {θ₀ : Fin 4 → ℝ}
    (hfv : AnalyticAt ℝ fv θ₀) (hfw : AnalyticAt ℝ fw θ₀) :
    AnalyticAt ℝ (fun θ => coordEnd (anchorΨinv H ∘ₗ
      titsTwoSided (compPhDiag (fv θ)) (compPhDiag (fw θ)) ∘ₗ anchorΨ H)) θ₀ := by
  let P := ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := Coord) (Fin 27)
  have hA : (fun θ => coordEnd (anchorΨinv H ∘ₗ
      titsTwoSided (compPhDiag (fv θ)) (compPhDiag (fw θ)) ∘ₗ anchorΨ H)) =
      fun θ => (P.symm : (Fin 27 → Coord) →L[ℝ] CEnd) (fun i k =>
        (LinearMap.proj k ∘ₗ NativePolynomial.upperCoordinateEquiv.toLinearMap ∘ₗ anchorΨinv H)
          (titsTwoSided (compPhDiag (fv θ)) (compPhDiag (fw θ))
            (anchorΨ H (NativePolynomial.fromUpperCoordinates (Pi.single i 1))))) := by
    funext θ
    apply P.injective
    rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  rw [hA]
  refine (P.symm : (Fin 27 → Coord) →L[ℝ] CEnd).analyticAt _ |>.comp ?_
  refine analyticAt_pi_iff.mpr fun i => analyticAt_pi_iff.mpr fun k => ?_
  exact comp_analyticAt_functional hfv hfw _ _


/-! ## Assembling the compensation from per-anchor data -/

/-- The Cartan coordinates as a linear map. -/
def compCartanL : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 8 → ℝ) where
  toFun := cartanCoord
  map_add' x y := by
    funext m
    simp only [cartanCoord, Pi.add_apply, Pi.single_apply]
    split_ifs <;> ring
  map_smul' c x := by
    funext m
    simp only [cartanCoord, Pi.add_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Pi.single_apply]
    split_ifs <;> ring

theorem comp_of_data {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4)
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
      ∀ θ, literalCfg (commonPhase ξ₀ θ) = actC (A θ) (preMap ξ₀ hξ₀ H (k θ, 0, e θ)) := by
  have hβsum : ∀ θ, compLin Nβ θ 0 + compLin Nβ θ 1 + compLin Nβ θ 2 = 0 := fun θ => by
    rw [compLin_sum3]
    simp [hβ]
  refine ⟨fun θ => coordEnd (anchorΨinv H ∘ₗ
      titsTwoSided (compPhDiag (compLin Nv θ)) (compPhDiag (compLin Nw θ)) ∘ₗ anchorΨ H),
    fun θ => cartanCoord (compLin Nβ θ), compLin Ne,
    comp_analyticAt_A H (compLin_analyticAt Nv 0) (compLin_analyticAt Nw 0), ?_, fun θ => ?_,
    ?_, ?_, compLin_analyticAt Ne 0, compLin_zero Ne, fun θ => ?_⟩
  · simp only [compLin_zero, compPhDiag_zero, titsTwoSided_one, LinearMap.id_comp,
      anchorΨinv_comp_anchorΨ]
    exact map_one coordEnd
  · refine comp_mem_autC H (compPhDiag_unitary _) (compPhDiag_unitary _) ?_
    rw [compPhDiag_det, compPhDiag_det, compLin_sum3, compLin_sum3]
    simp only [hdet]
  · exact (LinearMap.toContinuousLinearMap compCartanL).analyticAt _ |>.comp
      (compLin_analyticAt Nβ 0)
  · simp [compLin_zero, cartanCoord]
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


/-! ## Entry formulas for the per-anchor checks -/

theorem compLin_add {n : ℕ} (N N' : Fin n → Fin 4 → ℤ) (θ : Fin 4 → ℝ) :
    compLin N θ + compLin N' θ = compLin (N + N') θ := by
  funext j
  simp only [compLin, Pi.add_apply, ← Finset.sum_add_distrib, Int.cast_add]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem comp_left_entryT (Nv Nβ : Fin 3 → Fin 4 → ℤ) (θ : Fin 4 → ℝ) (L : TitsComplexMatrix)
    (i j : Fin 3) :
    (compPhDiag (compLin Nv θ) * compPhDiag (compLin Nβ θ) * L) i j =
      (∏ a, compF θ a ^ (Nv i a + Nβ i a)) * L i j := by
  rw [compPhDiag_mul, compLin_add, compPhDiag_compLin, Matrix.diagonal_mul]
  rfl

theorem comp_left_entry (Nv Nβ : Fin 3 → Fin 4 → ℤ) (θ : Fin 4 → ℝ) (L : Mat) (i j : Index) :
    (compM (compPhDiag (compLin Nv θ)) * compM (compPhDiag (compLin Nβ θ)) * L) i j =
      (∏ a, compF θ a ^ (Nv i a + Nβ i a)) * L i j :=
  comp_left_entryT Nv Nβ θ (compT L) i j

theorem comp_right_entryT (N : Fin 3 → Fin 4 → ℤ) (θ : Fin 4 → ℝ) (R : TitsComplexMatrix)
    (i j : Fin 3) :
    (R * compPhDiag (compLin N θ)) i j = R i j * ∏ a, compF θ a ^ (N j a) := by
  rw [compPhDiag_compLin, Matrix.mul_diagonal]

theorem comp_right_entry (N : Fin 3 → Fin 4 → ℤ) (θ : Fin 4 → ℝ) (R : Mat) (i j : Index) :
    (R * compM (compPhDiag (compLin N θ))) i j = R i j * ∏ a, compF θ a ^ (N j a) :=
  comp_right_entryT N θ (compT R) i j

theorem comp_torus_exp (Ne : Fin 2 → Fin 4 → ℤ) (θ : Fin 4 → ℝ) (j : Index) :
    Complex.exp (((torusAngles (compLin Ne θ) j : ℝ) : ℂ) * Complex.I) =
      ∏ a, compF θ a ^ ((![Ne 0, Ne 1, -Ne 0 - Ne 1] : Fin 3 → Fin 4 → ℤ) j a) := by
  rw [torusAngles_compLin]
  exact compLin_exp _ θ j

/-! ## Anchor 3 -/

theorem comp_anchor3 {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) :
    ∃ (A : (Fin 4 → ℝ) → CEnd) (k : (Fin 4 → ℝ) → Fin 8 → ℝ) (e : (Fin 4 → ℝ) → Fin 2 → ℝ),
      AnalyticAt ℝ A 0 ∧ A 0 = 1 ∧ (∀ θ, A θ ∈ autC) ∧
      AnalyticAt ℝ k 0 ∧ k 0 = 0 ∧ AnalyticAt ℝ e 0 ∧ e 0 = 0 ∧
      ∀ θ, literalCfg (commonPhase ξ₀ θ) = actC (A θ) (preMap ξ₀ hξ₀ 3 (k θ, 0, e θ)) := by
  have h0 : ξ₀ 0 ≠ 0 := fun h => by simpa [h] using hξ₀ 0
  have h1 : ξ₀ 1 ≠ 0 := fun h => by simpa [h] using hξ₀ 1
  have h2 : ξ₀ 2 ≠ 0 := fun h => by simpa [h] using hξ₀ 2
  have h3 : ξ₀ 3 ≠ 0 := fun h => by simpa [h] using hξ₀ 3
  refine comp_of_data hξ₀ 3
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
      simp [gaugeRight, Fin.prod_univ_four, mul_comm]
  · field_simp
  · rw [comp_torus_exp]
    rcases Anchor0.indexCases j with rfl | rfl | rfl <;>
      simp [anchorPhases, Fin.prod_univ_four, commonPhase_compF] <;> field_simp


theorem compLin_zero_rows (θ : Fin 4 → ℝ) :
    compLin ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]] θ = 0 := by
  funext j
  fin_cases j <;> simp [compLin, Fin.sum_univ_four]

/-! ## Anchor 0 -/

theorem comp_anchor0 {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) :
    ∃ (A : (Fin 4 → ℝ) → CEnd) (k : (Fin 4 → ℝ) → Fin 8 → ℝ) (e : (Fin 4 → ℝ) → Fin 2 → ℝ),
      AnalyticAt ℝ A 0 ∧ A 0 = 1 ∧ (∀ θ, A θ ∈ autC) ∧
      AnalyticAt ℝ k 0 ∧ k 0 = 0 ∧ AnalyticAt ℝ e 0 ∧ e 0 = 0 ∧
      ∀ θ, literalCfg (commonPhase ξ₀ θ) = actC (A θ) (preMap ξ₀ hξ₀ 0 (k θ, 0, e θ)) := by
  have h0 : ξ₀ 0 ≠ 0 := fun h => by simpa [h] using hξ₀ 0
  have h1 : ξ₀ 1 ≠ 0 := fun h => by simpa [h] using hξ₀ 1
  have h2 : ξ₀ 2 ≠ 0 := fun h => by simpa [h] using hξ₀ 2
  have h3 : ξ₀ 3 ≠ 0 := fun h => by simpa [h] using hξ₀ 3
  refine comp_of_data hξ₀ 0 ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
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
      simp [gaugeLeft, Anchor0.gaugeL, Fin.prod_univ_four, commonPhase_compF,
        show (0 : Index) ≠ 2 by decide, show (1 : Index) ≠ 2 by decide,
        show (2 : Index) ≠ 0 by decide, show (2 : Index) ≠ 1 by decide] <;> field_simp
  · ext i j
    rw [comp_right_entry]
    rcases Anchor0.indexCases i with rfl | rfl | rfl <;>
      rcases Anchor0.indexCases j with rfl | rfl | rfl <;>
      simp [gaugeRight, Anchor0.gaugeR, Fin.prod_univ_four, commonPhase_compF,
        show (0 : Index) ≠ 2 by decide, show (1 : Index) ≠ 2 by decide,
        show (2 : Index) ≠ 0 by decide, show (2 : Index) ≠ 1 by decide] <;> field_simp
  · field_simp
  · rw [comp_torus_exp]
    rcases Anchor0.indexCases j with rfl | rfl | rfl <;>
      simp [anchorPhases, Fin.prod_univ_four, commonPhase_compF] <;> field_simp

/-! ## Anchor 1 -/

theorem comp_anchor1 {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) :
    ∃ (A : (Fin 4 → ℝ) → CEnd) (k : (Fin 4 → ℝ) → Fin 8 → ℝ) (e : (Fin 4 → ℝ) → Fin 2 → ℝ),
      AnalyticAt ℝ A 0 ∧ A 0 = 1 ∧ (∀ θ, A θ ∈ autC) ∧
      AnalyticAt ℝ k 0 ∧ k 0 = 0 ∧ AnalyticAt ℝ e 0 ∧ e 0 = 0 ∧
      ∀ θ, literalCfg (commonPhase ξ₀ θ) = actC (A θ) (preMap ξ₀ hξ₀ 1 (k θ, 0, e θ)) := by
  have h0 : ξ₀ 0 ≠ 0 := fun h => by simpa [h] using hξ₀ 0
  have h1 : ξ₀ 1 ≠ 0 := fun h => by simpa [h] using hξ₀ 1
  have h2 : ξ₀ 2 ≠ 0 := fun h => by simpa [h] using hξ₀ 2
  have h3 : ξ₀ 3 ≠ 0 := fun h => by simpa [h] using hξ₀ 3
  refine comp_of_data hξ₀ 1 ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]
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

/-! ## Anchor 2 -/

theorem comp_anchor2 {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) :
    ∃ (A : (Fin 4 → ℝ) → CEnd) (k : (Fin 4 → ℝ) → Fin 8 → ℝ) (e : (Fin 4 → ℝ) → Fin 2 → ℝ),
      AnalyticAt ℝ A 0 ∧ A 0 = 1 ∧ (∀ θ, A θ ∈ autC) ∧
      AnalyticAt ℝ k 0 ∧ k 0 = 0 ∧ AnalyticAt ℝ e 0 ∧ e 0 = 0 ∧
      ∀ θ, literalCfg (commonPhase ξ₀ θ) = actC (A θ) (preMap ξ₀ hξ₀ 2 (k θ, 0, e θ)) := by
  have h0 : ξ₀ 0 ≠ 0 := fun h => by simpa [h] using hξ₀ 0
  have h1 : ξ₀ 1 ≠ 0 := fun h => by simpa [h] using hξ₀ 1
  have h2 : ξ₀ 2 ≠ 0 := fun h => by simpa [h] using hξ₀ 2
  have h3 : ξ₀ 3 ≠ 0 := fun h => by simpa [h] using hξ₀ 3
  refine comp_of_data hξ₀ 2
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
      simp [gaugeLeft, Anchor2.gaugeL, Anchor2.gaugeLv, Fin.prod_univ_four, commonPhase_compF,
        show (0 : Index) ≠ 2 by decide, show (1 : Index) ≠ 2 by decide,
        show (2 : Index) ≠ 0 by decide, show (2 : Index) ≠ 1 by decide,
        show (1 : Index) + 1 = 2 by decide, show (1 : Index) + 2 = 0 by decide,
        show (2 : Index) + 2 = 1 by decide] <;>
      field_simp
  · ext i j
    rw [comp_right_entry]
    rcases Anchor0.indexCases i with rfl | rfl | rfl <;>
      rcases Anchor0.indexCases j with rfl | rfl | rfl <;>
      simp [gaugeRight, Anchor2.gaugeR, Anchor2.gaugeRv, Fin.prod_univ_four, commonPhase_compF,
        show (0 : Index) ≠ 2 by decide, show (1 : Index) ≠ 2 by decide,
        show (2 : Index) ≠ 0 by decide, show (2 : Index) ≠ 1 by decide] <;>
      field_simp
  · field_simp
  · rw [comp_torus_exp]
    rcases Anchor0.indexCases j with rfl | rfl | rfl <;>
      simp [anchorPhases, Fin.prod_univ_four, commonPhase_compF] <;> field_simp

/-- The compensation, anchor by anchor (`comp_anchor0` … `comp_anchor3`): with `t_a = θ_a / 3` and
`F_a = e^{i t_a}`, the quartet transport `v`, the hidden right factor `w`, the Cartan element `g`
(`β` in `t`-units) and the torus angles `e` (in `t`-units) are

* anchor 0: `v = 1`, `g = w⁻¹ = diag(F₂²F₃, F₂⁻¹F₃⁻², F₂⁻¹F₃)`, `e = (θ₀+θ₁−θ₂, −θ₀−θ₃)`;
* anchor 1: `v = 1`, `g = diag(F₀⁻²F₁⁻¹, F₀F₁², F₀F₁⁻¹)`, `e = (θ₀+θ₂+θ₃, θ₁−θ₂)`;
* anchor 2: `v = diag(1, F₀³, F₁⁻³)`, `g = diag(F₀F₁⁻¹F₂²F₃, F₀⁻²F₁⁻¹F₂⁻¹F₃⁻², F₀F₁²F₂⁻¹F₃)`,
  `e = (θ₂+θ₃, −θ₂)`;
* anchor 3: `v = diag(1, F₂⁻³, F₃³)`, `g = diag(F₂⁻¹F₃, F₂²F₃, F₂⁻¹F₃⁻²)`, `w = F₂⁻¹F₃ · 1`,
  `e = (−θ₀, −θ₁)`;

and `A θ = coordEnd (anchorΨinv H ∘ titsTwoSided v w ∘ anchorΨ H)`. -/
theorem exists_compensation {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    ∃ (A : (Fin 4 → ℝ) → CEnd) (k : (Fin 4 → ℝ) → Fin 8 → ℝ) (e : (Fin 4 → ℝ) → Fin 2 → ℝ),
      AnalyticAt ℝ A 0 ∧ A 0 = 1 ∧ (∀ θ, A θ ∈ autC) ∧
      AnalyticAt ℝ k 0 ∧ k 0 = 0 ∧ AnalyticAt ℝ e 0 ∧ e 0 = 0 ∧
      ∀ θ, literalCfg (commonPhase ξ₀ θ) = actC (A θ) (preMap ξ₀ hξ₀ H (k θ, 0, e θ)) := by
  fin_cases H
  · exact comp_anchor0 hξ₀
  · exact comp_anchor1 hξ₀
  · exact comp_anchor2 hξ₀
  · exact comp_anchor3 hξ₀

end CKM.NativeFourFamily

#print axioms CKM.NativeFourFamily.exists_compensation
#print axioms CKM.NativeFourFamily.comp_of_data
#print axioms CKM.NativeFourFamily.comp_analyticAt_A
#print axioms CKM.NativeFourFamily.comp_mem_autC
#print axioms CKM.NativeFourFamily.comp_cfg
