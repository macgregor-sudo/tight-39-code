module

public import A5Gauge
public import A5Misc
public import Mathlib.Analysis.Quaternion
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section

/-!
# Analyticity and strict derivatives of the families at the base point (piece FAMAN)

All maps are compositions of the analytic `SU(3)` chart `suExp`, the torus chart, polynomial matrix
operations, the affine hidden-point map `U ↦ p(U)`, linear native maps and `upperCoordinates`, the
analytic group chart `groupChart` and the bilinear action `actC`. The derivative of `preMap` at `0`
is the explicit `preVar` (quartet labels do not move; hidden labels move by `hidVar`).
-/

noncomputable section

open CKM.NativeFirstOrder CKM.NativeGroupSlice CompactAlbert UnitaryErrorBases
open scoped Matrix Topology

namespace CKM.NativeFourFamily

/-! ## Layer 1: the raw family is affine in the entries of the hidden matrices -/

theorem faman_hiddenVec_pair (U : TitsComplexMatrix) :
    nativeTitsMatrixPair (hiddenVec U) = (0, (1 / 3 : ℂ) • U) :=
  Elim.mkPoint_pair _ _ _

theorem faman_hiddenVec_add (U V : TitsComplexMatrix) :
    hiddenVec (U + V) = hiddenVec U + hiddenVec V := by
  apply nativeTitsMatrixPair_injective
  rw [map_add, faman_hiddenVec_pair, faman_hiddenVec_pair, faman_hiddenVec_pair, Prod.mk_add_mk,
    add_zero, smul_add]

theorem faman_hiddenVec_smul (r : ℝ) (U : TitsComplexMatrix) :
    hiddenVec (r • U) = r • hiddenVec U := by
  apply nativeTitsMatrixPair_injective
  rw [map_smul, faman_hiddenVec_pair, faman_hiddenVec_pair, Prod.smul_mk, smul_zero, smul_comm]

theorem faman_ncp_eq (U : TitsComplexMatrix) :
    nativeComplementaryPoint U = nativeComplementaryPoint 0 + hiddenVec U := by
  apply nativeTitsMatrixPair_injective
  rw [map_add, nativeComplementaryPoint_pair, nativeComplementaryPoint_pair, faman_hiddenVec_pair,
    Prod.mk_add_mk, smul_zero, add_zero, zero_add]

/-! The same facts, elaborated on `Mat` (index `ZMod 3`), so that they rewrite inside
`stdAnchored`/`stdAnchoredVar`. -/

private theorem faman_hiddenVec_add' (U V : Mat) :
    hiddenVec (U + V) = hiddenVec U + hiddenVec V := faman_hiddenVec_add U V

private theorem faman_hiddenVec_smul' (r : ℝ) (U : Mat) :
    hiddenVec (r • U) = r • hiddenVec U := faman_hiddenVec_smul r U

private theorem faman_ncp_eq' (U : Mat) :
    nativeComplementaryPoint U = nativeComplementaryPoint 0 + hiddenVec U := faman_ncp_eq U

/-- `stdAnchoredVar` is real-linear in the family. -/
def faman_varLin : Family →ₗ[ℝ] (Fin 39 → Glennie.Albert) where
  toFun V := stdAnchoredVar V
  map_add' V W := by
    funext i
    simp only [Pi.add_apply]
    unfold stdAnchoredVar
    split_ifs with h
    · rw [add_zero]
    · rw [Pi.add_apply, smul_add, faman_hiddenVec_add']
  map_smul' r V := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply]
    unfold stdAnchoredVar
    split_ifs with h
    · rw [smul_zero]
    · rw [Pi.smul_apply, smul_comm _ r, faman_hiddenVec_smul']

theorem faman_stdAnchored_eq (q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian})
    (W : Family) (i : Fin 39) :
    stdAnchored q W i = stdAnchored q 0 i + stdAnchoredVar W i := by
  unfold stdAnchored stdAnchoredVar
  split_ifs with h
  · rw [add_zero]
  · conv_lhs => rw [faman_ncp_eq']
    simp only [Pi.zero_apply, smul_zero]
    rfl

/-- Entry space of hidden families (product norm). -/
abbrev FamanEnt := Label → Index → Index → ℂ

/-- Entries to families. -/
def faman_ofEnt : FamanEnt →ₗ[ℝ] Family where
  toFun e l := Matrix.of (e l)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The linear part of the raw family in the hidden entries. -/
def faman_preLin (H : Fin 4) : FamanEnt →L[ℝ] Cfg :=
  LinearMap.toContinuousLinearMap
    (((LinearMap.pi fun i : Fin 39 => NativePolynomial.upperCoordinateEquiv.toLinearMap ∘ₗ
      anchorΨinv H ∘ₗ LinearMap.proj ((anchorRelabel H).symm i)) ∘ₗ faman_varLin ∘ₗ
        faman_ofEnt : FamanEnt →ₗ[ℝ] Cfg))

theorem faman_preLin_apply (H : Fin 4) (e : FamanEnt) :
    faman_preLin H e = fun i => NativePolynomial.upperCoordinates
      (anchorΨinv H (stdAnchoredVar (fun l => Matrix.of (e l)) ((anchorRelabel H).symm i))) :=
  rfl

/-- The constant part of the raw family. -/
def faman_preBase (ξ₀ : Fin 4 → ℂ) (H : Fin 4) : Cfg := fun i =>
  NativePolynomial.upperCoordinates
    (anchorΨinv H (stdAnchored (anchorQuartet ξ₀ H) 0 ((anchorRelabel H).symm i)))

/-- Entries of the hidden family. -/
def faman_hidEnt (ξ₀ : Fin 4 → ℂ) (H : Fin 4) (g h : Mat) (d : PhaseTriple) : FamanEnt :=
  fun l i j => hidFamily ξ₀ H g h d l i j

theorem faman_preCfg_eq (ξ₀ : Fin 4 → ℂ) (H : Fin 4) (g h : Mat) (d : PhaseTriple) :
    preCfg ξ₀ H g h d = faman_preBase ξ₀ H + faman_preLin H (faman_hidEnt ξ₀ H g h d) := by
  funext i
  simp only [preCfg, prePoint, Pi.add_apply, faman_preBase, faman_preLin_apply]
  rw [faman_stdAnchored_eq, map_add, NativePolynomial.upperCoordinates_add]
  rfl

theorem faman_preVar_eq (ξ₀ : Fin 4 → ℂ) (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) (p : PreParam) :
    preVar ξ₀ hξ₀ H p = faman_preLin H (fun l i j => hidVar ξ₀ H (anchorTriple ξ₀ hξ₀ H)
      (suMat p.1) (suMat p.2.1) (torusVar (anchorTriple ξ₀ hξ₀ H) p.2.2) l i j) :=
  rfl

/-! ## Layer 2: entrywise analyticity of matrix-valued maps -/

section EntAna

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : Type*}

theorem faman_ana_fst {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {f : E → F × G} {x : E} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => (f y).1) x :=
  ((ContinuousLinearMap.fst ℝ F G).analyticAt _).comp hf

theorem faman_ana_snd {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {f : E → F × G} {x : E} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => (f y).2) x :=
  ((ContinuousLinearMap.snd ℝ F G).analyticAt _).comp hf

/-- Every entry is real-analytic at `x`. -/
def FamanEntAna (M : E → Matrix n n ℂ) (x : E) : Prop :=
  ∀ i j, AnalyticAt ℝ (fun y => M y i j) x

theorem faman_ana_const (C : Matrix n n ℂ) (x : E) : FamanEntAna (fun _ : E => C) x :=
  fun _ _ => analyticAt_const

theorem faman_ana_mul [Fintype n] {A B : E → Matrix n n ℂ} {x : E} (hA : FamanEntAna A x)
    (hB : FamanEntAna B x) : FamanEntAna (fun y => A y * B y) x := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Finset.analyticAt_fun_sum _ fun k _ => (hA i k).mul (hB k j)

theorem faman_ana_smul (c : ℂ) {A : E → Matrix n n ℂ} {x : E} (hA : FamanEntAna A x) :
    FamanEntAna (fun y => c • A y) x := by
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact analyticAt_const.mul (hA i j)

theorem faman_ana_star {f : E → ℂ} {x : E} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => star (f y)) x :=
  (Complex.conjCLE.toContinuousLinearMap.analyticAt _).comp hf

theorem faman_ana_ct {A : E → Matrix n n ℂ} {x : E} (hA : FamanEntAna A x) :
    FamanEntAna (fun y => (A y)ᴴ) x := by
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact faman_ana_star (hA j i)

theorem faman_ana_diag [DecidableEq n] {v : E → n → ℂ} {x : E} (hv : ∀ i, AnalyticAt ℝ (fun y => v y i) x) :
    FamanEntAna (fun y => Matrix.diagonal (v y)) x := by
  intro i j
  by_cases h : i = j
  · subst h
    simp only [Matrix.diagonal_apply_eq]
    exact hv i
  · simp only [Matrix.diagonal_apply_ne _ h]
    exact analyticAt_const

theorem faman_ana_suExp {k : E → Fin 8 → ℝ} {x : E} (hk : AnalyticAt ℝ k x) :
    FamanEntAna (n := Index) (fun y => suExp (k y)) x := by
  intro i j
  have h := analyticAt_pi_iff.mp (analyticAt_pi_iff.mp (analyticAt_suExp (k x)) i) j
  exact h.comp hk

theorem faman_ana_ofReal {f : E → ℝ} {x : E} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => ((f y : ℝ) : ℂ)) x :=
  (Complex.ofRealCLM.analyticAt _).comp hf

theorem faman_ana_cexp {f : E → ℂ} {x : E} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => Complex.exp (f y)) x := by
  have he : AnalyticAt ℝ Complex.exp (f x) := analyticAt_cexp.restrictScalars
  exact AnalyticAt.comp (g := Complex.exp) he hf

theorem faman_ana_torusAngles {e : E → Fin 2 → ℝ} {x : E} (he : AnalyticAt ℝ e x) (j : Index) :
    AnalyticAt ℝ (fun y => torusAngles (e y) j) x := by
  have h0 : AnalyticAt ℝ (fun y => e y 0) x := analyticAt_pi_iff.mp he 0
  have h1 : AnalyticAt ℝ (fun y => e y 1) x := analyticAt_pi_iff.mp he 1
  fin_cases j
  · exact h0
  · exact h1
  · exact h0.neg.sub h1

theorem faman_ana_phaseMatrix (d₀ : PhaseTriple) (b : Index) {e : E → Fin 2 → ℝ} {x : E}
    (he : AnalyticAt ℝ e x) :
    FamanEntAna (fun y => phaseMatrix (torusPhase d₀ (e y)) b) x := by
  unfold phaseMatrix
  apply faman_ana_diag
  intro j
  by_cases hb : b = 2
  · simp only [hb, ite_true, torusPhase]
    exact analyticAt_const.mul
      (faman_ana_cexp ((faman_ana_ofReal (faman_ana_torusAngles he j)).mul analyticAt_const))
  · simp only [hb, ite_false]
    exact analyticAt_const

theorem faman_ana_monomial (d₀ : PhaseTriple) (b : Label) {e : E → Fin 2 → ℝ} {x : E}
    (he : AnalyticAt ℝ e x) :
    FamanEntAna (fun y => monomialFamily (torusPhase d₀ (e y)) b) x := by
  unfold monomialFamily
  exact faman_ana_mul (faman_ana_mul (faman_ana_const _ x) (faman_ana_phaseMatrix d₀ b.2 he))
    (faman_ana_const _ x)

theorem faman_ana_hidFamily (ξ₀ : Fin 4 → ℂ) (H : Fin 4) (d₀ : PhaseTriple) (l : Label)
    {g h : E → Fin 8 → ℝ} {e : E → Fin 2 → ℝ} {x : E} (hg : AnalyticAt ℝ g x)
    (hh : AnalyticAt ℝ h x) (he : AnalyticAt ℝ e x) :
    FamanEntAna (fun y => hidFamily ξ₀ H (suExp (g y)) (suExp (h y)) (torusPhase d₀ (e y)) l) x := by
  unfold hidFamily
  exact faman_ana_smul _ (faman_ana_mul (faman_ana_mul (faman_ana_mul (faman_ana_mul
    (faman_ana_suExp hg) (faman_ana_const _ x)) (faman_ana_monomial d₀ _ he)) (faman_ana_const _ x))
    (faman_ana_ct (faman_ana_suExp hh)))

end EntAna

/-! ## Layer 3: entrywise derivatives along lines -/

section EntDer

variable {n : Type*}

/-- Every entry has the given derivative at `t`. -/
def FamanEntDer (M : ℝ → Matrix n n ℂ) (M' : Matrix n n ℂ) (t : ℝ) : Prop :=
  ∀ i j, HasDerivAt (fun s => M s i j) (M' i j) t

theorem faman_der_const (C : Matrix n n ℂ) (t : ℝ) : FamanEntDer (fun _ => C) 0 t :=
  fun _ _ => hasDerivAt_const _ _

theorem faman_der_mul [Fintype n] {A B : ℝ → Matrix n n ℂ} {A' B' : Matrix n n ℂ} {t : ℝ}
    (hA : FamanEntDer A A' t) (hB : FamanEntDer B B' t) :
    FamanEntDer (fun s => A s * B s) (A' * B t + A t * B') t := by
  intro i j
  simp only [Matrix.mul_apply, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _ => (hA i k).mul (hB k j)

theorem faman_der_mul_const [Fintype n] {A : ℝ → Matrix n n ℂ} {A' : Matrix n n ℂ} {t : ℝ}
    (hA : FamanEntDer A A' t) (C : Matrix n n ℂ) :
    FamanEntDer (fun s => A s * C) (A' * C) t := by
  have h := faman_der_mul hA (faman_der_const C t)
  simpa only [Matrix.mul_zero, add_zero] using h

theorem faman_der_const_mul [Fintype n] {A : ℝ → Matrix n n ℂ} {A' : Matrix n n ℂ} {t : ℝ}
    (C : Matrix n n ℂ) (hA : FamanEntDer A A' t) :
    FamanEntDer (fun s => C * A s) (C * A') t := by
  have h := faman_der_mul (faman_der_const C t) hA
  simpa only [Matrix.zero_mul, zero_add] using h

theorem faman_der_smul (c : ℂ) {A : ℝ → Matrix n n ℂ} {A' : Matrix n n ℂ} {t : ℝ}
    (hA : FamanEntDer A A' t) : FamanEntDer (fun s => c • A s) (c • A') t := by
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact (hA i j).const_mul c

theorem faman_der_ct {A : ℝ → Matrix n n ℂ} {A' : Matrix n n ℂ} {t : ℝ}
    (hA : FamanEntDer A A' t) : FamanEntDer (fun s => (A s)ᴴ) A'ᴴ t := by
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact (hA j i).star

theorem faman_der_suExp (X : Fin 8 → ℝ) :
    FamanEntDer (n := Index) (fun t => suExp (t • X)) (suMat X) 0 := by
  intro i j
  have hl : HasDerivAt (fun t : ℝ => t • X) X 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const X
  have h := hasStrictFDerivAt_suExp.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)
  have h2 := hasDerivAt_pi.mp (hasDerivAt_pi.mp h i) j
  have e : suMatCLM X i j = suMat X i j := suMatCLM_apply X i j
  rw [e] at h2
  exact h2

/-- Local copy of `torusPhase_zero` (so this file does not depend on its proof). -/
private theorem faman_torusPhase_zero (d₀ : PhaseTriple) : torusPhase d₀ 0 = d₀ := by
  apply Subtype.ext
  funext j
  have h : torusAngles 0 j = 0 := by
    fin_cases j <;> simp [torusAngles]
  simp [torusPhase, h]

/-- `suExp` and `suMat`, typed as `Mat`. -/
def faman_sE (k : Fin 8 → ℝ) : Mat := suExp k

def faman_sM (k : Fin 8 → ℝ) : Mat := suMat k

theorem faman_sE_zero : faman_sE 0 = 1 := suExp_zero

theorem faman_der_sE (X : Fin 8 → ℝ) :
    FamanEntDer (fun t => faman_sE (t • X)) (faman_sM X) 0 := faman_der_suExp X

theorem faman_der_angle (d₀ : PhaseTriple) (e : Fin 2 → ℝ) (j : Index) :
    HasDerivAt (fun t : ℝ => d₀.val j * Complex.exp ((torusAngles (t • e) j : ℂ) * Complex.I))
      (torusVar d₀ e j) 0 := by
  have hlin : ∀ t : ℝ, torusAngles (t • e) j = t * torusAngles e j := by
    intro t
    fin_cases j <;> (simp [torusAngles]; try ring)
  simp only [hlin]
  have h1 : HasDerivAt (fun t : ℝ => (((t * torusAngles e j : ℝ) : ℂ) * Complex.I))
      ((torusAngles e j : ℂ) * Complex.I) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const (torusAngles e j)).ofReal_comp.mul_const Complex.I
    simpa using this
  have h2 := (h1.cexp).const_mul (d₀.val j)
  simpa [torusVar] using h2

theorem faman_der_phaseMatrix (d₀ : PhaseTriple) (e : Fin 2 → ℝ) (b : Index) :
    FamanEntDer (fun t => phaseMatrix (torusPhase d₀ (t • e)) b)
      (if b = 2 then Matrix.diagonal (torusVar d₀ e) else 0) 0 := by
  intro i j
  unfold phaseMatrix
  by_cases hb : b = 2
  · simp only [hb, ite_true, torusPhase]
    by_cases h : i = j
    · subst h
      simp only [Matrix.diagonal_apply_eq]
      exact faman_der_angle d₀ e i
    · simp only [Matrix.diagonal_apply_ne _ h]
      exact hasDerivAt_const _ _
  · simp only [hb, ite_false]
    exact hasDerivAt_const _ _

theorem faman_der_monomial (d₀ : PhaseTriple) (e : Fin 2 → ℝ) (b : Label) :
    FamanEntDer (fun t => monomialFamily (torusPhase d₀ (t • e)) b)
      (monomialVar (torusVar d₀ e) b) 0 := by
  unfold monomialFamily monomialVar
  exact faman_der_mul_const (faman_der_const_mul _ (faman_der_phaseMatrix d₀ e b.2)) _

theorem faman_der_hidFamily (ξ₀ : Fin 4 → ℂ) (H : Fin 4) (d₀ : PhaseTriple) (l : Label)
    (X Y : Fin 8 → ℝ) (e : Fin 2 → ℝ) :
    FamanEntDer (fun t => hidFamily ξ₀ H (suExp (t • X)) (suExp (t • Y)) (torusPhase d₀ (t • e)) l)
      (hidVar ξ₀ H d₀ (suMat X) (suMat Y) (torusVar d₀ e) l) 0 := by
  change FamanEntDer (fun t => hidFamily ξ₀ H (faman_sE (t • X)) (faman_sE (t • Y))
      (torusPhase d₀ (t • e)) l) (hidVar ξ₀ H d₀ (faman_sM X) (faman_sM Y) (torusVar d₀ e) l) 0
  simp only [hidFamily, hidVar]
  set L := gaugeLeft ξ₀ H
  set R := gaugeRight ξ₀ H
  set M₀ := monomialFamily d₀ (gaugeLabel H l)
  set Mv := monomialVar (torusVar d₀ e) (gaugeLabel H l)
  set SX := faman_sM X
  set SY := faman_sM Y
  have h1 : FamanEntDer (fun t => faman_sE (t • X) * L) (SX * L) 0 :=
    faman_der_mul_const (faman_der_sE X) L
  have h2 : FamanEntDer (fun t => faman_sE (t • X) * L * monomialFamily (torusPhase d₀ (t • e))
      (gaugeLabel H l)) (SX * L * M₀ + L * Mv) 0 := by
    have h := faman_der_mul h1 (faman_der_monomial d₀ e (gaugeLabel H l))
    have e0 : faman_sE ((0 : ℝ) • X) * L = L := by
      rw [zero_smul, faman_sE_zero, Matrix.one_mul]
    have e1 : monomialFamily (torusPhase d₀ ((0 : ℝ) • e)) (gaugeLabel H l) = M₀ := by
      rw [zero_smul, faman_torusPhase_zero]
    simp only [e0, e1] at h
    exact h
  have h3 : FamanEntDer (fun t => faman_sE (t • X) * L * monomialFamily (torusPhase d₀ (t • e))
      (gaugeLabel H l) * R) ((SX * L * M₀ + L * Mv) * R) 0 :=
    faman_der_mul_const h2 R
  have h4 := faman_der_mul h3 (faman_der_ct (faman_der_sE Y))
  have e2 : faman_sE ((0 : ℝ) • X) * L * monomialFamily (torusPhase d₀ ((0 : ℝ) • e))
      (gaugeLabel H l) * R = L * M₀ * R := by
    rw [zero_smul, zero_smul, faman_sE_zero, faman_torusPhase_zero, Matrix.one_mul]
  have e3 : (faman_sE ((0 : ℝ) • Y))ᴴ = 1 := by
    rw [zero_smul, faman_sE_zero, Matrix.conjTranspose_one]
  simp only [e2, e3] at h4
  have h5 := faman_der_smul (gaugeScalar H l) h4
  have e4 : (SX * L * M₀ + L * Mv) * R * 1 + L * M₀ * R * SYᴴ =
      SX * L * M₀ * R + L * M₀ * R * SYᴴ + L * Mv * R := by
    rw [Matrix.mul_one, Matrix.add_mul]
    abel
  rw [e4] at h5
  exact h5

end EntDer

/-! ## Layer 4: the pre-saturation family -/

theorem faman_analyticAt_hidEnt (ξ₀ : Fin 4 → ℂ) (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) (p : PreParam) :
    AnalyticAt ℝ (fun p : PreParam => faman_hidEnt ξ₀ H (suExp p.1) (suExp p.2.1)
      (torusPhase (anchorTriple ξ₀ hξ₀ H) p.2.2)) p := by
  show AnalyticAt ℝ (fun p : PreParam => fun l i j => hidFamily ξ₀ H (suExp p.1) (suExp p.2.1)
      (torusPhase (anchorTriple ξ₀ hξ₀ H) p.2.2) l i j) p
  refine analyticAt_pi_iff.mpr fun l => analyticAt_pi_iff.mpr fun i => analyticAt_pi_iff.mpr
    fun j => ?_
  exact faman_ana_hidFamily ξ₀ H _ l analyticAt_fst (faman_ana_fst analyticAt_snd)
    (faman_ana_snd analyticAt_snd) i j

theorem faman_preMap_eq (ξ₀ : Fin 4 → ℂ) (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    preMap ξ₀ hξ₀ H = fun p => faman_preBase ξ₀ H + faman_preLin H (faman_hidEnt ξ₀ H
      (suExp p.1) (suExp p.2.1) (torusPhase (anchorTriple ξ₀ hξ₀ H) p.2.2)) :=
  funext fun _ => faman_preCfg_eq _ _ _ _ _

theorem faman_analyticAt_preMap_all {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4)
    (p : PreParam) : AnalyticAt ℝ (preMap ξ₀ hξ₀ H) p := by
  rw [faman_preMap_eq]
  exact analyticAt_const.add (((faman_preLin H).analyticAt _).comp
    (faman_analyticAt_hidEnt ξ₀ hξ₀ H p))

theorem analyticAt_preMap {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    AnalyticAt ℝ (preMap ξ₀ hξ₀ H) 0 := faman_analyticAt_preMap_all hξ₀ H 0

theorem hasStrictFDerivAt_preMap {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    HasStrictFDerivAt (preMap ξ₀ hξ₀ H) (preDer ξ₀ hξ₀ H) 0 :=
  (analyticAt_preMap hξ₀ H).hasStrictFDerivAt

theorem faman_hasDerivAt_hidEnt (ξ₀ : Fin 4 → ℂ) (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) (p : PreParam) :
    HasDerivAt (fun t : ℝ => faman_hidEnt ξ₀ H (suExp (t • p).1) (suExp (t • p).2.1)
      (torusPhase (anchorTriple ξ₀ hξ₀ H) (t • p).2.2))
      (fun l i j => hidVar ξ₀ H (anchorTriple ξ₀ hξ₀ H) (suMat p.1) (suMat p.2.1)
        (torusVar (anchorTriple ξ₀ hξ₀ H) p.2.2) l i j) 0 := by
  refine hasDerivAt_pi.mpr fun l => hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => ?_
  exact faman_der_hidFamily ξ₀ H _ l p.1 p.2.1 p.2.2 i j

theorem preDer_apply {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) (p : PreParam) :
    preDer ξ₀ hξ₀ H p = preVar ξ₀ hξ₀ H p := by
  have hl : HasDerivAt (fun t : ℝ => t • p) p 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const p
  have h1 : HasDerivAt (preMap ξ₀ hξ₀ H ∘ fun t : ℝ => t • p) (preDer ξ₀ hξ₀ H p) 0 :=
    (analyticAt_preMap hξ₀ H).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)
  have h2 := (((faman_preLin H).hasFDerivAt).comp_hasDerivAt (0 : ℝ)
    (faman_hasDerivAt_hidEnt ξ₀ hξ₀ H p)).const_add (faman_preBase ξ₀ H)
  rw [faman_preVar_eq]
  refine h1.unique ?_
  convert h2 using 1
  funext t
  exact faman_preCfg_eq _ _ _ _ _

/-! ## Layer 5: saturation by the group chart -/

section Sat

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem faman_analyticAt_sat {u : P → Cfg} (hu : ∀ y, AnalyticAt ℝ u y) (q : ↥derC × P) :
    AnalyticAt ℝ (fun q : ↥derC × P => actC (groupChart q.1) (u q.2)) q := by
  have hb := ContinuousLinearMap.analyticAt_bilinear actC (groupChart q.1, u q.2)
  have hp : AnalyticAt ℝ (fun q : ↥derC × P => (groupChart q.1, u q.2)) q :=
    (AnalyticAt.comp (f := Prod.fst) (analyticAt_groupChart q.1) analyticAt_fst).prod
      (AnalyticAt.comp (f := Prod.snd) (hu q.2) analyticAt_snd)
  exact AnalyticAt.comp (g := fun x : CEnd × Cfg => actC x.1 x.2)
    (f := fun q : ↥derC × P => (groupChart q.1, u q.2)) hb hp

/- Adapted block. Source: the group/slice package of this project (not a public repository; no
commit pin), `geometry/native-group-slice-v1/final/GSSlice.lean`, `slice_hasStrictFDerivAt_generic`
(lines 79–99), project CKM native group/slice (Claude/Codex team), license: project-internal, no
SPDX identifier declared. Modifications: the affine second argument `P + ι p.2` is replaced by an
arbitrary map `u` with a (non-strict) Fréchet derivative, and the conclusion is `HasFDerivAt`.
Thanks to the authors of the group/slice package.
"If I have seen further it is by standing on the sholders of Giants." — Isaac Newton, letter to
Robert Hooke, 1676. -/

/-- Generic chain rule for `p ↦ B (g p.1) (u p.2)` at `0`, over abstract normed spaces (as GS's
`slice_hasStrictFDerivAt_generic`, so that no instance unification on submodules happens). -/
theorem faman_sat_generic {E₁ E₂ A V : Type*} [NormedAddCommGroup E₁]
    [NormedSpace ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : A →L[ℝ] V →L[ℝ] V) (g : E₁ → A) (g' : E₁ →L[ℝ] A) (hg : HasStrictFDerivAt g g' 0)
    (h1 : B (g 0) = ContinuousLinearMap.id ℝ V) (u : E₂ → V) (u' : E₂ →L[ℝ] V)
    (hu : HasFDerivAt u u' 0) (e : E₁ × E₂ →L[ℝ] V) (he : ∀ p, e p = B (g' p.1) (u 0) + u' p.2) :
    HasFDerivAt (fun p : E₁ × E₂ => B (g p.1) (u p.2)) e 0 := by
  have hg2 : HasFDerivAt (fun p : E₁ × E₂ => g p.1)
      (g'.comp (ContinuousLinearMap.fst ℝ E₁ E₂)) 0 :=
    hg.hasFDerivAt.comp (0 : E₁ × E₂) hasFDerivAt_fst
  have hu2 : HasFDerivAt (fun p : E₁ × E₂ => u p.2)
      (u'.comp (ContinuousLinearMap.snd ℝ E₁ E₂)) 0 :=
    hu.comp (0 : E₁ × E₂) hasFDerivAt_snd
  refine (B.hasFDerivAt_of_bilinear hg2 hu2).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun p => ?_
  rw [he]
  simp only [add_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', Prod.fst_zero, Prod.snd_zero, h1]
  rw [add_comm]
  rfl

theorem faman_hasFDerivAt_sat {u : P → Cfg} {u' : P →L[ℝ] Cfg} (hu : HasFDerivAt u u' 0) :
    HasFDerivAt (fun q : ↥derC × P => actC (groupChart q.1) (u q.2))
      (((actC.flip (u 0)).comp derC.subtypeL).coprod u') 0 :=
  faman_sat_generic actC groupChart derC.subtypeL hasStrictFDerivAt_groupChart
    (by rw [groupChart_zero, actC_one]) u u' hu _ fun _ => rfl

end Sat

theorem analyticAt_rawMap {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    AnalyticAt ℝ (rawMap ξ₀ hξ₀ H) 0 :=
  faman_analyticAt_sat (faman_analyticAt_preMap_all hξ₀ H) 0

theorem hasStrictFDerivAt_rawMap {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    HasStrictFDerivAt (rawMap ξ₀ hξ₀ H) (rawDer ξ₀ hξ₀ H) 0 :=
  (analyticAt_rawMap hξ₀ H).hasStrictFDerivAt

theorem rawDer_apply {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) (p : RawParam) :
    rawDer ξ₀ hξ₀ H p = orbitMapC ξ₀ (p.1 : CEnd) + preDer ξ₀ hξ₀ H p.2 := by
  have hu : HasFDerivAt (preMap ξ₀ hξ₀ H) (preDer ξ₀ hξ₀ H) 0 :=
    (analyticAt_preMap hξ₀ H).differentiableAt.hasFDerivAt
  have h := (faman_hasFDerivAt_sat hu).fderiv
  unfold rawDer
  change fderiv ℝ (fun q : RawParam => actC (groupChart q.1) (preMap ξ₀ hξ₀ H q.2)) 0 p = _
  rw [h, preMap_zero hξ₀ H]
  rfl

/-- The complement parameters `(X, e) ↦ (X, 0, e)`. -/
def faman_j62 (y : (Fin 8 → ℝ) × (Fin 2 → ℝ)) : PreParam := (y.1, 0, y.2)

theorem faman_analyticAt_j62 (y : (Fin 8 → ℝ) × (Fin 2 → ℝ)) : AnalyticAt ℝ faman_j62 y :=
  analyticAt_fst.prod (analyticAt_const.prod analyticAt_snd)

theorem faman_hasFDerivAt_j62 :
    HasFDerivAt faman_j62 ((ContinuousLinearMap.fst ℝ (Fin 8 → ℝ) (Fin 2 → ℝ)).prod
      ((0 : (Fin 8 → ℝ) × (Fin 2 → ℝ) →L[ℝ] (Fin 8 → ℝ)).prod
        (ContinuousLinearMap.snd ℝ (Fin 8 → ℝ) (Fin 2 → ℝ)))) 0 :=
  hasFDerivAt_fst.prodMk ((hasFDerivAt_const _ _).prodMk hasFDerivAt_snd)

theorem faman_rawMap62_eq (ξ₀ : Fin 4 → ℂ) (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    rawMap62 ξ₀ hξ₀ H = fun q : RawParam62 => actC (groupChart q.1)
      ((preMap ξ₀ hξ₀ H ∘ faman_j62) q.2) := rfl

theorem faman_analyticAt_preMap62 {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4)
    (y : (Fin 8 → ℝ) × (Fin 2 → ℝ)) : AnalyticAt ℝ (preMap ξ₀ hξ₀ H ∘ faman_j62) y :=
  AnalyticAt.comp (faman_analyticAt_preMap_all hξ₀ H _) (faman_analyticAt_j62 y)

theorem analyticAt_rawMap62 {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    AnalyticAt ℝ (rawMap62 ξ₀ hξ₀ H) 0 := by
  rw [faman_rawMap62_eq]
  exact faman_analyticAt_sat (faman_analyticAt_preMap62 hξ₀ H) 0

theorem hasStrictFDerivAt_rawMap62 {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    HasStrictFDerivAt (rawMap62 ξ₀ hξ₀ H) (rawDer62 ξ₀ hξ₀ H) 0 :=
  (analyticAt_rawMap62 hξ₀ H).hasStrictFDerivAt

theorem rawDer62_apply {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) (p : RawParam62) :
    rawDer62 ξ₀ hξ₀ H p = rawDer ξ₀ hξ₀ H (p.1, p.2.1, 0, p.2.2) := by
  have hp : HasFDerivAt (preMap ξ₀ hξ₀ H) (preDer ξ₀ hξ₀ H) (faman_j62 0) :=
    (faman_analyticAt_preMap_all hξ₀ H _).differentiableAt.hasFDerivAt
  have hu := HasFDerivAt.comp (f := faman_j62) (0 : (Fin 8 → ℝ) × (Fin 2 → ℝ)) hp
    faman_hasFDerivAt_j62
  have h := (faman_hasFDerivAt_sat hu).fderiv
  unfold rawDer62
  rw [faman_rawMap62_eq, h, rawDer_apply]
  have e0 : (preMap ξ₀ hξ₀ H ∘ faman_j62) 0 = literalCfg ξ₀ := preMap_zero hξ₀ H
  rw [e0]
  rfl

/-! ## Layer 6: the literal phase family -/

section Oct

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}

/-- Quaternion components as continuous linear functionals. -/
def faman_qre : Quaternion ℝ →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (QuaternionAlgebra.reₗ _ _ _)
def faman_qimI : Quaternion ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (QuaternionAlgebra.imIₗ _ _ _)
def faman_qimJ : Quaternion ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (QuaternionAlgebra.imJₗ _ _ _)
def faman_qimK : Quaternion ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (QuaternionAlgebra.imKₗ _ _ _)

theorem faman_ana_quat {f : E → Quaternion ℝ} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => (f y).re) x ∧ AnalyticAt ℝ (fun y => (f y).imI) x ∧
      AnalyticAt ℝ (fun y => (f y).imJ) x ∧ AnalyticAt ℝ (fun y => (f y).imK) x :=
  ⟨(faman_qre.analyticAt _).comp hf, (faman_qimI.analyticAt _).comp hf,
    (faman_qimJ.analyticAt _).comp hf, (faman_qimK.analyticAt _).comp hf⟩

/-- Quaternion conjugation as a continuous real-linear map. -/
def faman_qstarL : Quaternion ℝ →L[ℝ] Quaternion ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := star
      map_add' := star_add
      map_smul' := fun r q => by ext <;> simp }

theorem faman_ana_qstar {f : E → Quaternion ℝ} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => star (f y)) x :=
  (faman_qstarL.analyticAt _).comp hf

theorem faman_ana_octMul {f g : E → Glennie.Octonion} (hf : AnalyticAt ℝ f x)
    (hg : AnalyticAt ℝ g x) : AnalyticAt ℝ (fun y => Glennie.octMul (f y) (g y)) x := by
  unfold Glennie.octMul
  have f1 := faman_ana_fst hf
  have f2 := faman_ana_snd hf
  have g1 := faman_ana_fst hg
  have g2 := faman_ana_snd hg
  exact ((f1.mul g1).sub ((faman_ana_qstar g2).mul f2)).prod
    ((g2.mul f1).add (f2.mul (faman_ana_qstar g1)))

theorem faman_ana_octConj {f : E → Glennie.Octonion} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => Glennie.octConj (f y)) x := by
  unfold Glennie.octConj
  exact (faman_ana_qstar (faman_ana_fst hf)).prod (faman_ana_snd hf).neg

theorem faman_ana_octNormSq {f : E → Glennie.Octonion} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => Glennie.octNormSq (f y)) x := by
  unfold Glennie.octNormSq
  simp only [Quaternion.normSq_def]
  have f1 := faman_ana_fst hf
  have f2 := faman_ana_snd hf
  exact (faman_ana_quat (f1.mul (faman_ana_qstar f1))).1.add
    (faman_ana_quat (f2.mul (faman_ana_qstar f2))).1

theorem faman_ana_upper {f : E → Glennie.Albert}
    (h0 : AnalyticAt ℝ (fun y => (f y).d0) x) (h1 : AnalyticAt ℝ (fun y => (f y).d1) x)
    (h2 : AnalyticAt ℝ (fun y => (f y).d2) x) (h3 : AnalyticAt ℝ (fun y => (f y).o01) x)
    (h4 : AnalyticAt ℝ (fun y => (f y).o02) x) (h5 : AnalyticAt ℝ (fun y => (f y).o12) x) :
    AnalyticAt ℝ (fun y => NativePolynomial.upperCoordinates (f y)) x := by
  obtain ⟨a1, a2, a3, a4⟩ := faman_ana_quat (faman_ana_fst h3)
  obtain ⟨a5, a6, a7, a8⟩ := faman_ana_quat (faman_ana_snd h3)
  obtain ⟨b1, b2, b3, b4⟩ := faman_ana_quat (faman_ana_fst h4)
  obtain ⟨b5, b6, b7, b8⟩ := faman_ana_quat (faman_ana_snd h4)
  obtain ⟨c1, c2, c3, c4⟩ := faman_ana_quat (faman_ana_fst h5)
  obtain ⟨c5, c6, c7, c8⟩ := faman_ana_quat (faman_ana_snd h5)
  refine analyticAt_pi_iff.mpr fun k => ?_
  fin_cases k
  exacts [h0, h1, h2, a1, a2, a3, a4, a5, a6, a7, a8, b1, b2, b3, b4, b5, b6, b7, b8,
    c1, c2, c3, c4, c5, c6, c7, c8]

/-- `complexOctonion` is real-linear. -/
def faman_complexOctonionL : ℂ →L[ℝ] Glennie.Octonion :=
  LinearMap.toContinuousLinearMap
    { toFun := complexOctonion
      map_add' := fun z w => by
        apply Prod.ext
        · ext <;> simp [complexOctonion]
        · simp [complexOctonion]
      map_smul' := fun r z => by
        apply Prod.ext
        · ext <;> simp [complexOctonion]
        · simp [complexOctonion] }

theorem faman_ana_outer {z₁ z₂ : E → ℂ} (h1 : AnalyticAt ℝ z₁ x) (h2 : AnalyticAt ℝ z₂ x)
    (b b' : Glennie.Octonion) :
    AnalyticAt ℝ (fun y => NativePolynomial.upperCoordinates (nativeOuterProductThird
      (Glennie.octMul (complexOctonion (z₁ y)) b) (Glennie.octMul (complexOctonion (z₂ y)) b'))) x := by
  have hu : AnalyticAt ℝ (fun y => Glennie.octMul (complexOctonion (z₁ y)) b) x :=
    faman_ana_octMul ((faman_complexOctonionL.analyticAt _).comp h1) analyticAt_const
  have hw : AnalyticAt ℝ (fun y => Glennie.octMul (complexOctonion (z₂ y)) b') x :=
    faman_ana_octMul ((faman_complexOctonionL.analyticAt _).comp h2) analyticAt_const
  apply faman_ana_upper
  · exact analyticAt_const
  · exact (faman_ana_octNormSq hu).mul analyticAt_const
  · exact (faman_ana_octNormSq hw).mul analyticAt_const
  · exact (faman_ana_octConj hu).fun_const_smul (c := (1 / 3 : ℝ))
  · exact (faman_ana_octConj hw).fun_const_smul (c := (1 / 3 : ℝ))
  · exact (faman_ana_octMul hu (faman_ana_octConj hw)).fun_const_smul (c := (1 / 3 : ℝ))

theorem faman_ana_literalFamilyPoint {ξ : E → Fin 4 → ℂ} (hξ : ∀ a, AnalyticAt ℝ (fun y => ξ y a) x)
    (q : Fin 4) (s t : UnitaryErrorBases.ComplexQuartet.PhaseIndex) :
    AnalyticAt ℝ (fun y => NativePolynomial.upperCoordinates (literalFamilyPoint (ξ y) q s t)) x := by
  unfold literalFamilyPoint
  by_cases h0 : q = 0
  · simp only [h0, ite_true]
    exact analyticAt_const
  by_cases h1 : q = 1
  · simp only [h1, ite_true]
    exact analyticAt_const
  by_cases h2 : q = 2
  · simp only [h2, ite_true]
    exact faman_ana_outer ((hξ 0).mul analyticAt_const) ((hξ 1).mul analyticAt_const) _ _
  · simp only [h0, h1, h2, ite_false]
    exact faman_ana_outer ((hξ 2).mul analyticAt_const) ((hξ 3).mul analyticAt_const) _ _

theorem faman_ana_literalPoint {ξ : E → Fin 4 → ℂ} (hξ : ∀ a, AnalyticAt ℝ (fun y => ξ y a) x)
    (i : Fin 39) :
    AnalyticAt ℝ (fun y => NativePolynomial.upperCoordinates (literalPoint (ξ y) i)) x := by
  unfold literalPoint
  by_cases hi : i.val < 3
  · simp only [hi, dite_true]
    exact analyticAt_const
  · simp only [hi, dite_false]
    exact faman_ana_literalFamilyPoint hξ _ _ _

end Oct

theorem faman_ana_commonPhase (ξ₀ : Fin 4 → ℂ) (θ₀ : Fin 4 → ℝ) (a : Fin 4) :
    AnalyticAt ℝ (fun θ : Fin 4 → ℝ => commonPhase ξ₀ θ a) θ₀ := by
  unfold commonPhase
  exact analyticAt_const.mul (faman_ana_cexp ((faman_ana_ofReal
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) a).analyticAt _)).mul
      analyticAt_const))

theorem faman_analyticAt_literalPhase_all (ξ₀ : Fin 4 → ℂ) (θ₀ : Fin 4 → ℝ) :
    AnalyticAt ℝ (fun θ => literalCfg (commonPhase ξ₀ θ)) θ₀ := by
  show AnalyticAt ℝ (fun θ => fun i =>
    NativePolynomial.upperCoordinates (literalPoint (commonPhase ξ₀ θ) i)) θ₀
  exact analyticAt_pi_iff.mpr fun i => faman_ana_literalPoint (faman_ana_commonPhase ξ₀ θ₀) i

theorem analyticAt_literalPhase {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) :
    AnalyticAt ℝ (fun θ => literalCfg (commonPhase ξ₀ θ)) 0 :=
  faman_analyticAt_literalPhase_all ξ₀ 0

theorem hasStrictFDerivAt_literalPhase {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) :
    HasStrictFDerivAt (fun θ => literalCfg (commonPhase ξ₀ θ)) (phaseDer ξ₀) 0 :=
  (analyticAt_literalPhase hξ₀).hasStrictFDerivAt

/-! ## Layer 7: the common family -/

theorem analyticAt_commonMap {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) :
    AnalyticAt ℝ (commonMap ξ₀) 0 :=
  faman_analyticAt_sat (faman_analyticAt_literalPhase_all ξ₀) 0

theorem hasStrictFDerivAt_commonMap {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) :
    HasStrictFDerivAt (commonMap ξ₀) (commonDer ξ₀) 0 :=
  (analyticAt_commonMap hξ₀).hasStrictFDerivAt

theorem commonDer_apply {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (p : CommonParam) :
    commonDer ξ₀ p = orbitMapC ξ₀ (p.1 : CEnd) + phaseDer ξ₀ p.2 := by
  have hu : HasFDerivAt (fun θ => literalCfg (commonPhase ξ₀ θ)) (phaseDer ξ₀) 0 :=
    (analyticAt_literalPhase hξ₀).differentiableAt.hasFDerivAt
  have h := (faman_hasFDerivAt_sat hu).fderiv
  unfold commonDer
  change fderiv ℝ (fun q : CommonParam => actC (groupChart q.1)
    (literalCfg (commonPhase ξ₀ q.2))) 0 p = _
  rw [h]
  have e0 : commonPhase ξ₀ 0 = ξ₀ := by
    funext a
    simp [commonPhase]
  rw [e0]
  rfl

end CKM.NativeFourFamily

#print axioms CKM.NativeFourFamily.analyticAt_preMap
#print axioms CKM.NativeFourFamily.hasStrictFDerivAt_preMap
#print axioms CKM.NativeFourFamily.preDer_apply
#print axioms CKM.NativeFourFamily.analyticAt_rawMap
#print axioms CKM.NativeFourFamily.hasStrictFDerivAt_rawMap
#print axioms CKM.NativeFourFamily.rawDer_apply
#print axioms CKM.NativeFourFamily.analyticAt_rawMap62
#print axioms CKM.NativeFourFamily.hasStrictFDerivAt_rawMap62
#print axioms CKM.NativeFourFamily.rawDer62_apply
#print axioms CKM.NativeFourFamily.analyticAt_literalPhase
#print axioms CKM.NativeFourFamily.hasStrictFDerivAt_literalPhase
#print axioms CKM.NativeFourFamily.analyticAt_commonMap
#print axioms CKM.NativeFourFamily.hasStrictFDerivAt_commonMap
#print axioms CKM.NativeFourFamily.commonDer_apply
