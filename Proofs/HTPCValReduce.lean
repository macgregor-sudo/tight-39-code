module

public import HTPCValSupp
public import HTPhaseCompleteDirection
public import NativeHResidualQuadratic
public import NativeTAnalyticBridge

@[expose] public section

/-!
# Value reduction at every unit phase (first-party)

For every unit phase `ξ`, every `z`, and every row weight `ell` that annihilates the original Jacobian
columns at `Pξ = pack (literalCfg ξ)`:

  `Σ_r ell_r · F_r(Pξ + Vξ z) = Σ_r ell_r · Q_r( N(y) · Pξ )`,   `y = realCoordinates z`,

where `N(y) = Σ_j y_j (A_j − K_j)` (`nOp`; `A_j` the certificate's derivation extensions, `K_j` the specified
fixed operators) acts state-wise. Chain: `F(Pξ) = 0` (accepted `literalCfg_all_original_F`), tangency
(`Vxi_tangent`, through the accepted derivative `originalF_hasFDerivAt` / `original_column_cast`), the gauge lemma
with `D = Σ_j y_j A_j` (`dirDer_props`), and `Vξ z = Re(K(y)·literalCfg ξ)` (`Vxi_fixedK_complex`).
No hypothesis on the phase beyond `IsUnitPhase`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace Option2.NativeStress.HTPhaseComplete

open scoped BigOperators
open CKM.NativeFirstOrder NativePolynomial QuarticCertificate.RowBridge ConfigurationResidualIndices
open NativePolynomial.ConfigurationResiduals NativeH.Equilibrium PolynomialJets AnchorSupport

/-- `N(y) = Σ_j y_j (A_j − K_j)` through a ring map from `Q12` (`nZ j = 2(A_j − K_j)`). -/
def nOp {R : Type*} [CommRing R] (ι : Q12 →+* R) (y : Fin 24 → R) : Fin 27 → Fin 27 → R :=
  fun k c => ∑ j, y j * (ι kHalf * ι (gToQ12 (nZ j k c)))

/-- The complexified literal point. -/
noncomputable abbrev Xc (ξ : Fin 4 → ℂ) : Fin 1053 → ℂ := fun v => ((Pxi ξ v : ℝ) : ℂ)

theorem Xc_vi (ξ : Fin 4 → ℂ) (i : Fin 39) (k : Fin 27) :
    Xc ξ (variableIndex i k) = ((literalCfg ξ i k : ℝ) : ℂ) := by
  simp only [Xc, Pxi, PartialAction.pack_variableIndex]

/-- `Vξ z`, complexified, is `K(y)` applied state-wise to the literal point. -/
theorem vxi_op (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (z : BookHT.Blocks) :
    (fun v => ((Vxi ξ hξ z v : ℝ) : ℂ)) =
      opApply (fun k c => ∑ j, BookHT.Dictionary.realCoordinates z j * Q12.toComplex (kMat j k c)) (Xc ξ) := by
  funext v
  rw [Vxi_fixedK_complex]
  unfold kWeight opApply
  simp only [Xc_vi, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc]; rfl

theorem w_eq (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (z : BookHT.Blocks) :
    opApply (dirDer Q12.toComplex (BookHT.Dictionary.realCoordinates z)) (Xc ξ) -
        (fun v => ((Vxi ξ hξ z v : ℝ) : ℂ)) =
      opApply (nOp Q12.toComplex (BookHT.Dictionary.realCoordinates z)) (Xc ξ) := by
  rw [vxi_op]
  funext v
  simp only [Pi.sub_apply, opApply, dirDer, nOp, ← Finset.sum_sub_distrib, ← sub_mul]
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [aMat, kMat_eq_kZ, nZ, map_sub, map_mul, map_mul, map_sub]
  ring

theorem F_at_literal (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (r : Fin 2184) :
    rowValue (1/2 : ℂ) (1/3 : ℂ) r (Xc ξ) = 0 := by
  rw [← NativeH.Reproduction.originalF_complex]
  have h : Option2.NativeStress.originalF (Pxi ξ) r = 0 := literalCfg_all_original_F ξ hξ r
  rw [h, Complex.ofReal_zero]

theorem jac_cast (C : Fin 1053 → ℝ) (r : Fin 2184) (c : Fin 1053) :
    (MvPolynomial.eval C (MvPolynomial.pderiv c (fRow (1/2 : ℝ) (1/3 : ℝ) r)) : ℂ) =
      jacobianEntry (1/2 : ℂ) (1/3 : ℂ) r (fun v => (C v : ℂ)) c := by
  rw [NativeT.original_column_cast]
  exact equationLinearMatrix_translate_fRow _ _ _ r c

/-- Tangency, row form. -/
theorem tangent_rows (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (z : BookHT.Blocks) (r : Fin 2184) :
    ∑ c, jacobianEntry (1/2 : ℂ) (1/3 : ℂ) r (Xc ξ) c * ((Vxi ξ hξ z c : ℝ) : ℂ) = 0 := by
  have h := Vxi_tangent ξ hξ z
  rw [(NativeT.originalF_hasFDerivAt (Pxi ξ)).fderiv] at h
  have hr := congrFun h r
  simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    Pi.zero_apply] at hr
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hr
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_zero, jac_cast] at hc
  exact hc

/-- **Value reduction.** -/
theorem value_reduce (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (ell : Fin 2184 → ℂ)
    (hcol : ∀ c, ∑ r, ell r * equationLinearMatrix (translatedRow (Xc ξ)) r c = 0)
    (z : BookHT.Blocks) :
    ∑ r, ell r * ((Option2.NativeStress.originalF (Pxi ξ + Vxi ξ hξ z) r : ℝ) : ℂ) =
      ∑ r, ell r * quadraticPartValue (1/2 : ℂ) r
        (opApply (nOp Q12.toComplex (BookHT.Dictionary.realCoordinates z)) (Xc ξ)) := by
  set y := BookHT.Dictionary.realCoordinates z
  set vC : Fin 1053 → ℂ := fun v => ((Vxi ξ hξ z v : ℝ) : ℂ)
  have hℓ : ∀ c, ∑ r, ell r * jacobianEntry (1/2 : ℂ) (1/3 : ℂ) r (Xc ξ) c = 0 := by
    intro c; rw [← hcol c]
    refine Finset.sum_congr rfl fun r _ => ?_
    congr 1
    exact (equationLinearMatrix_translate_fRow _ _ _ r c).symm
  have hD := dirDer_props Q12.toComplex y
  have hsplit : (fun c => (((Pxi ξ + Vxi ξ hξ z) c : ℝ) : ℂ)) = Xc ξ + vC := by
    funext c; simp only [Pi.add_apply, Complex.ofReal_add, Xc, vC]
  calc ∑ r, ell r * ((Option2.NativeStress.originalF (Pxi ξ + Vxi ξ hξ z) r : ℝ) : ℂ)
      = ∑ r, ell r * quadraticPartValue (1/2 : ℂ) r vC := by
        refine Finset.sum_congr rfl fun r _ => ?_
        congr 1
        rw [NativeH.Reproduction.originalF_complex, hsplit, NativeH.Reproduction.rowValue_add,
          F_at_literal ξ hξ r, tangent_rows ξ hξ z r]
        ring
    _ = ∑ r, ell r * quadraticPartValue (1/2 : ℂ) r (opApply (dirDer Q12.toComplex y) (Xc ξ) - vC) :=
        (gauge (1/2 : ℂ) (1/3 : ℂ) (by norm_num) (dirDer Q12.toComplex y) hD.1 hD.2.1 hD.2.2.1 hD.2.2.2
          (Xc ξ) vC ell (F_at_literal ξ hξ) hℓ (tangent_rows ξ hξ z)).symm
    _ = _ := by rw [w_eq]

end Option2.NativeStress.HTPhaseComplete

#print axioms Option2.NativeStress.HTPhaseComplete.value_reduce
