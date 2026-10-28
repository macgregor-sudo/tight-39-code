module

public import HTPhaseCompleteHPack
public import HTRouteKron

@[expose] public section

/-!
# H values at phase ξ (first-party)

`Hxi_value`: for every unit ξ and every real ambient direction `V`,
`residualHxi ξ (originalF (Pξ + V))_ia = U^{-c_ia} · q_ia(d_i(U)⁻¹ · V)`, where `q_ia` is the ACTUAL
contracted quadratic of `weightC i a` at the accepted base (`contractedQuadratic Pbase (weightC i a)`).
`H_base_quadratic`: `BookHT.H z i a = q_ia(realV z)` (accepted fixed-seed `native_H_reproduction`,
HTRouteKron, plus the accepted quadratic expansion `contractedF_add_eq_quadratic`).
Hence the value identity at phase ξ is EXACTLY the transported anchor-velocity identity
`TAV : q_ia(d_i(U)⁻¹ · V z) = U^{c_ia} · q_ia(realV z)`, which only reads the quartet-`i` anchor
coordinates (accepted `hasAnchorSupport`). `H_reproduction_of_TAV` proves the Book value from it.
`TAV_low`: for quartets 0, 1 (d_i = id, c = 1) TAV holds for every direction that equals `realV z`
on the 21 states of frame 0 and windows 0, 1.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

noncomputable section

namespace Option2.NativeStress.HTPhaseComplete

open scoped BigOperators
open MvPolynomial NativePolynomial NativePolynomial.PartialAction ConfigurationResidualIndices
open Option2.NativeStress.AnchorSupport Option2.NativeStress.HTPhaseKron CKM.NativeFirstOrder
open Option2.NativeStress.BookHT.TangentCoordinates Option2.BookNativeBase

/-- The actual base contracted quadratic of the H component `(i, a)`. -/
noncomputable def qH (i : Fin 4) (a : Fin 3) : MvPolynomial (Fin 1053) ℂ :=
  contractedQuadratic Pbase (NativeH.weightC i a)

/-- Complexification of a real ambient vector. -/
def cplx (x : Fin 1053 → ℝ) : Fin 1053 → ℂ := fun v => ((x v : ℝ) : ℂ)

theorem contract_real (ell : Weights) (x : Fin 1053 → ℝ) :
    ∑ r : Fin 2184, ell r * ((Option2.NativeStress.originalF x r : ℝ) : ℂ) = contractedF ell (cplx x) := by
  unfold contractedF
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← eval_real_row]; rfl

/-- The base value is the base contracted quadratic on `realV z` (fixed seed). -/
theorem H_base_quadratic (z : BookHT.Blocks) (i : Fin 4) (a : Fin 3) :
    (BookHT.H z i).ofLp a = eval (cplx (realV z)) (qH i a) := by
  rw [← Option2.NativeStress.HTRouteKron.native_H_reproduction z i a]
  change NativeH.residualContraction _ i a = _
  rw [NativeH.residualContraction_apply, contract_real]
  have hc : cplx (bookBase + realV z) = Pbase + cplx (realV z) := by
    funext v; simp [cplx, Pbase_eq_bookBase]
  rw [hc, contractedF_add_eq_quadratic Pbase _ Pbase_solution (Pbase_equilibrium i a)]
  rfl

/-- The phase value is the base contracted quadratic on the transported direction. -/
theorem Hxi_value (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 4) (a : Fin 3) (V : Fin 1053 → ℝ) :
    (residualHxi ξ hξ (Option2.NativeStress.originalF (PartialAction.pack (literalCfg ξ) + V)) i).ofLp a =
      mono (Ux ξ hξ) (Ex.neg (cExp i a)) *
        eval (stateAct (invCartan (Ux ξ hξ) i) (cplx V)) (qH i a) := by
  rw [residualHxi, residualOf_apply]
  simp only [ellH, mul_assoc]
  rw [← Finset.mul_sum, ← AnalyticDerivative.stressCovector_apply]
  have h := transported_line ξ hξ i a V 1
  rw [one_smul, Complex.ofReal_one, one_pow, one_mul] at h
  rw [h]
  rfl

/-- The transported anchor-velocity identity (the exact remaining value statement). -/
def TAV (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (V : BookHT.Blocks → Fin 1053 → ℝ) : Prop :=
  ∀ (i : Fin 4) (a : Fin 3) (z : BookHT.Blocks),
    eval (stateAct (invCartan (Ux ξ hξ) i) (cplx (V z))) (qH i a) =
      mono (Ux ξ hξ) (cExp i a) * eval (cplx (realV z)) (qH i a)

/-- **Book H value at phase ξ from TAV**, for the same direction and the unchanged Book model. -/
theorem H_reproduction_of_TAV (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (V : BookHT.Blocks → Fin 1053 → ℝ)
    (hT : TAV ξ hξ V) (z : BookHT.Blocks) :
    residualHxi ξ hξ (Option2.NativeStress.originalF (PartialAction.pack (literalCfg ξ) + V z)) =
      BookHT.H z := by
  funext i
  apply PiLp.ext
  intro a
  rw [Hxi_value, hT i a z, H_base_quadratic, ← mul_assoc, mul_comm (mono _ _), mono_mul_neg, one_mul]

/-- The base quadratic only reads quartet-`i` anchor coordinates. -/
theorem qH_anchor_congr (i : Fin 4) (a : Fin 3) (X Y : Fin 1053 → ℂ)
    (h : ∀ v, AnchorCoordinate i v → X v = Y v) : eval X (qH i a) = eval Y (qH i a) := by
  rw [qH, ← contractedF_add_eq_quadratic Pbase _ Pbase_solution (Pbase_equilibrium i a),
    ← contractedF_add_eq_quadratic Pbase _ Pbase_solution (Pbase_equilibrium i a)]
  exact contractedF_eq_of_anchor_eq Pbase _ i Pbase_solution (Pbase_equilibrium i a)
    (NativeH.hasAnchorSupport Pbase i a) X Y h

theorem invCartan_low (U : Fin 4 → ℂˣ) (i : Fin 4) (hi : i = 0 ∨ i = 1) (x : Fin 27 → ℂ) :
    invCartan U i x = x := by
  change cartanFun (Uinv U) i x = x
  rw [cartanFun_eq_rot]
  have hd : ∀ j, dExp i j = (0, 0, 0, 0) := by
    intro j; rcases hi with rfl | rfl <;> unfold dExp <;> rw [if_neg (by decide), if_neg (by decide)]
  have h1 : (fun j => mono (Uinv U) (dExp i j)) = 1 := by
    funext j; rw [hd, mono_zero]; rfl
  have h2 : (fun j => mono (Uinv U) (Ex.neg (dExp i j))) = 1 := by
    funext j; rw [hd]; simpa [Ex.neg] using mono_zero (Uinv U)
  rw [h1, h2, rotForm_one]

/-- **TAV for quartets 0 and 1**, for every direction agreeing with `realV z` on states `< 21`. -/
theorem TAV_low (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (V : BookHT.Blocks → Fin 1053 → ℝ)
    (hV : ∀ z (v : Fin 1053), v.val / 27 < 21 → V z v = realV z v)
    (i : Fin 4) (hi : i = 0 ∨ i = 1) (a : Fin 3) (z : BookHT.Blocks) :
    eval (stateAct (invCartan (Ux ξ hξ) i) (cplx (V z))) (qH i a) =
      mono (Ux ξ hξ) (cExp i a) * eval (cplx (realV z)) (qH i a) := by
  have hc : cExp i a = (0, 0, 0, 0) := by rcases hi with rfl | rfl <;> simp [cExp]
  rw [hc, mono_zero, one_mul]
  apply qH_anchor_congr
  intro v hv
  have hst : stateAct (invCartan (Ux ξ hξ) i) (cplx (V z)) = cplx (V z) := by
    unfold stateAct
    simp only [invCartan_low _ i hi]
    exact pack_unpackC _
  rw [hst]
  simp only [cplx]
  rw [hV z v (by unfold AnchorCoordinate at hv; rcases hi with rfl | rfl <;> simp at hv <;> omega)]

end Option2.NativeStress.HTPhaseComplete

end

#print axioms Option2.NativeStress.HTPhaseComplete.H_base_quadratic
#print axioms Option2.NativeStress.HTPhaseComplete.Hxi_value
#print axioms Option2.NativeStress.HTPhaseComplete.H_reproduction_of_TAV
#print axioms Option2.NativeStress.HTPhaseComplete.qH_anchor_congr
#print axioms Option2.NativeStress.HTPhaseComplete.TAV_low
