module

public import HTPhaseCompleteHStress

@[expose] public section

/-!
# H covectors at phase ξ: explicit row formulas, unit-character normalisation, packaging

`ellH ξ hξ i a := c_ia(U)⁻¹ • (weightC i a ∘ ρ_{d_i(U)⁻¹})`, `U = ξ / exactPhases`, with the unit
monomial `c_ia(U) = U^{cExp i a}`: `c_0a = c_1a = 1`, `(c_20, c_21, c_22) = ((u0u1)⁻¹, u0, u1)`,
`(c_30, c_31, c_32) = (u3, (u2u3)⁻¹, u2)` for the LEAN-ORIENTED weights `weightC` (hSpec conjugates
components (2,0), (3,1), (1,2)); exact Python, py/orient_c.py at xi1, py/run_H2.out for the Book orientation; it is needed only for the value
identity; equilibrium holds for every normalisation). Names follow the covector interface
(`ellH`, `residualOf`, `residualHxi`, `H_equilibrium`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

noncomputable section

namespace Option2.NativeStress.HTPhaseComplete

open scoped BigOperators
open NativePolynomial NativePolynomial.PartialAction ConfigurationResidualIndices
open Option2.NativeStress.AnchorSupport Option2.NativeStress.HTPhaseKron CKM.NativeFirstOrder

/-! ## Explicit row formulas of the transported weights -/

theorem sum_fNumber (f : Fin 2184 → ℂ) : ∑ q : Fin 2184, f q = ∑ l : FLabel, f (fNumber l) :=
  (Equiv.sum_comp fNumber f).symm

theorem single_fNumber (l₀ : FLabel) :
    (fun q : FLabel => (Pi.single (fNumber l₀) (1 : ℂ) : Fin 2184 → ℂ) (fNumber q)) =
      fun q => if q = l₀ then 1 else 0 := by
  funext q
  by_cases h : q = l₀
  · subst h; simp
  · rw [Pi.single_apply, if_neg (fun e => h (fNumber.injective e)), if_neg h]

theorem lin_zero_of (g : (Fin 27 → ℂ) →ₗ[ℂ] (Fin 27 → ℂ)) (v : Fin 27 → ℂ) (h : ∀ j, v j = 0)
    (n : Fin 27) : g v n = 0 := by
  rw [show v = 0 from funext h, map_zero]; rfl

theorem lin_congr (g : (Fin 27 → ℂ) →ₗ[ℂ] (Fin 27 → ℂ)) (v w : Fin 27 → ℂ) (h : ∀ j, v j = w j)
    (n : Fin 27) : g v n = g w n := by
  rw [funext h]

theorem rowAct_apply_label (g : (Fin 27 → ℂ) →ₗ[ℂ] (Fin 27 → ℂ)) (y : Fin 2184 → ℂ) (l : FLabel) :
    rowAct g y (fNumber l) = labelAct g (fun q => y (fNumber q)) l := by
  simp [rowAct]

/-- Row formula on scalar rows: trace and pair weights are unchanged. -/
theorem ellRawU_trace (U : Fin 4 → ℂˣ) (i : Fin 4) (a : Fin 3) (k : Fin 39) :
    ellRawU U i a (fNumber (fTrace k)) = NativeH.weightC i a (fNumber (fTrace k)) := by
  unfold ellRawU
  rw [sum_fNumber, Finset.sum_eq_single (fTrace k)]
  · rw [rowAct_apply_label, single_fNumber]; simp [labelAct, fTrace]
  · intro l _ hl
    rw [rowAct_apply_label, single_fNumber]
    rcases l with ⟨k', n⟩ | k' | ⟨f, n⟩ | ij
    · simp only [labelAct]
      rw [lin_zero_of _ _ (fun j => by simp [fTrace, fId]), mul_zero]
    · simp only [labelAct]
      rw [if_neg (show fTrace k' ≠ fTrace k from hl), mul_zero]
    · simp only [labelAct]
      rw [lin_zero_of _ _ (fun j => by simp [fTrace, fSum]), mul_zero]
    · simp [labelAct, fPair, fTrace]
  · simp

theorem ellRawU_pair (U : Fin 4 → ℂˣ) (i : Fin 4) (a : Fin 3) (ij : Pair 39) :
    ellRawU U i a (fNumber (fPair ij)) = NativeH.weightC i a (fNumber (fPair ij)) := by
  unfold ellRawU
  rw [sum_fNumber, Finset.sum_eq_single (fPair ij)]
  · rw [rowAct_apply_label, single_fNumber]; simp [labelAct, fPair]
  · intro l _ hl
    rw [rowAct_apply_label, single_fNumber]
    rcases l with ⟨k', n⟩ | k' | ⟨f, n⟩ | ij'
    · simp only [labelAct]
      rw [lin_zero_of _ _ (fun j => by simp [fPair, fId]), mul_zero]
    · simp [labelAct, fPair, fTrace]
    · simp only [labelAct]
      rw [lin_zero_of _ _ (fun j => by simp [fPair, fSum]), mul_zero]
    · simp only [labelAct]
      rw [if_neg (show fPair ij' ≠ fPair ij from hl), mul_zero]
  · simp

/-- Row formula on an idempotency row `(k, m)`: `Σ_n ℓ(k, n) · (E e_m)_n`. -/
theorem ellRawU_id (U : Fin 4 → ℂˣ) (i : Fin 4) (a : Fin 3) (k : Fin 39) (m : Fin 27) :
    ellRawU U i a (fNumber (fId k m)) =
      ∑ n : Fin 27, NativeH.weightC i a (fNumber (fId k n)) *
        invCartan U i (Pi.single m 1) n := by
  unfold ellRawU
  rw [sum_fNumber]
  simp only [rowAct_apply_label, single_fNumber]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h2 : ∑ l : Fin 39, NativeH.weightC i a (fNumber (.inr (.inl l))) *
      labelAct (invCartan U i) (fun q => if q = fId k m then 1 else 0) (.inr (.inl l)) = 0 := by
    apply Finset.sum_eq_zero; intro l _; simp [labelAct, fTrace, fId]
  have h3 : ∑ l : Fin 13 × Fin 27, NativeH.weightC i a (fNumber (.inr (.inr (.inl l)))) *
      labelAct (invCartan U i) (fun q => if q = fId k m then 1 else 0) (.inr (.inr (.inl l))) = 0 := by
    apply Finset.sum_eq_zero; rintro ⟨f, n⟩ _
    simp only [labelAct]
    rw [lin_zero_of _ _ (fun j => by simp [fSum, fId]), mul_zero]
  have h4 : ∑ l : Pair 39, NativeH.weightC i a (fNumber (.inr (.inr (.inr l)))) *
      labelAct (invCartan U i) (fun q => if q = fId k m then 1 else 0) (.inr (.inr (.inr l))) = 0 := by
    apply Finset.sum_eq_zero; intro l _; simp [labelAct, fPair, fId]
  rw [h2, h3, h4, add_zero, add_zero, Fintype.sum_prod_type, Finset.sum_eq_single k]
  · simp only [add_zero]
    apply Finset.sum_congr rfl
    intro n _
    simp only [labelAct]
    rw [lin_congr _ _ (Pi.single m 1) (fun j => by
      by_cases hj : j = m <;> simp [fId, hj, Pi.single_apply])]
    rfl
  · intro k' _ hk'
    apply Finset.sum_eq_zero; intro n _
    simp only [labelAct]
    rw [lin_zero_of _ _ (fun j => by simp [fId, hk']), mul_zero]
  · simp

/-! ## Unit characters and packaging -/

/-- Exponent of the unit monomial `c_ia`. -/
def cExp (i : Fin 4) (a : Fin 3) : Ex :=
  if i = 2 then ![(-1, -1, 0, 0), (1, 0, 0, 0), (0, 1, 0, 0)] a
  else if i = 3 then ![(0, 0, 0, 1), (0, 0, -1, -1), (0, 0, 1, 0)] a
  else (0, 0, 0, 0)

/-- **The transported H covector at phase ξ** (every unit ξ). -/
noncomputable def ellH (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 4) (a : Fin 3) : Weights :=
  fun r => mono (Ux ξ hξ) (Ex.neg (cExp i a)) * ellRaw ξ hξ i a r

/-- Same packaging as the accepted `NativeH.residualContraction`. -/
def residualOf (ell : Fin 4 → Fin 3 → Weights) : (Fin 2184 → ℝ) →L[ℝ] BookHT.Blocks :=
  ContinuousLinearMap.pi fun i =>
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℂ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun a => AnalyticDerivative.stressCovector (ell i a))

def residualHxi (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : (Fin 2184 → ℝ) →L[ℝ] BookHT.Blocks :=
  residualOf (ellH ξ hξ)

theorem residualOf_apply (ell : Fin 4 → Fin 3 → Weights) (q : Fin 2184 → ℝ) (i : Fin 4) (a : Fin 3) :
    (residualOf ell q i).ofLp a = ∑ r : Fin 2184, ell i a r * (q r : ℂ) :=
  AnalyticDerivative.stressCovector_apply (ell i a) q

theorem stressCovector_smul (c : ℂ) (ell : Weights) :
    AnalyticDerivative.stressCovector (fun r => c * ell r) =
      c • AnalyticDerivative.stressCovector ell := by
  ext y
  simp only [ContinuousLinearMap.smul_apply, AnalyticDerivative.stressCovector_apply, smul_eq_mul,
    Finset.mul_sum, mul_assoc]

/-- **H equilibrium at every unit phase**. -/
theorem H_equilibrium (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 4) (a : Fin 3) :
    (AnalyticDerivative.stressCovector (ellH ξ hξ i a)).comp
      (fderiv ℝ Option2.NativeStress.originalF (PartialAction.pack (literalCfg ξ))) = 0 := by
  change (AnalyticDerivative.stressCovector
    (fun r => mono (Ux ξ hξ) (Ex.neg (cExp i a)) * ellRaw ξ hξ i a r)).comp _ = 0
  rw [stressCovector_smul, ContinuousLinearMap.smul_comp, ellRaw_equilibrium]
  ext x
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply, smul_zero]

/-- Block form. -/
theorem residualHxi_equilibrium (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    (residualHxi ξ hξ).comp
      (fderiv ℝ Option2.NativeStress.originalF (PartialAction.pack (literalCfg ξ))) = 0 := by
  ext W i a
  have h := congrArg (fun L : (Fin 1053 → ℝ) →L[ℝ] ℂ => L W) (H_equilibrium ξ hξ i a)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at h ⊢
  rw [residualHxi, residualOf_apply, ← AnalyticDerivative.stressCovector_apply, h]
  rfl

end Option2.NativeStress.HTPhaseComplete

end

#print axioms Option2.NativeStress.HTPhaseComplete.ellRawU_trace
#print axioms Option2.NativeStress.HTPhaseComplete.ellRawU_pair
#print axioms Option2.NativeStress.HTPhaseComplete.ellRawU_id
#print axioms Option2.NativeStress.HTPhaseComplete.H_equilibrium
#print axioms Option2.NativeStress.HTPhaseComplete.residualHxi_equilibrium
