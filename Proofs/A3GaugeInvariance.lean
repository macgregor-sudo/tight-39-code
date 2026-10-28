module

public import UEBResidualDerivative
public import ThreeCycleDimension
public import ThreeCycleUnitaryErrorBasis

@[expose] public section

/-!
# Gauge, relabelling and central invariance of the unrestricted first-order space

For the accepted `UnitaryErrorBases.firstOrderSpace`, a family obtained
from a unitary error basis by constant unitary left/right multiplication, a relabelling of the nine labels
and unit scalar factors has a real-linearly equivalent first-order space, via `V ↦ c p • (L * V (σ p) * R)`.
-/

namespace CKM.NativeFirstOrder

open UnitaryErrorBases

section GaugeHelpers

/-- Two-sided cancellation used by both compositions of the gauge map. -/
theorem sandwich_cancel (X Y P Q A : Mat) (hXY : X * Y = 1) (hPQ : P * Q = 1) :
    X * (Y * A * P) * Q = A := by
  rw [show X * (Y * A * P) * Q = (X * Y) * A * (P * Q) by simp only [Matrix.mul_assoc], hXY, hPQ,
    Matrix.one_mul, Matrix.mul_one]

theorem star_mul_self_of_normSq (z : ℂ) (hz : Complex.normSq z = 1) : star z * z = 1 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, hz, Complex.ofReal_one]

/-- The pairing of two gauge-transformed matrices. -/
theorem gauge_pair (L R A B : Mat) (hL : L.conjTranspose * L = 1) (a b : ℂ) :
    (a • (L * A * R)).conjTranspose * (b • (L * B * R)) =
      (star a * b) • (R.conjTranspose * (A.conjTranspose * B) * R) := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    show R.conjTranspose * (A.conjTranspose * L.conjTranspose) * (L * B * R) =
      R.conjTranspose * (A.conjTranspose * (L.conjTranspose * L) * B) * R by
        simp only [Matrix.mul_assoc],
    hL, Matrix.mul_one]

theorem trace_conj_unitary (R X : Mat) (hR : R * R.conjTranspose = 1) :
    Matrix.trace (R.conjTranspose * X * R) = Matrix.trace X := by
  rw [Matrix.trace_mul_cycle, hR, Matrix.one_mul]

/-- The real-linear gauge map `V ↦ c p • (L * V (σ p) * R)` on the full ambient. -/
def gaugeMap (L R : Mat) (c : Label → ℂ) (σ : Label ≃ Label) : Family →ₗ[ℝ] Family where
  toFun V p := c p • (L * V (σ p) * R)
  map_add' V W := by
    funext p
    simp only [Pi.add_apply, Matrix.mul_add, Matrix.add_mul, smul_add]
  map_smul' r V := by
    funext p
    simp only [Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
    exact smul_comm (c p) r _

theorem gaugeMap_apply (L R : Mat) (c : Label → ℂ) (σ : Label ≃ Label) (V : Family) (p : Label) :
    gaugeMap L R c σ V p = c p • (L * V (σ p) * R) := rfl

/-- The gauge map sends the first-order space of `U` into that of its gauge image. -/
theorem gaugeMap_mem (U U' : Family) (hU : IsUnitaryErrorBasis U)
    (hU' : IsUnitaryErrorBasis U') (L R : Mat) (hL : L.conjTranspose * L = 1)
    (hR : R * R.conjTranspose = 1) (c : Label → ℂ) (hc : ∀ p, Complex.normSq (c p) = 1)
    (σ : Label ≃ Label) (h : ∀ p, U' p = c p • (L * U (σ p) * R)) (V : Family)
    (hV : V ∈ firstOrderSpace U) : gaugeMap L R c σ V ∈ firstOrderSpace U' := by
  rw [ArchitectureUEBDerivative.first_order_mem_iff _ _ hU] at hV
  rw [ArchitectureUEBDerivative.first_order_mem_iff _ _ hU']
  obtain ⟨h1, h2, h3⟩ := hV
  refine ⟨?_, ?_, ?_⟩
  · intro p
    rw [gaugeMap_apply, h p, gauge_pair L R _ _ hL, gauge_pair L R _ _ hL,
      star_mul_self_of_normSq _ (hc p), one_smul, one_smul, ← Matrix.add_mul, ← Matrix.mul_add,
      h1 (σ p), Matrix.mul_zero, Matrix.zero_mul]
  · intro p
    rw [gaugeMap_apply, h p, gauge_pair L R _ _ hL, star_mul_self_of_normSq _ (hc p), one_smul,
      trace_conj_unitary R _ hR, h2 (σ p)]
  · intro p q hpq
    rw [gaugeMap_apply, gaugeMap_apply, h p, h q, gauge_pair L R _ _ hL, gauge_pair L R _ _ hL,
      ← smul_add, Matrix.trace_smul, ← Matrix.add_mul, ← Matrix.mul_add,
      trace_conj_unitary R _ hR, h3 (σ p) (σ q) (σ.injective.ne hpq), smul_zero]

/-- The inverse gauge data presents `U` as a gauge image of `U'`. -/
theorem gauge_symm (U U' : Family) (L R : Mat) (hL : L.conjTranspose * L = 1)
    (hR : R * R.conjTranspose = 1) (c : Label → ℂ) (hc : ∀ p, Complex.normSq (c p) = 1)
    (σ : Label ≃ Label) (h : ∀ p, U' p = c p • (L * U (σ p) * R)) (q : Label) :
    U q = (fun q => star (c (σ.symm q))) q •
      (L.conjTranspose * U' (σ.symm q) * R.conjTranspose) := by
  rw [h, Equiv.apply_symm_apply, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    star_mul_self_of_normSq _ (hc _), one_smul, sandwich_cancel _ _ _ _ _ hL hR]

theorem gaugeMap_left_inv (L R : Mat) (hL : L.conjTranspose * L = 1)
    (hR : R * R.conjTranspose = 1) (c : Label → ℂ) (hc : ∀ p, Complex.normSq (c p) = 1)
    (σ : Label ≃ Label) (V : Family) :
    gaugeMap L.conjTranspose R.conjTranspose (fun q => star (c (σ.symm q))) σ.symm
      (gaugeMap L R c σ V) = V := by
  funext q
  rw [gaugeMap_apply, gaugeMap_apply, Equiv.apply_symm_apply, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul, star_mul_self_of_normSq _ (hc _), one_smul, sandwich_cancel _ _ _ _ _ hL hR]

theorem gaugeMap_right_inv (L R : Mat) (hL : L.conjTranspose * L = 1)
    (hR : R * R.conjTranspose = 1) (c : Label → ℂ) (hc : ∀ p, Complex.normSq (c p) = 1)
    (σ : Label ≃ Label) (W : Family) :
    gaugeMap L R c σ
      (gaugeMap L.conjTranspose R.conjTranspose (fun q => star (c (σ.symm q))) σ.symm W) = W := by
  funext p
  have hL' : L * L.conjTranspose = 1 := mul_eq_one_comm.mp hL
  have hR' : R.conjTranspose * R = 1 := mul_eq_one_comm.mp hR
  rw [gaugeMap_apply, gaugeMap_apply, Equiv.symm_apply_apply, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul, mul_comm, star_mul_self_of_normSq _ (hc _), one_smul,
    sandwich_cancel _ _ _ _ _ hL' hR']

end GaugeHelpers

theorem firstOrderSpace_equiv_of_gauge (U U' : Family) (hU : IsUnitaryErrorBasis U)
    (hU' : IsUnitaryErrorBasis U') (L R : Mat) (hL : L.conjTranspose * L = 1)
    (hR : R * R.conjTranspose = 1) (c : Label → ℂ) (hc : ∀ p, Complex.normSq (c p) = 1)
    (σ : Label ≃ Label) (h : ∀ p, U' p = c p • (L * U (σ p) * R)) :
    Nonempty (firstOrderSpace U ≃ₗ[ℝ] firstOrderSpace U') := by
  have hL' : L.conjTranspose.conjTranspose * L.conjTranspose = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp hL
  have hR' : R.conjTranspose * R.conjTranspose.conjTranspose = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp hR
  have hc' : ∀ q, Complex.normSq ((fun q => star (c (σ.symm q))) q) = 1 := fun q => by
    rw [Complex.star_def, Complex.normSq_conj]
    exact hc _
  let f : firstOrderSpace U →ₗ[ℝ] firstOrderSpace U' :=
    (gaugeMap L R c σ).restrict (gaugeMap_mem U U' hU hU' L R hL hR c hc σ h)
  let g : firstOrderSpace U' →ₗ[ℝ] firstOrderSpace U :=
    (gaugeMap L.conjTranspose R.conjTranspose (fun q => star (c (σ.symm q))) σ.symm).restrict
      (gaugeMap_mem U' U hU' hU L.conjTranspose R.conjTranspose hL' hR' _ hc' σ.symm
        (gauge_symm U U' L R hL hR c hc σ h))
  refine ⟨LinearEquiv.ofLinearMap f g ?_ ?_⟩
  · ext W : 2
    exact gaugeMap_right_inv L R hL hR c hc σ W
  · ext V : 2
    exact gaugeMap_left_inv L R hL hR c hc σ V

theorem finrank_firstOrderSpace_of_gauge (U U' : Family) (hU : IsUnitaryErrorBasis U)
    (hU' : IsUnitaryErrorBasis U') (L R : Mat) (hL : L.conjTranspose * L = 1)
    (hR : R * R.conjTranspose = 1) (c : Label → ℂ) (hc : ∀ p, Complex.normSq (c p) = 1)
    (σ : Label ≃ Label) (h : ∀ p, U' p = c p • (L * U (σ p) * R)) :
    Module.finrank ℝ (firstOrderSpace U') = Module.finrank ℝ (firstOrderSpace U) := by
  obtain ⟨e⟩ := firstOrderSpace_equiv_of_gauge U U' hU hU' L R hL hR c hc σ h
  exact e.finrank_eq.symm

/-- A gauge image of the normal-form family has the accepted dimension `18 + 2r`. -/
theorem finrank_firstOrderSpace_of_gauge_monomial (d : PhaseTriple) (U' : Family)
    (hU' : IsUnitaryErrorBasis U') (L R : Mat) (hL : L.conjTranspose * L = 1)
    (hR : R * R.conjTranspose = 1) (c : Label → ℂ) (hc : ∀ p, Complex.normSq (c p) = 1)
    (σ : Label ≃ Label) (h : ∀ p, U' p = c p • (L * monomialFamily d (σ p) * R)) :
    Module.finrank ℝ (firstOrderSpace U') = 18 + 2 * resonanceCount d := by
  rw [finrank_firstOrderSpace_of_gauge (monomialFamily d) U'
    (ThreeCycleMatrix.monomial_family_is_unitary_error_basis d) hU' L R hL hR c hc σ h]
  exact ThreeCycleMatrix.firstOrder_finrank d


end CKM.NativeFirstOrder
