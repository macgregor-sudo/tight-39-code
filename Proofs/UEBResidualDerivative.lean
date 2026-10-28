/-
Isolated first-party derivative prototype for the unchanged original UEB residual.
Ordinary finite-dimensional real calculus, using existing Mathlib product, sum,
pi and multilinear derivative APIs. No upstream proof body is copied.
Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55, Apache-2.0; Lean v4.35.0-rc2.
Thanks to the Lean and Mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
No first-party release license is assigned here.
-/
module

public import UEBDeterminantDerivative
import all UEBResidualDefinitions

@[expose] public section
noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open UnitaryErrorBases

namespace ArchitectureUEBDerivative

-- Explicit matrix multiplication avoids the pointwise Pi multiplication instance.
local notation "matrixMul" => (fun (A B : Matrix Index Index ℂ) => A * B)

/-- Explicit function carriers keep the normed Pi instances visible when the
unchanged, non-exposed Challenge probe is imported. These are definitionally
the original `Mat`, `Family`, and `Residual`, not different mathematical models. -/
abbrev AmbientMatrix := Index → Index → ℂ
abbrev AmbientFamily := Label → AmbientMatrix
abbrev AmbientResidual :=
  (Label → AmbientMatrix) × (Label → ℂ) × (Label → Label → ℂ)

/-- The unchanged original residual with explicit normed function carriers. -/
def residualOnAmbient : AmbientFamily → AmbientResidual := UnitaryErrorBases.residual

def entry (p : Label) (i j : Index) : AmbientFamily →L[ℝ] ℂ :=
  ((ContinuousLinearMap.proj j : (Index → ℂ) →L[ℝ] ℂ).comp
    (ContinuousLinearMap.proj i : AmbientMatrix →L[ℝ] (Index → ℂ))).comp
      (ContinuousLinearMap.proj p : AmbientFamily →L[ℝ] AmbientMatrix)

def conjEntry (p : Label) (i j : Index) : AmbientFamily →L[ℝ] ℂ :=
  Complex.conjCLE.toContinuousLinearMap.comp (entry p i j)

def productEntryDerivative (U : AmbientFamily) (p q : Label) (i j : Index) :
    AmbientFamily →L[ℝ] ℂ :=
  ∑ k : Index, (star (U p k i) • entry q k j + U q k j • conjEntry p k i)

def productDerivative (U : AmbientFamily) (p q : Label) : AmbientFamily →L[ℝ] AmbientMatrix :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    productEntryDerivative U p q i j

def pairingDerivative (U : AmbientFamily) (p q : Label) : AmbientFamily →L[ℝ] ℂ :=
  ∑ i : Index, productEntryDerivative U p q i i

def residualDerivative (U : AmbientFamily) : AmbientFamily →L[ℝ] AmbientResidual :=
  (ContinuousLinearMap.pi fun p => productDerivative U p p).prod
    ((ContinuousLinearMap.pi fun p =>
      (detMultilinear.linearDeriv (U p)).comp
        (ContinuousLinearMap.proj p : AmbientFamily →L[ℝ] AmbientMatrix)).prod
      (ContinuousLinearMap.pi fun p => ContinuousLinearMap.pi fun q =>
        if p = q then 0 else pairingDerivative U p q))

theorem productDerivative_apply (U V : AmbientFamily) (p q : Label) :
    productDerivative U p q V =
      matrixMul (Matrix.conjTranspose (U p)) (V q) +
        matrixMul (Matrix.conjTranspose (V p)) (U q) := by
  ext i j
  change productEntryDerivative U p q i j V =
    (∑ k : Index, star (U p k i) * V q k j) +
      (∑ k : Index, star (V p k i) * U q k j)
  simp [productEntryDerivative, entry, conjEntry, Finset.sum_add_distrib, mul_comm]

theorem pairingDerivative_apply (U V : AmbientFamily) (p q : Label) :
    pairingDerivative U p q V =
      Matrix.trace (matrixMul (Matrix.conjTranspose (V p)) (U q) +
        matrixMul (Matrix.conjTranspose (U p)) (V q)) := by
  change (∑ i : Index, productEntryDerivative U p q i i) V = _
  rw [sum_apply]
  change (∑ i : Index, productDerivative U p q V i i) = _
  rw [productDerivative_apply]
  rw [add_comm (matrixMul (Matrix.conjTranspose (U p)) (V q))]
  rfl

theorem hasFDerivAt_productEntry (U : AmbientFamily) (p q : Label) (i j : Index) :
    HasFDerivAt (fun W : AmbientFamily => matrixMul (Matrix.conjTranspose (W p)) (W q) i j)
      (productEntryDerivative U p q i j) U := by
  change HasFDerivAt (fun W => ∑ k : Index, star (W p k i) * W q k j) _ U
  unfold productEntryDerivative
  apply HasFDerivAt.fun_sum
  intro k _
  exact (conjEntry p k i).hasFDerivAt.mul (entry q k j).hasFDerivAt

theorem hasFDerivAt_product (U : AmbientFamily) (p q : Label) :
    HasFDerivAt (fun W : AmbientFamily => matrixMul (Matrix.conjTranspose (W p)) (W q))
      (productDerivative U p q) U := by
  exact hasFDerivAt_pi.mpr fun i =>
    hasFDerivAt_pi.mpr fun j => hasFDerivAt_productEntry U p q i j

theorem hasFDerivAt_pairing (U : AmbientFamily) (p q : Label) :
    HasFDerivAt (fun W : AmbientFamily => Matrix.trace (matrixMul (Matrix.conjTranspose (W p)) (W q)))
      (pairingDerivative U p q) U := by
  exact HasFDerivAt.fun_sum fun i _ => hasFDerivAt_productEntry U p q i i

theorem hasFDerivAt_residual (U : AmbientFamily) :
    HasFDerivAt residualOnAmbient (residualDerivative U) U := by
  unfold residualOnAmbient UnitaryErrorBases.residual residualDerivative
  apply HasFDerivAt.prodMk
  · exact hasFDerivAt_pi.mpr fun p => (hasFDerivAt_product U p p).sub_const 1
  · apply HasFDerivAt.prodMk
    · exact hasFDerivAt_pi.mpr fun p =>
        ((hasFDerivAt_det (U p)).comp U
          (ContinuousLinearMap.proj p : AmbientFamily →L[ℝ] AmbientMatrix).hasFDerivAt).sub_const (1 : ℂ)
    · apply hasFDerivAt_pi.mpr
      intro p
      apply hasFDerivAt_pi.mpr
      intro q
      by_cases hpq : p = q
      · simp only [hpq, ite_true]
        exact hasFDerivAt_const (0 : ℂ) U
      · simpa only [hpq, ite_false] using hasFDerivAt_pairing U p q

theorem differentiable_residual : Differentiable ℝ residual :=
  fun U => (hasFDerivAt_residual U).differentiableAt

theorem residualDerivative_apply_of_UEB (U V : AmbientFamily) (hU : IsUnitaryErrorBasis U) :
    residualDerivative U V =
      (fun p => matrixMul (Matrix.conjTranspose (U p)) (V p) +
         matrixMul (Matrix.conjTranspose (V p)) (U p),
       fun p => Matrix.trace (matrixMul (Matrix.conjTranspose (U p)) (V p)),
       fun p q => if p = q then 0 else
         Matrix.trace (matrixMul (Matrix.conjTranspose (V p)) (U q) +
           matrixMul (Matrix.conjTranspose (U p)) (V q))) := by
  apply Prod.ext
  · funext p
    exact productDerivative_apply U V p p
  · apply Prod.ext
    · funext p
      exact detDerivative_apply_of_specialUnitary (U p) (V p) (hU.1 p)
    · funext p q
      by_cases hpq : p = q
      · simp [residualDerivative, hpq]
      · simp [residualDerivative, hpq, pairingDerivative_apply]

theorem first_order_mem_iff (U V : Family) (hU : IsUnitaryErrorBasis U) :
    V ∈ firstOrderSpace U ↔ SatisfiesFirstOrder U V := by
  unfold firstOrderSpace
  change fderiv ℝ residualOnAmbient U V = 0 ↔ _
  rw [(hasFDerivAt_residual U).fderiv]
  change residualDerivative U V = 0 ↔ _
  rw [residualDerivative_apply_of_UEB U V hU]
  unfold SatisfiesFirstOrder
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro p
      exact congrArg (fun R : AmbientResidual => R.1 p) h
    · intro p
      exact congrArg (fun R : AmbientResidual => R.2.1 p) h
    · intro p q hpq
      have hpair := congrArg (fun R : AmbientResidual => R.2.2 p q) h
      change (if p = q then (0 : ℂ) else
        Matrix.trace ((V p).conjTranspose * U q + (U p).conjTranspose * V q)) = 0 at hpair
      simpa only [if_neg hpq] using hpair
  · rintro ⟨hgram, hdet, hpair⟩
    apply Prod.ext
    · funext p
      exact hgram p
    · apply Prod.ext
      · funext p
        exact hdet p
      · funext p q
        change (if p = q then (0 : ℂ) else
          Matrix.trace ((V p).conjTranspose * U q + (U p).conjTranspose * V q)) = 0
        by_cases hpq : p = q
        · simp only [if_pos hpq]
        · simpa only [if_neg hpq] using hpair p q hpq

#check hasFDerivAt_residual
#check differentiable_residual
#check first_order_mem_iff
#print axioms hasFDerivAt_residual
#print axioms first_order_mem_iff

end ArchitectureUEBDerivative
