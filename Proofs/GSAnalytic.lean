module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Normed.Algebra.Exponential

@[expose] public section

/-!
# Generic analytic tools: analytic local inverses and exponentials of derivations

Mathlib-only module (no native import).

* `analyticAt_toOpenPartialHomeomorph_symm`: the analytic inverse function theorem in the form used
  below. The local inverse produced by `HasStrictFDerivAt.toOpenPartialHomeomorph` of a map that is
  analytic at the base point is analytic at the image point. Route: `AnalyticAt` gives a power series
  `p`; its linear term is the strict derivative (uniqueness of the Fréchet derivative), so
  mathlib's `OpenPartialHomeomorph.hasFPowerSeriesAt_symm` applies.
* `exp_map_bilinear`: for a continuous bilinear product `m` on a real Banach space and a
  continuous linear `D` obeying the Leibniz law for `m`, `exp D` preserves `m`. Route (adapted from
  the pinned compact library's `Glennie.Compact.Flows.flowC_prodC`, attribution in the proof
  file): the curve `s ↦ exp(-sD) (m (exp(sD) a) (exp(sD) b))` has zero derivative.
* `exp_mul_exp_neg`, `exp_neg_mul_exp`: `exp D` is invertible with inverse `exp (-D)`.
-/

noncomputable section

namespace CKM.NativeGroupSlice

open scoped Topology

section IFT

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Analytic inverse function theorem.** The local inverse of an analytic map with invertible
strict derivative is analytic at the image of the base point. -/
theorem analyticAt_toOpenPartialHomeomorph_symm {f : E → F} {e : E ≃L[ℝ] F} {a : E}
    (hf : HasStrictFDerivAt f (e : E →L[ℝ] F) a) (ha : AnalyticAt ℝ f a) :
    AnalyticAt ℝ (hf.toOpenPartialHomeomorph f).symm (f a) := by
  obtain ⟨p, hp⟩ := ha
  have heq : continuousMultilinearCurryFin1 ℝ E F (p 1) = (e : E →L[ℝ] F) :=
    hp.hasFDerivAt.unique hf.hasFDerivAt
  have hp1 : p 1 = (continuousMultilinearCurryFin1 ℝ E F).symm e := by
    rw [← heq, LinearIsometryEquiv.symm_apply_apply]
  exact ((hf.toOpenPartialHomeomorph f).hasFPowerSeriesAt_symm
    hf.mem_toOpenPartialHomeomorph_source hp hp1).analyticAt

end IFT

section Exp

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The Leibniz law of a continuous linear map for a continuous bilinear product. -/
def IsDerivationOf (m : V →L[ℝ] V →L[ℝ] V) (D : V →L[ℝ] V) : Prop :=
  ∀ a b, D (m a b) = m (D a) b + m a (D b)

-- Adapted from https://github.com/macgregor-sudo/compact-albert-recognition, commit
-- 40d3b344180d9ddb78aaa2876873377c1e631515, file Glennie/Compact/Flows.lean, lines 118–123
-- (`hasDerivAt_flowC_apply`), project compact-albert-recognition (maintainer Robert MacGregor,
-- AI-generated development, per its THIRD-PARTY-NOTICES.md), SPDX-License-Identifier: Apache-2.0.
-- Modified: generalized from the coordinate space `Fin 27 → ℝ` and `toCoord D` to an arbitrary
-- real Banach space `V` and `D : V →L[ℝ] V`.
-- We thank the authors and contributors of compact-albert-recognition for these reusable proofs.
-- “If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
/-- Derivative of the curve `s ↦ exp(s • D) c`. -/
private theorem analytic_hasDerivAt_exp_smul_apply (D : V →L[ℝ] V) (c : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • D) c) (D (NormedSpace.exp (t • D) c)) t := by
  have h : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • D) c)
      ((D * NormedSpace.exp (t • D)) c + NormedSpace.exp (t • D) 0) t :=
    (hasDerivAt_exp_smul_const' D t).clm_apply (hasDerivAt_const t c)
  refine h.congr_deriv ?_
  rw [mul_apply_eq_comp, map_zero, add_zero]

-- Adapted from https://github.com/macgregor-sudo/compact-albert-recognition, commit
-- 40d3b344180d9ddb78aaa2876873377c1e631515, file Glennie/Compact/Flows.lean, lines 90–97
-- (`flowC_mul_flowInvC`), project compact-albert-recognition (maintainer Robert MacGregor,
-- AI-generated development, per its THIRD-PARTY-NOTICES.md), SPDX-License-Identifier: Apache-2.0.
-- Modified: generalized from the coordinate space `Fin 27 → ℝ` and `toCoord D` to an arbitrary
-- real Banach space `V` and `D : V →L[ℝ] V`.
-- We thank the authors and contributors of compact-albert-recognition for these reusable proofs.
-- “If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
/-- `exp (t • D) * exp (t • -D) = 1`. -/
private theorem analytic_exp_smul_mul_exp_smul_neg (D : V →L[ℝ] V) (t : ℝ) :
    NormedSpace.exp (t • D) * NormedSpace.exp (t • -D) = 1 := by
  let +nondep : NormedAlgebra ℚ (V →L[ℝ] V) := .restrictScalars ℚ ℝ _
  have h : Commute (t • D) (t • -D) :=
    (((Commute.refl D).neg_right).smul_left t).smul_right t
  rw [← NormedSpace.exp_add_of_commute h, ← smul_add, add_neg_cancel, smul_zero,
    NormedSpace.exp_zero]

/-- The exponential of a derivation preserves the product. -/
theorem exp_map_bilinear (m : V →L[ℝ] V →L[ℝ] V) {D : V →L[ℝ] V} (hD : IsDerivationOf m D)
    (a b : V) :
    NormedSpace.exp D (m a b) = m (NormedSpace.exp D a) (NormedSpace.exp D b) := by
  -- Adapted from https://github.com/macgregor-sudo/compact-albert-recognition, commit
  -- 40d3b344180d9ddb78aaa2876873377c1e631515, file Glennie/Compact/Flows.lean, lines 131–160
  -- (`flowC_prodC`; its use of `hasDerivAt_flowInvC`, lines 125–127, is inlined here as
  -- `hasDerivAt_exp_smul_const`), project compact-albert-recognition
  -- (maintainer Robert MacGregor, AI-generated development, per its THIRD-PARTY-NOTICES.md),
  -- SPDX-License-Identifier: Apache-2.0.
  -- Modified: generalized from the native product `prodC` on `Fin 27 → ℝ` and a transported
  -- Jordan derivation to an arbitrary continuous bilinear `m` on a real Banach space `V` and a
  -- continuous linear `D` with `IsDerivationOf m D`; specialized to time `t = 1`.
  -- We thank the authors and contributors of compact-albert-recognition for these reusable proofs.
  -- “If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
  have hderiv : ∀ s : ℝ, HasDerivAt
      (fun r : ℝ => NormedSpace.exp (r • -D)
        (m (NormedSpace.exp (r • D) a) (NormedSpace.exp (r • D) b))) 0 s := by
    intro s
    have hu := analytic_hasDerivAt_exp_smul_apply D a s
    have hv := analytic_hasDerivAt_exp_smul_apply D b s
    have hpu : HasDerivAt (fun r : ℝ => m (NormedSpace.exp (r • D) a))
        (m (D (NormedSpace.exp (s • D) a))) s :=
      m.hasFDerivAt.comp_hasDerivAt s hu
    have hw : HasDerivAt (fun r : ℝ => m (NormedSpace.exp (r • D) a) (NormedSpace.exp (r • D) b))
        (m (D (NormedSpace.exp (s • D) a)) (NormedSpace.exp (s • D) b) +
          m (NormedSpace.exp (s • D) a) (D (NormedSpace.exp (s • D) b))) s :=
      hpu.clm_apply hv
    have hall : HasDerivAt (fun r : ℝ => NormedSpace.exp (r • -D)
        (m (NormedSpace.exp (r • D) a) (NormedSpace.exp (r • D) b)))
        ((NormedSpace.exp (s • -D) * -D)
            (m (NormedSpace.exp (s • D) a) (NormedSpace.exp (s • D) b)) +
          NormedSpace.exp (s • -D)
            (m (D (NormedSpace.exp (s • D) a)) (NormedSpace.exp (s • D) b) +
              m (NormedSpace.exp (s • D) a) (D (NormedSpace.exp (s • D) b)))) s :=
      (hasDerivAt_exp_smul_const (-D) s).clm_apply hw
    refine hall.congr_deriv ?_
    rw [mul_apply_eq_comp, neg_apply, ← map_add, ← hD,
      neg_add_cancel, map_zero]
  have hconst := is_const_of_deriv_eq_zero
    (fun s => (hderiv s).differentiableAt) (fun s => (hderiv s).deriv) 1 0
  simp only [zero_smul, NormedSpace.exp_zero, one_apply_eq_self,
    one_smul] at hconst
  have h2 := congrArg (fun v : V => NormedSpace.exp D v) hconst
  have hinv := congrArg (fun T : V →L[ℝ] V => T (m (NormedSpace.exp D a) (NormedSpace.exp D b)))
    (analytic_exp_smul_mul_exp_smul_neg D 1)
  simp only [one_smul, mul_apply_eq_comp, one_apply_eq_self] at hinv
  rw [hinv] at h2
  exact h2.symm

theorem exp_mul_exp_neg (D : V →L[ℝ] V) : NormedSpace.exp D * NormedSpace.exp (-D) = 1 := by
  simpa only [one_smul] using analytic_exp_smul_mul_exp_smul_neg D 1

theorem exp_neg_mul_exp (D : V →L[ℝ] V) : NormedSpace.exp (-D) * NormedSpace.exp D = 1 := by
  simpa only [neg_neg] using exp_mul_exp_neg (-D)

end Exp

end CKM.NativeGroupSlice

#print axioms CKM.NativeGroupSlice.analyticAt_toOpenPartialHomeomorph_symm
#print axioms CKM.NativeGroupSlice.exp_map_bilinear
#print axioms CKM.NativeGroupSlice.exp_mul_exp_neg
#print axioms CKM.NativeGroupSlice.exp_neg_mul_exp
