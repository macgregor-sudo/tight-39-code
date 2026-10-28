module

public import OriginalFAnchorSupportV3
public import Mathlib.Algebra.MvPolynomial.Supported

@[expose] public section

/-!
Structural support for the literal original F equations. The row-incidence
premise below refers to the actual point/frame/pair labels and all 1053 ambient
variables. It is not a statement that any supplied H covector has been decoded
or checked. No base annihilation, solutionhood or coefficient cancellation is
needed for these support conclusions.

This first-party composition imports, rather than copies, Mathlib's polynomial
subalgebra API (leanprover-community/mathlib4, commit
065356127b1dc0016f66b7283ce0ce2c4055aa55, Apache-2.0). Thanks to its contributors.
"If I have seen further it is by standing on the sholders of Giants."
— Isaac Newton, letter to Robert Hooke, 1676.
https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section

namespace Option2.NativeStress.AnchorRowSupport

open scoped BigOperators
open MvPolynomial PolynomialJets
open NativePolynomial.CoordinateMaps NativePolynomial.ConfigurationResiduals
open ConfigurationResidualIndices AnchorSupport

/-- The actual four anchor-frame sets, including their common frame zero. -/
def AnchorFrame (i : Fin 4) (f : Fin 13) : Prop :=
  f.val = 0 ∨ (1 + 3 * i.val ≤ f.val ∧ f.val ≤ 3 + 3 * i.val)

/-- A labelled point belongs to its frame, with all three outcomes retained. -/
def AnchorPoint (i : Fin 4) (p : Fin 39) : Prop :=
  p.val / 3 = 0 ∨ (1 + 3 * i.val ≤ p.val / 3 ∧ p.val / 3 ≤ 3 + 3 * i.val)

/-- Incidence of the original typed residual, not support of a derived quadric. -/
def LabelUsesAnchor (i : Fin 4) : FLabel → Prop
  | .inl (p, _) => AnchorPoint i p
  | .inr (.inl p) => AnchorPoint i p
  | .inr (.inr (.inl (f, _))) => AnchorFrame i f
  | .inr (.inr (.inr pq)) => AnchorPoint i pq.val.1 ∧ AnchorPoint i pq.val.2

/-- Numbered rows use only the existing canonical inverse equivalence. -/
def RowUsesAnchor (i : Fin 4) (r : Fin 2184) : Prop :=
  LabelUsesAnchor i (fNumber.symm r)

/-- This is the remaining row-incidence premise for a concrete covector. -/
def WeightsUseAnchor (ell : Weights) (i : Fin 4) : Prop :=
  ∀ r : Fin 2184, ell r ≠ 0 → RowUsesAnchor i r

theorem rowUsesAnchor_number (i : Fin 4) (q : FLabel) :
    RowUsesAnchor i (fNumber q) ↔ LabelUsesAnchor i q := by
  simp only [RowUsesAnchor, fNumber.symm_apply_apply]

private def anchorAlgebra (i : Fin 4) : Subalgebra ℂ Poly :=
  supported ℂ {v | AnchorCoordinate i v}

private theorem constant_mem (i : Fin 4) (c : ℂ) : C c ∈ anchorAlgebra i :=
  (anchorAlgebra i).algebraMap_mem c

private theorem point_mem (i : Fin 4) (p : Fin 39) (hp : AnchorPoint i p)
    (k : Fin 27) : point p k ∈ anchorAlgebra i := by
  apply X_mem_supported.mpr
  change AnchorCoordinate i (variableIndex p k)
  have hindex : (27 * p.val + k.val) / 81 = p.val / 3 := by omega
  simpa only [AnchorCoordinate, AnchorPoint, variableIndex_val, hindex] using hp

private theorem framePoint_anchor (i : Fin 4) (f : Fin 13)
    (hf : AnchorFrame i f) (a : Fin 3) : AnchorPoint i (framePointIndex f a) := by
  have hindex : (3 * f.val + a.val) / 3 = f.val := by omega
  simpa only [AnchorPoint, AnchorFrame, framePointIndex_val, hindex] using hf

private theorem product_mem (i : Fin 4) (p : Fin 39) (hp : AnchorPoint i p)
    (k : Fin 27) : coordinateProduct (C (1 / 2 : ℂ)) (point p) (point p) k ∈
      anchorAlgebra i := by
  rw [coordinateProduct_apply]
  apply (anchorAlgebra i).sum_mem
  intro a _
  apply (anchorAlgebra i).sum_mem
  intro b _
  apply (anchorAlgebra i).mul_mem
  · exact (anchorAlgebra i).mul_mem (point_mem i p hp a) (point_mem i p hp b)
  · exact (anchorAlgebra i).mul_mem (constant_mem i (1 / 2))
      ((anchorAlgebra i).intCast_mem _)

private theorem residual_mem (i : Fin 4) (q : FLabel) (hq : LabelUsesAnchor i q) :
    fResidual (1 / 2 : ℂ) (1 / 3 : ℂ) q ∈ anchorAlgebra i := by
  rcases q with ⟨p, k⟩ | p | ⟨f, k⟩ | pq
  · change coordinateProduct (C (1 / 2 : ℂ)) (point p) (point p) k - point p k ∈ _
    exact (anchorAlgebra i).sub_mem (product_mem i p hq k) (point_mem i p hq k)
  · change coordinateTrace (point p) - 1 ∈ _
    rw [coordinateTrace_apply]
    exact (anchorAlgebra i).sub_mem
      ((anchorAlgebra i).add_mem
        ((anchorAlgebra i).add_mem (point_mem i p hq 0) (point_mem i p hq 1))
        (point_mem i p hq 2)) (anchorAlgebra i).one_mem
  · change (∑ a : Fin 3, point (framePointIndex f a) k) - coordinateUnit k ∈ _
    apply (anchorAlgebra i).sub_mem
    · exact (anchorAlgebra i).sum_mem fun a _ =>
        point_mem i _ (framePoint_anchor i f hq a) k
    · unfold coordinateUnit
      split_ifs <;> first | exact (anchorAlgebra i).one_mem | exact (anchorAlgebra i).zero_mem
  · change coordinatePairing (point pq.val.1) (point pq.val.2) -
        (if pq.val.1.val / 3 = pq.val.2.val / 3 then 0 else C (1 / 3 : ℂ)) ∈ _
    apply (anchorAlgebra i).sub_mem
    · unfold coordinatePairing
      apply (anchorAlgebra i).sum_mem
      intro k _
      exact (anchorAlgebra i).mul_mem
        ((anchorAlgebra i).mul_mem ((anchorAlgebra i).intCast_mem _)
          (point_mem i _ hq.1 k)) (point_mem i _ hq.2 k)
    · split_ifs
      · exact (anchorAlgebra i).zero_mem
      · exact constant_mem i (1 / 3)

/-- The literal half/third F row has no variable outside its incident anchor. -/
theorem row_vars (i : Fin 4) (r : Fin 2184) (hr : RowUsesAnchor i r) :
    ∀ v ∈ (row r).vars, AnchorCoordinate i v := by
  have hmem : row r ∈ anchorAlgebra i := residual_mem i (fNumber.symm r) hr
  exact mem_supported.mp hmem

private theorem translate_mem (i : Fin 4) (P : Ambient) (p : Poly)
    (hp : p ∈ anchorAlgebra i) : translate P p ∈ anchorAlgebra i := by
  let T : Poly →+* Poly := eval₂Hom C (fun v => X v + C (P v))
  change T p ∈ anchorAlgebra i
  change p ∈ Algebra.adjoin ℂ (X '' {v | AnchorCoordinate i v}) at hp
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      change (eval₂Hom C (fun v => X v + C (P v))) (X v) ∈ _
      rw [eval₂Hom_X']
      exact (anchorAlgebra i).add_mem (X_mem_supported.mpr hv) (constant_mem i (P v))
  | algebraMap c =>
      change (eval₂Hom C (fun v => X v + C (P v))) (C c) ∈ _
      rw [eval₂Hom_C]
      exact constant_mem i c
  | add x y _ _ hx hy =>
      rw [map_add]
      exact (anchorAlgebra i).add_mem hx hy
  | mul x y _ _ hx hy =>
      rw [map_mul]
      exact (anchorAlgebra i).mul_mem hx hy

/-- Translation at any ambient base preserves the same literal variable support. -/
theorem translatedRow_vars (i : Fin 4) (P : Ambient) (r : Fin 2184)
    (hr : RowUsesAnchor i r) :
    ∀ v ∈ (translatedRow P r).vars, AnchorCoordinate i v := by
  exact mem_supported.mp (translate_mem i P (row r) (mem_supported.mpr (row_vars i r hr)))

private theorem homogeneous_mem (i : Fin 4) (n : ℕ) (p : Poly)
    (hp : p ∈ anchorAlgebra i) : homogeneousComponent n p ∈ anchorAlgebra i := by
  apply mem_supported.mpr
  intro v hv
  obtain ⟨d, hd, hvd⟩ := (mem_vars_iff_mem_support v).mp hv
  rw [support_homogeneousComponent] at hd
  exact mem_supported.mp hp ((mem_vars_iff_mem_support v).mpr
    ⟨d, (Finset.mem_filter.mp hd).1, hvd⟩)

/-- Arbitrary weighted contraction stays in the anchor subalgebra, at any base.
The only condition on the weights is the explicit original-row incidence. -/
theorem contractedPolynomial_vars (P : Ambient) (ell : Weights) (i : Fin 4)
    (hell : WeightsUseAnchor ell i) :
    ∀ v ∈ (contractedPolynomial P ell).vars, AnchorCoordinate i v := by
  apply mem_supported.mp
  change (∑ r, ell r • translatedRow P r) ∈ anchorAlgebra i
  apply (anchorAlgebra i).sum_mem
  intro r _
  by_cases hr : ell r = 0
  · rw [hr, zero_smul]
    exact (anchorAlgebra i).zero_mem
  · exact (anchorAlgebra i).smul_mem
      (mem_supported.mpr (translatedRow_vars i P r (hell r hr))) (ell r)

/-- The existing AMBIENT quadratic-support premise is derived, not assumed. -/
theorem hasAnchorSupport (P : Ambient) (ell : Weights) (i : Fin 4)
    (hell : WeightsUseAnchor ell i) : HasAnchorSupport P ell i := by
  apply mem_supported.mp
  change (∑ r, ell r • homogeneousComponent 2 (translatedRow P r)) ∈ anchorAlgebra i
  apply (anchorAlgebra i).sum_mem
  intro r _
  by_cases hr : ell r = 0
  · rw [hr, zero_smul]
    exact (anchorAlgebra i).zero_mem
  · exact (anchorAlgebra i).smul_mem
      (homogeneous_mem i 2 _
        (mem_supported.mpr (translatedRow_vars i P r (hell r hr)))) (ell r)

private theorem finite_off_support_column {ι : Type*} [Fintype ι]
    (g : ι → Poly) (ell : ι → ℂ) (q : Poly) (heq : (∑ r, ell r • g r) = q)
    (v : Fin 1053) (hv : v ∉ q.vars) :
    ∑ r, ell r * equationLinearMatrix g r v = 0 := by
  classical
  have hc : q.coeff (Finsupp.single v 1) = 0 := by
    by_contra hn
    have hvars : v ∈ q.vars :=
      (mem_vars_iff_mem_support v).mpr
        ⟨Finsupp.single v 1, mem_support_iff.mpr hn, by simp⟩
    exact hv hvars
  have hcoeff := congrArg (fun p : Poly => p.coeff (Finsupp.single v 1)) heq
  rw [hc] at hcoeff
  simpa only [coeff_sum, coeff_smul, smul_eq_mul, equationLinearMatrix] using hcoeff

/-- Every original linear column outside the anchor vanishes termwise in support.
No annihilation on the anchor, solution premise or derivative replacement is used. -/
theorem off_anchor_column (P : Ambient) (ell : Weights) (i : Fin 4)
    (hell : WeightsUseAnchor ell i) (v : Fin 1053) (hv : ¬ AnchorCoordinate i v) :
    ∑ r : Fin 2184, ell r * equationLinearMatrix (translatedRow P) r v = 0 := by
  have hs := contractedPolynomial_vars P ell i hell
  generalize hq : contractedPolynomial P ell = q at hs
  apply finite_off_support_column (translatedRow P) ell q hq v
  intro hvars
  exact hv (hs v hvars)

/-- Only the actual anchor columns remain to establish full base annihilation. -/
theorem all_columns_of_anchor_columns (P : Ambient) (ell : Weights) (i : Fin 4)
    (hell : WeightsUseAnchor ell i)
    (hanchor : ∀ v : Fin 1053, AnchorCoordinate i v →
      ∑ r : Fin 2184, ell r * equationLinearMatrix (translatedRow P) r v = 0) :
    ∀ v : Fin 1053,
      ∑ r : Fin 2184, ell r * equationLinearMatrix (translatedRow P) r v = 0 := by
  intro v
  by_cases hv : AnchorCoordinate i v
  · exact hanchor v hv
  · exact off_anchor_column P ell i hell v hv

end Option2.NativeStress.AnchorRowSupport
