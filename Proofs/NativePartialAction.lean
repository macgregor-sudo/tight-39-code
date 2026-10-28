module

public import NativeConfigurationPolynomialResiduals

@[expose] public section
set_option backward.proofsInPublic true

/-!
# Partial actions preserve every original configuration row

The component predicate below has exactly the four branches of the original F
family. In particular its pair condition is scalar, including pairs within a
frame. No within-frame Jordan-product condition is added. The evaluation theorem
binds this predicate to every original numbered polynomial, without using G.

An isometric linear partial action fixes an anchor submodule and agrees with a
genuine product automorphism on its orthogonal complement. A configuration point
in the anchor submodule is fixed; one in the complementary affine slice is sent
to its image under that automorphism. This proves idempotency point by point.
Linearity, the fixed unit and isometry preserve all remaining rows.

This first-party proof uses elementary linear algebra and ring-homomorphism laws;
no upstream implementation is copied. Mathlib APIs are imported at the existing
pin 065356127b1dc0016f66b7283ce0ce2c4055aa55. The unchanged native integer tensor
and its provenance are imported through NativeConfigurationPolynomialResiduals.
No new Albert carrier, dimension, exhaustion or canonical subgroup is asserted.
Thanks to the native-model, Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section

namespace NativePolynomial.PartialAction

open scoped BigOperators
open CoordinateMaps ConfigurationResiduals ConfigurationResidualIndices

variable {S : Type*} [CommRing S]

abbrev NativeVector (S : Type*) := Fin 27 → S
abbrev Configuration (S : Type*) := Fin 39 → NativeVector S

/-- The point-first values in the literal 1053-variable polynomial ring. -/
def pack (C : Configuration S) (v : Fin 1053) : S :=
  C ⟨v.val / 27, by omega⟩ ⟨v.val % 27, by omega⟩

theorem pack_variableIndex (C : Configuration S) (i : Fin 39) (k : Fin 27) :
    pack C (variableIndex i k) = C i k := by
  unfold pack
  have hdiv : (variableIndex i k).val / 27 = i.val := by
    rw [variableIndex_val]
    omega
  have hmod : (variableIndex i k).val % 27 = k.val := by
    rw [variableIndex_val]
    omega
  have hi : (⟨(variableIndex i k).val / 27, by omega⟩ : Fin 39) = i := Fin.ext hdiv
  have hk : (⟨(variableIndex i k).val % 27, by omega⟩ : Fin 27) = k := Fin.ext hmod
  rw [hi, hk]

/-- Exactly the original F equations, retaining every scalar pair. -/
structure OriginalEquations (h t : S) (C : Configuration S) : Prop where
  idempotent : ∀ i, coordinateProduct h (C i) (C i) = C i
  trace_one : ∀ i, coordinateTrace (C i) = 1
  frame_sum : ∀ f : Fin 13, ∑ a : Fin 3, C (framePointIndex f a) = coordinateUnit
  pair : ∀ ij : Pair 39,
    coordinatePairing (C ij.val.1) (C ij.val.2) =
      if ij.val.1.val / 3 = ij.val.2.val / 3 then 0 else t

/-- Evaluation of the four typed original residual branches. -/
def originalValue (h t : S) (C : Configuration S) : FLabel → S
  | .inl (i, k) => coordinateProduct h (C i) (C i) k - C i k
  | .inr (.inl i) => coordinateTrace (C i) - 1
  | .inr (.inr (.inl (f, k))) =>
      (∑ a : Fin 3, C (framePointIndex f a) k) - coordinateUnit k
  | .inr (.inr (.inr ij)) =>
      coordinatePairing (C ij.val.1) (C ij.val.2) -
        (if ij.val.1.val / 3 = ij.val.2.val / 3 then 0 else t)

private theorem eval_product (p : Fin 1053 → S) (h : S)
    (x y : Fin 27 → MvPolynomial (Fin 1053) S) (k : Fin 27) :
    MvPolynomial.eval p (coordinateProduct (MvPolynomial.C h) x y k) =
      coordinateProduct h (fun i => MvPolynomial.eval p (x i))
        (fun j => MvPolynomial.eval p (y j)) k := by
  simp only [coordinateProduct_apply, map_sum, map_mul, MvPolynomial.eval_C,
    map_intCast]

private theorem eval_pairing (p : Fin 1053 → S)
    (x y : Fin 27 → MvPolynomial (Fin 1053) S) :
    MvPolynomial.eval p (coordinatePairing x y) =
      coordinatePairing (fun i => MvPolynomial.eval p (x i))
        (fun j => MvPolynomial.eval p (y j)) := by
  simp only [coordinatePairing, map_sum, map_mul, map_intCast]

private theorem eval_unit (p : Fin 1053 → S) (k : Fin 27) :
    MvPolynomial.eval p (coordinateUnit k) = (coordinateUnit (P := S) k) := by
  unfold coordinateUnit
  split_ifs <;> simp only [map_one, map_zero]

private theorem eval_point (C : Configuration S) (i : Fin 39) (k : Fin 27) :
    MvPolynomial.eval (pack C) (point i k) = C i k := by
  simp only [point, MvPolynomial.eval_X, pack_variableIndex]

/-- All four original typed branches evaluate to their literal component formulas. -/
theorem eval_fResidual (h t : S) (C : Configuration S) (q : FLabel) :
    MvPolynomial.eval (pack C) (fResidual h t q) = originalValue h t C q := by
  rcases q with ⟨i, k⟩ | i | ⟨f, k⟩ | ij
  · simp only [fResidual, FrameResiduals.idempotencyResidual, Pi.sub_apply,
      map_sub, eval_product, eval_point, originalValue]
  · simp only [fResidual, coordinateTrace_apply, map_sub, map_add, map_one,
      eval_point, originalValue]
  · simp only [fResidual, map_sub, map_sum, eval_point, eval_unit, originalValue]
  · simp only [fResidual, map_sub, eval_pairing, eval_point, originalValue]
    split_ifs <;> simp only [MvPolynomial.eval_C, map_zero]

/-- The sole canonical numbering covers every original row. -/
theorem eval_fRow (h t : S) (C : Configuration S) (r : Fin 2184) :
    MvPolynomial.eval (pack C) (ConfigurationResiduals.fRow h t r) =
      originalValue h t C (fNumber.symm r) :=
  eval_fResidual h t C (fNumber.symm r)

theorem originalEquations_iff_values_zero (h t : S) (C : Configuration S) :
    OriginalEquations h t C ↔ ∀ q : FLabel, originalValue h t C q = 0 := by
  constructor
  · intro hC q
    rcases q with ⟨i, k⟩ | i | ⟨f, k⟩ | ij
    · exact sub_eq_zero.mpr (congrFun (hC.idempotent i) k)
    · exact sub_eq_zero.mpr (hC.trace_one i)
    · apply sub_eq_zero.mpr
      simpa only [Finset.sum_apply] using congrFun (hC.frame_sum f) k
    · exact sub_eq_zero.mpr (hC.pair ij)
  · intro hC
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      funext k
      exact sub_eq_zero.mp (hC (fId i k))
    · intro i
      exact sub_eq_zero.mp (hC (fTrace i))
    · intro f
      funext k
      simpa only [Finset.sum_apply] using sub_eq_zero.mp (hC (fSum f k))
    · intro ij
      exact sub_eq_zero.mp (hC (fPair ij))

/-- Faithful equivalence to all 2184 original polynomial equations. -/
theorem originalEquations_iff_all_fRows (h t : S) (C : Configuration S) :
    OriginalEquations h t C ↔
      ∀ r : Fin 2184,
        MvPolynomial.eval (pack C) (ConfigurationResiduals.fRow h t r) = 0 := by
  rw [originalEquations_iff_values_zero]
  constructor
  · intro hC r
    rw [eval_fRow]
    exact hC _
  · intro hC q
    have hq := hC (fNumber q)
    rw [eval_fRow, fNumber.symm_apply_apply] at hq
    exact hq

/-- Pairing with the unit is exactly the original coordinate trace. -/
theorem pairing_unit (x : NativeVector S) :
    coordinatePairing x coordinateUnit = coordinateTrace x := by
  simp [coordinatePairing, coordinateUnit, coordinateTrace_apply,
    IntegralStructureConstants.coordinateTraceWeight, Fin.sum_univ_succ, add_assoc]

/-- Isometry and a fixed unit preserve trace; no product law for T is used. -/
theorem trace_of_isometry (T : NativeVector S →ₗ[S] NativeVector S)
    (hUnit : T coordinateUnit = coordinateUnit)
    (hPair : ∀ x y, coordinatePairing (T x) (T y) = coordinatePairing x y)
    (x : NativeVector S) : coordinateTrace (T x) = coordinateTrace x := by
  rw [← pairing_unit, ← hUnit, hPair, pairing_unit]

/-- Orthogonality for the native weighted trace pairing. -/
def OrthogonalTo (A : Submodule S (NativeVector S)) (z : NativeVector S) : Prop :=
  ∀ a ∈ A, coordinatePairing z a = 0

/-- The partial action agrees with g on the complementary affine slice. -/
theorem affine_slice_agreement (A : Submodule S (NativeVector S))
    (g : NativeVector S ≃ₗ[S] NativeVector S)
    (T : NativeVector S →ₗ[S] NativeVector S) (c : S)
    (hUnitA : coordinateUnit ∈ A)
    (hFix : ∀ a ∈ A, T a = a)
    (hAgree : ∀ z, OrthogonalTo A z → T z = g z)
    (hgUnit : g coordinateUnit = coordinateUnit)
    (z : NativeVector S) (hz : OrthogonalTo A z) :
    T (c • coordinateUnit + z) = g (c • coordinateUnit + z) := by
  rw [map_add, map_smul, hFix _ hUnitA, hAgree z hz,
    map_add, map_smul, hgUnit]

/-- Preservation of the exact component equations by a genuine partial action.
The product law belongs to g alone. The scalar c is arbitrary; the native real
application specializes it to 1/3. No anchor count or dimension is assumed. -/
theorem OriginalEquations.partial_action {h t : S} {C : Configuration S}
    (hC : OriginalEquations h t C)
    (A : Submodule S (NativeVector S))
    (g : NativeVector S ≃ₗ[S] NativeVector S)
    (T : NativeVector S →ₗ[S] NativeVector S) (c : S)
    (hUnitA : coordinateUnit ∈ A)
    (hFix : ∀ a ∈ A, T a = a)
    (hAgree : ∀ z, OrthogonalTo A z → T z = g z)
    (hgUnit : g coordinateUnit = coordinateUnit)
    (hgProduct : ∀ x y, g (coordinateProduct h x y) = coordinateProduct h (g x) (g y))
    (hPair : ∀ x y, coordinatePairing (T x) (T y) = coordinatePairing x y)
    (hPosition : ∀ i, C i ∈ A ∨
      ∃ z, OrthogonalTo A z ∧ C i = c • coordinateUnit + z) :
    OriginalEquations h t (fun i => T (C i)) := by
  have hUnit : T coordinateUnit = coordinateUnit := hFix _ hUnitA
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    rcases hPosition i with hi | ⟨z, hz, hi⟩
    · rw [hFix _ hi]
      exact hC.idempotent i
    · have hAt : T (C i) = g (C i) := by
        rw [hi]
        exact affine_slice_agreement A g T c hUnitA hFix hAgree hgUnit z hz
      rw [hAt, ← hgProduct, hC.idempotent]
  · intro i
    rw [trace_of_isometry T hUnit hPair, hC.trace_one]
  · intro f
    rw [← map_sum, hC.frame_sum, hUnit]
  · intro ij
    rw [hPair, hC.pair]

/-- A reusable end-to-end endpoint against every literal original F row. -/
theorem all_fRows_partial_action {h t : S} {C : Configuration S}
    (hC : ∀ r : Fin 2184,
      MvPolynomial.eval (pack C) (ConfigurationResiduals.fRow h t r) = 0)
    (A : Submodule S (NativeVector S))
    (g : NativeVector S ≃ₗ[S] NativeVector S)
    (T : NativeVector S →ₗ[S] NativeVector S) (c : S)
    (hUnitA : coordinateUnit ∈ A)
    (hFix : ∀ a ∈ A, T a = a)
    (hAgree : ∀ z, OrthogonalTo A z → T z = g z)
    (hgUnit : g coordinateUnit = coordinateUnit)
    (hgProduct : ∀ x y, g (coordinateProduct h x y) = coordinateProduct h (g x) (g y))
    (hPair : ∀ x y, coordinatePairing (T x) (T y) = coordinatePairing x y)
    (hPosition : ∀ i, C i ∈ A ∨
      ∃ z, OrthogonalTo A z ∧ C i = c • coordinateUnit + z) :
    ∀ r : Fin 2184,
      MvPolynomial.eval (pack (fun i => T (C i)))
        (ConfigurationResiduals.fRow h t r) = 0 := by
  apply (originalEquations_iff_all_fRows h t _).mp
  exact ((originalEquations_iff_all_fRows h t C).mpr hC).partial_action
    A g T c hUnitA hFix hAgree hgUnit hgProduct hPair hPosition

end NativePolynomial.PartialAction
