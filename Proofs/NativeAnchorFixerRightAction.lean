module

public import NativeTracePreservation
public import NativeActualAnchorComplement
public import NativeHermitianLeftRealization
public import NativeAnchorHermitianCommutant

@[expose] public section

/-!
Actual native first-twelve-anchor fixers act by right multiplication on the
hidden matrix sector. Trace, complement preservation, visible-input fixing and
Hermitian-left commutation are derived, not public premises.
The trace, mixed-product, complement and commutant identities supply the action formula.
This endpoint does not assert unitarity, determinant or full gauge topology.
First-party composition of these exact native owners and pinned Mathlib APIs.
Thanks to their contributors. “If I have seen further it is by standing on the
sholders of Giants.” — Isaac Newton, 1676.
https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section
namespace CompactAlbert
open ActualQuartetStates
open QuadraticCertificate.ExactCKMConfiguration

private theorem inner_sub_left (x y z : Glennie.Albert) :
    Glennie.inner (x - y) z = Glennie.inner x z - Glennie.inner y z := by
  change Glennie.trace (Glennie.jordanLinear (x - y) z) = _
  rw [map_sub, LinearMap.sub_apply, Glennie.trace_sub]
  rfl

private theorem inner_sub_right (x y z : Glennie.Albert) :
    Glennie.inner x (y - z) = Glennie.inner x y - Glennie.inner x z := by
  rw [Glennie.inner_comm, inner_sub_left, Glennie.inner_comm y x, Glennie.inner_comm z x]

/-- Actual anchor fixing determines every zero-hidden native input, using
native positive definiteness rather than an assumed visible-span bridge. -/
private theorem fixes_visible_input
    (f : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert)
    (hprod : ∀ x y, f (Glennie.jordan x y) = Glennie.jordan (f x) (f y))
    (hfix : ∀ i : Fin 39, i.val < 12 → f (nativePoint i) = nativePoint i)
    (x : Glennie.Albert) (hx : (toTitsCoordinates x).2.2 = 0) : f x = x := by
  have hpair := Glennie.trace_pairing_preserved_of_jordan_equiv f hprod
  have hdvisible : hermitianMatrix (toTitsCoordinates (f x - x)) = 0 := by
    apply (actual_anchor_orthogonal_iff_visible_zero _).mp
    intro i hi
    change Glennie.inner (f x - x) (nativePoint i) = 0
    rw [inner_sub_left]
    have hp := hpair x (nativePoint i)
    rw [hfix i hi] at hp
    exact sub_eq_zero.mpr hp
  have hcross : Glennie.inner (f x - x) x = 0 := by
    change Glennie.trace (Glennie.jordan (f x - x) x) = 0
    rw [native_trace_jordan_eq_visible_pairing_of_hidden_eq_zero _ _ hx, hdvisible]
    simp
  have hnorm : Glennie.inner (f x - x) (f x - x) = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, Glennie.inner_comm x (f x)]
    change Glennie.inner (f x) (f x) - Glennie.inner (f x) x -
      (Glennie.inner (f x) x - Glennie.inner x x) = 0
    have hn : Glennie.inner (f x) (f x) = Glennie.inner x x := hpair x x
    rw [inner_sub_left] at hcross
    linarith
  exact sub_eq_zero.mp ((Glennie.inner_self_eq_zero _).mp hnorm)

private def hiddenInputLinear : TitsComplexMatrix →ₗ[ℝ] Glennie.Albert where
  toFun := nativeHiddenMatrix
  map_add' B D := by
    apply nativeTitsMatrixPair_injective
    simp [nativeHiddenMatrix_pair]
  map_smul' r B := by
    apply nativeTitsMatrixPair_injective
    simp [nativeHiddenMatrix_pair]

private def inducedHiddenAction (f : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert) :
    TitsComplexMatrix →ₗ[ℝ] TitsComplexMatrix :=
  (LinearMap.snd ℝ TitsComplexMatrix TitsComplexMatrix).comp
    (nativeTitsMatrixPair.comp (f.toLinearMap.comp hiddenInputLinear))

private theorem induced_hidden_pair
    (f : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert)
    (hprod : ∀ x y, f (Glennie.jordan x y) = Glennie.jordan (f x) (f y))
    (hfix : ∀ i : Fin 39, i.val < 12 → f (nativePoint i) = nativePoint i)
    (B : TitsComplexMatrix) :
    nativeTitsMatrixPair (f (nativeHiddenMatrix B)) = (0, inducedHiddenAction f B) := by
  have hz : hermitianMatrix (toTitsCoordinates (nativeHiddenMatrix B)) = 0 :=
    congrArg Prod.fst (nativeHiddenMatrix_pair B)
  have hfz := visible_zero_preserved_of_trace_pairing_and_actual_anchor_fixing
    f.toLinearMap (Glennie.trace_pairing_preserved_of_jordan_equiv f hprod)
    hfix (nativeHiddenMatrix B) hz
  apply Prod.ext
  · exact hfz
  · rfl

private theorem induced_hidden_native
    (f : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert)
    (hprod : ∀ x y, f (Glennie.jordan x y) = Glennie.jordan (f x) (f y))
    (hfix : ∀ i : Fin 39, i.val < 12 → f (nativePoint i) = nativePoint i)
    (B : TitsComplexMatrix) :
    f (nativeHiddenMatrix B) = nativeHiddenMatrix (inducedHiddenAction f B) := by
  apply nativeTitsMatrixPair_injective
  rw [induced_hidden_pair f hprod hfix, nativeHiddenMatrix_pair]

private theorem mixed_native (H B : TitsComplexMatrix) (hH : H.IsHermitian) :
    Glennie.jordan (nativeHermitianLeftInput H hH) (nativeHiddenMatrix B) =
      nativeHiddenMatrix (H * B) := by
  apply nativeTitsMatrixPair_injective
  rw [native_jordan_realizes_hermitian_left, nativeHiddenMatrix_pair]

private theorem induced_hermitian_left_commutation
    (f : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert)
    (hprod : ∀ x y, f (Glennie.jordan x y) = Glennie.jordan (f x) (f y))
    (hfix : ∀ i : Fin 39, i.val < 12 → f (nativePoint i) = nativePoint i)
    (H : TitsComplexMatrix) (hH : H.IsHermitian) (B : TitsComplexMatrix) :
    inducedHiddenAction f (H * B) = H * inducedHiddenAction f B := by
  have hv : f (nativeHermitianLeftInput H hH) = nativeHermitianLeftInput H hH :=
    fixes_visible_input f hprod hfix _ (congrArg Prod.snd (nativeHermitianLeftInput_pair H hH))
  have h := congrArg f (mixed_native H B hH)
  rw [hprod, hv, induced_hidden_native f hprod hfix B,
    induced_hidden_native f hprod hfix (H * B), mixed_native] at h
  have hh := congrArg (fun x => (nativeTitsMatrixPair x).2) h
  simpa only [nativeHiddenMatrix_pair] using hh.symm

/-- An actual native Jordan-product-preserving real-linear bijection fixing
precisely the original first twelve anchors acts on every native hidden input
by right multiplication. The multiplier is its induced hidden action at one.
Unitarity, determinant and gauge topology are not asserted here. -/
theorem native_anchor_fixer_right_action
    (f : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert)
    (hprod : ∀ x y, f (Glennie.jordan x y) = Glennie.jordan (f x) (f y))
    (hfix : ∀ i : Fin 39, i.val < 12 → f (nativePoint i) = nativePoint i) :
    ∃ R : TitsComplexMatrix,
      R = (nativeTitsMatrixPair (f (nativeHiddenMatrix 1))).2 ∧
      ∀ B : TitsComplexMatrix,
        nativeTitsMatrixPair (f (nativeHiddenMatrix B)) = (0, B * R) := by
  refine ⟨inducedHiddenAction f 1, rfl, ?_⟩
  intro B
  rw [induced_hidden_pair f hprod hfix]
  rw [eq_right_mul_of_hermitian_left_commutation (inducedHiddenAction f)
    (induced_hermitian_left_commutation f hprod hfix) B]

end CompactAlbert
