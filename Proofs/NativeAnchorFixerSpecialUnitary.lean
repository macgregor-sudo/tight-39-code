module

public import NativeAnchorFixerRightAction

@[expose] public section

/-!
The multiplier of an actual native first-twelve-anchor fixer is special unitary.
Only real-linear bijectivity, actual Jordan preservation and actual anchor fixing
are premises. The hidden-identity square and accepted adjugate equivalence supply
unitarity and determinant one. No converse or topology conclusion is made here.
First-party proof composition of the exact native owners and pinned Mathlib APIs.
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


private theorem hidden_one_square_pair :
    nativeTitsMatrixPair (Glennie.jordan (nativeHiddenMatrix 1) (nativeHiddenMatrix 1)) =
      ((2 : ℂ) • (1 : TitsComplexMatrix), 1) := by
  rw [native_tits_square_pair, nativeHiddenMatrix_pair]
  apply Prod.ext
  · norm_num [compactSecondTitsSquare, Matrix.trace_one]
    module
  · simp [compactSecondTitsSquare, Matrix.adjugate_one]

private theorem unitary_of_hidden_square_visible (R : TitsComplexMatrix)
    (hvisible : -(R * R.conjTranspose) +
      ((R * R.conjTranspose).trace.re : ℂ) • (1 : TitsComplexMatrix) =
        (2 : ℂ) • (1 : TitsComplexMatrix)) : R * R.conjTranspose = 1 := by
  have htr := congrArg (fun A : TitsComplexMatrix => A.trace.re) hvisible
  norm_num [Matrix.trace_add, Matrix.trace_neg, Matrix.trace_smul,
    Matrix.trace_one, Complex.mul_re] at htr
  have ht : (R * R.conjTranspose).trace.re = 3 := by linarith
  rw [ht] at hvisible
  norm_num at hvisible
  calc
    R * R.conjTranspose = (3 : ℂ) • (1 : TitsComplexMatrix) -
        (2 : ℂ) • (1 : TitsComplexMatrix) := by
      apply eq_sub_iff_add_eq.mpr
      have h := congrArg (fun A : TitsComplexMatrix => R * R.conjTranspose + A) hvisible
      simpa only [← add_assoc, add_neg_cancel, zero_add] using h.symm
    _ = 1 := by rw [← sub_smul]; norm_num

/-- The actual native multiplier at the hidden identity satisfies RR†=I and
det R=1, derived with no unitary, determinant or metric hypothesis. -/
theorem native_anchor_fixer_multiplier_specialUnitary
    (f : Glennie.Albert ≃ₗ[ℝ] Glennie.Albert)
    (hprod : ∀ x y, f (Glennie.jordan x y) = Glennie.jordan (f x) (f y))
    (hfix : ∀ i : Fin 39, i.val < 12 → f (nativePoint i) = nativePoint i) :
    let R := (nativeTitsMatrixPair (f (nativeHiddenMatrix 1))).2
    R * R.conjTranspose = 1 ∧ R.det = 1 := by
  obtain ⟨R, hR, haction⟩ := native_anchor_fixer_right_action f hprod hfix
  let v : Glennie.Albert := includeHermitianMatrix
    ⟨(2 : ℂ) • (1 : TitsComplexMatrix), Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])⟩
  have hvpair : nativeTitsMatrixPair v = ((2 : ℂ) • (1 : TitsComplexMatrix), 0) :=
    includeHermitianMatrix_pair _
  have hvfix : f v = v := fixes_visible_input f hprod hfix v (congrArg Prod.snd hvpair)
  have hsquare : Glennie.jordan (nativeHiddenMatrix 1) (nativeHiddenMatrix 1) =
      v + nativeHiddenMatrix 1 := by
    apply nativeTitsMatrixPair_injective
    rw [hidden_one_square_pair, map_add, hvpair, nativeHiddenMatrix_pair]
    simp
  have h := congrArg (fun x => nativeTitsMatrixPair (f x)) hsquare
  have hprod1 := hprod (nativeHiddenMatrix 1) (nativeHiddenMatrix 1)
  rw [hprod1, native_tits_square_pair, haction, map_add, map_add, hvfix,
    hvpair, haction] at h
  have hp : compactSecondTitsSquare (0, R) = ((2 : ℂ) • (1 : TitsComplexMatrix), R) := by
    simpa only [one_mul, Prod.mk_add_mk, zero_add, add_zero] using h
  have hvisible : -(R * R.conjTranspose) +
      ((R * R.conjTranspose).trace.re : ℂ) • (1 : TitsComplexMatrix) =
        (2 : ℂ) • (1 : TitsComplexMatrix) := by
    simpa only [compactSecondTitsSquare, zero_mul, zero_sub] using congrArg Prod.fst hp
  have hsharp : R.adjugate.conjTranspose = R := by
    simpa [compactSecondTitsSquare] using congrArg Prod.snd hp
  have hunit := unitary_of_hidden_square_visible R hvisible
  have hdet := (adjugate_conjTranspose_eq_iff_det_eq_one R hunit).mp hsharp
  change (nativeTitsMatrixPair (f (nativeHiddenMatrix 1))).2 *
      (nativeTitsMatrixPair (f (nativeHiddenMatrix 1))).2.conjTranspose = 1 ∧
    (nativeTitsMatrixPair (f (nativeHiddenMatrix 1))).2.det = 1
  rw [← hR]
  exact ⟨hunit, hdet⟩

end CompactAlbert
