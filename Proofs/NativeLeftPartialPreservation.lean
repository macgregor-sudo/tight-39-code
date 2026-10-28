module

public import NativeLeftPartialAction

@[expose] public section

/-!
# Native idempotency and metric preservation for the left partial action

At visible component I/3, the imported actual-native idempotency theorem
characterizes the hidden matrix U=3B by UUᴴ=I and det U=1. The partial action
sends U to VU, so the elementary multiplication laws for special-unitary
matrices prove transformed idempotency. This is a proved consequence of that
accepted classification, not an assumed preservation law for the partial map.

Native trace-pairing preservation uses the actual checked Tits pairing formula
and cyclic trace. The needed VᴴV=I is derived from VVᴴ=I and det V=1 through
the imported polynomial adjugate theorem. No global Jordan covariance for g or
T, ordinary unweighted coordinate metric, new carrier, original-point label
coverage, dimension or exhaustion conclusion is asserted.

New first-party applications of imported native classification and elementary
matrix identities. No upstream implementation is copied. Existing native-source
provenance, Apache-2.0 notices and mathlib pin remain in the unchanged imports.
Thanks to the native-model, Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

noncomputable section

namespace CompactAlbert

/-- Both unitary inverse identities follow from the supplied special-unitary
conditions, using the polynomial adjugate identity. -/
theorem nativeSpecialUnitary_left_inverse (V : TitsComplexMatrix)
    (hV : V * V.conjTranspose = (1 : TitsComplexMatrix)) (hd : V.det = 1) :
    V.conjTranspose * V = (1 : TitsComplexMatrix) := by
  have hAdj := Matrix.adjugate_mul V
  rw [hd, one_smul] at hAdj
  have hSharp := (adjugate_conjTranspose_eq_iff_det_eq_one V hV).mpr hd
  have hConj := congrArg (fun A : TitsComplexMatrix => A.conjTranspose) hSharp
  simp only [Matrix.conjTranspose_conjTranspose] at hConj
  rw [hConj] at hAdj
  exact hAdj

theorem nativePartialLeft_visible (V : TitsComplexMatrix) (x : Glennie.Albert) :
    hermitianMatrix (toTitsCoordinates (nativePartialLeft V x)) =
      hermitianMatrix (toTitsCoordinates x) := by
  rw [nativePartialLeft_coordinates]
  rfl

theorem nativePartialLeft_hidden (V : TitsComplexMatrix) (x : Glennie.Albert) :
    (toTitsCoordinates (nativePartialLeft V x)).2.2 =
      V * (toTitsCoordinates x).2.2 := by
  rw [nativePartialLeft_coordinates]

/-- The native trace is unchanged for every parameter matrix. -/
theorem nativePartialLeft_trace (V : TitsComplexMatrix) (x : Glennie.Albert) :
    Glennie.trace (nativePartialLeft V x) = Glennie.trace x := by
  rw [← compactTitsCoordinateEquiv_trace (nativePartialLeft V x),
    ← compactTitsCoordinateEquiv_trace x]
  change titsTrace (toTitsCoordinates (nativePartialLeft V x)) = _
  rw [nativePartialLeft_coordinates]
  rfl

private theorem hidden_left_trace (V : TitsComplexMatrix)
    (hVleft : V.conjTranspose * V = (1 : TitsComplexMatrix))
    (B D : TitsComplexMatrix) :
    ((V * B) * (V * D).conjTranspose).trace = (B * D.conjTranspose).trace := by
  rw [Matrix.conjTranspose_mul]
  calc
    _ = ((V * (B * D.conjTranspose)) * V.conjTranspose).trace := by
      simp only [Matrix.mul_assoc]
    _ = (V.conjTranspose * (V * (B * D.conjTranspose))).trace :=
      Matrix.trace_mul_comm _ _
    _ = (B * D.conjTranspose).trace := by
      rw [← Matrix.mul_assoc, hVleft, Matrix.one_mul]

/-- Isometry of the actual native product trace, with its correct hidden
factor two. No product-preservation law for the partial map is assumed. -/
theorem nativePartialLeft_trace_pairing (V : TitsComplexMatrix)
    (hV : V * V.conjTranspose = (1 : TitsComplexMatrix)) (hd : V.det = 1)
    (x y : Glennie.Albert) :
    Glennie.trace (Glennie.jordan (nativePartialLeft V x) (nativePartialLeft V y)) =
      Glennie.trace (Glennie.jordan x y) := by
  have hVleft := nativeSpecialUnitary_left_inverse V hV hd
  simp only [native_trace_jordan_eq_tits_pairing, nativePartialLeft_visible,
    nativePartialLeft_hidden, hidden_left_trace V hVleft]

/-- A pure-visible actual native vector is fixed. -/
theorem nativePartialLeft_eq_self_of_hidden_zero (V : TitsComplexMatrix)
    (x : Glennie.Albert) (hx : (nativeTitsMatrixPair x).2 = 0) :
    nativePartialLeft V x = x := by
  apply nativeTitsMatrixPair_injective
  rw [nativePartialLeft_pair]
  apply Prod.ext
  · rfl
  · change V * (nativeTitsMatrixPair x).2 = (nativeTitsMatrixPair x).2
    rw [hx, Matrix.mul_zero]

/-- Special-unitary multiplication preserves native idempotency on the
visible-I/3 slice. The proof uses the imported iff in both directions. -/
theorem nativePartialLeft_idempotent_of_visible_third (V : TitsComplexMatrix)
    (hV : V * V.conjTranspose = (1 : TitsComplexMatrix)) (hd : V.det = 1)
    (x : Glennie.Albert)
    (hx : hermitianMatrix (toTitsCoordinates x) =
      (1 / 3 : ℂ) • (1 : TitsComplexMatrix))
    (hId : Glennie.jordan x x = x) :
    Glennie.jordan (nativePartialLeft V x) (nativePartialLeft V x) =
      nativePartialLeft V x := by
  have hU := (native_idempotent_iff_scaled_specialUnitary_conditions x hx).mp hId
  have hTx : hermitianMatrix (toTitsCoordinates (nativePartialLeft V x)) =
      (1 / 3 : ℂ) • (1 : TitsComplexMatrix) := by
    rw [nativePartialLeft_visible, hx]
  apply (native_idempotent_iff_scaled_specialUnitary_conditions _ hTx).mpr
  simp only [nativePartialLeft_hidden, ← Matrix.mul_smul]
  constructor
  · rw [Matrix.conjTranspose_mul]
    calc
      _ = V * (((3 : ℂ) • (toTitsCoordinates x).2.2) *
          ((3 : ℂ) • (toTitsCoordinates x).2.2).conjTranspose) * V.conjTranspose := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU.1, Matrix.mul_one, hV]
  · rw [Matrix.det_mul, hd, hU.2, one_mul]

/-- The two required point classes: fixed visible vectors and the actual
native scalar-visible slice. Their classification is a statement about input
positions; transformed idempotency is proved rather than supplied. -/
theorem nativePartialLeft_idempotent_of_position (V : TitsComplexMatrix)
    (hV : V * V.conjTranspose = (1 : TitsComplexMatrix)) (hd : V.det = 1)
    (x : Glennie.Albert) (hId : Glennie.jordan x x = x)
    (hx : (nativeTitsMatrixPair x).2 = 0 ∨
      hermitianMatrix (toTitsCoordinates x) = (1 / 3 : ℂ) • (1 : TitsComplexMatrix)) :
    Glennie.jordan (nativePartialLeft V x) (nativePartialLeft V x) =
      nativePartialLeft V x := by
  rcases hx with hZero | hThird
  · rw [nativePartialLeft_eq_self_of_hidden_zero V x hZero]
    exact hId
  · exact nativePartialLeft_idempotent_of_visible_third V hV hd x hThird hId

end CompactAlbert
