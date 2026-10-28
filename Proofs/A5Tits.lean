module

public import A5Defs

@[expose] public section

/-!
# The two-sided Tits action as a native automorphism (piece TITS)

In the accepted Tits coordinates (`nativeTitsMatrixPair x = (a, B)`, `a` Hermitian), the map
`(a, B) ↦ (g a gᴴ, g B hᴴ)` is a native Jordan automorphism when `g, h` are unitary with
`det g = det h` (so in particular for `g, h ∈ SU(3)` and for conjugation by any unitary `u`,
`g = h = u`). Route: the accepted product formula `native_tits_product_pair`
(`compactSecondTitsProduct`) and injectivity of `nativeTitsMatrixPair`, in the style of the accepted
`NativeRightSU3Action`; the adjugate term uses `adj (g B hᴴ) = det g · conj (det h) · h adj B gᴴ`-type
identities for unitary `g, h` (classical: Yokota, arXiv:0902.0431, Thm 2.12.2, with the fixer on the
other side; here the native convention puts right multiplication on `B`).
-/

noncomputable section

open CKM.NativeFirstOrder CKM.NativeGroupSlice CompactAlbert UnitaryErrorBases
open scoped Matrix

namespace CKM.NativeFourFamily

/-! ## Matrix identities for the two-sided action (helpers) -/

/-- A one-sided unitary of size three is two-sided unitary. -/
private theorem tits_left_unitary {g : TitsComplexMatrix} (hg : g * gᴴ = 1) : gᴴ * g = 1 :=
  mul_eq_one_comm.mp hg

private theorem tits_cancel {g : TitsComplexMatrix} (hg : gᴴ * g = 1) (X : TitsComplexMatrix) :
    gᴴ * (g * X) = X := by
  rw [← Matrix.mul_assoc, hg, Matrix.one_mul]

/-- Conjugation by a unitary preserves the trace. -/
private theorem tits_trace_conj {g : TitsComplexMatrix} (hg : gᴴ * g = 1) (X : TitsComplexMatrix) :
    (g * X * gᴴ).trace = X.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hg, Matrix.one_mul]

/-- The adjugate of a unitary `g` is `det g • gᴴ` (no inverse needed). -/
private theorem tits_adjugate_unitary {g : TitsComplexMatrix} (hg : g * gᴴ = 1) :
    g.adjugate = g.det • gᴴ := by
  calc
    g.adjugate = g.adjugate * (g * gᴴ) := by rw [hg, Matrix.mul_one]
    _ = (g.adjugate * g) * gᴴ := (Matrix.mul_assoc _ _ _).symm
    _ = g.det • gᴴ := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]

/-- A unitary has unimodular determinant: `det g * conj (det g) = 1`. -/
private theorem tits_det_mul_star {g : TitsComplexMatrix} (hg : g * gᴴ = 1) :
    g.det * star g.det = 1 := by
  have h := congrArg Matrix.det hg
  rwa [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h

/-- Covariance of the polynomial adjugate: for unitary `g, h` with `det g = det h`,
`adj (g X hᴴ)ᴴ = g adj (X)ᴴ hᴴ`, with no invertibility assumption on `X`. -/
private theorem tits_adjugate_two_sided {g h : TitsComplexMatrix} (hg : g * gᴴ = 1)
    (hh : h * hᴴ = 1) (hdet : g.det = h.det) (X : TitsComplexMatrix) :
    (g * X * hᴴ).adjugate.conjTranspose = g * X.adjugate.conjTranspose * hᴴ := by
  have hhc : hᴴ * hᴴᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]; exact tits_left_unitary hh
  have hag := tits_adjugate_unitary hg
  have hah := tits_adjugate_unitary hhc
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, hag, hah,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.det_conjTranspose, star_star]
  have hs : star g.det * h.det = 1 := by
    rw [← hdet, mul_comm]; exact tits_det_mul_star hg
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs, one_smul,
    Matrix.mul_assoc]

/-- Visible product covariance under `(a, B) ↦ (g a gᴴ, g B hᴴ)`. -/
private theorem tits_productComplex_two {g h : TitsComplexMatrix} (hg : g * gᴴ = 1)
    (hh : h * hᴴ = 1) (a B c D : TitsComplexMatrix) :
    compactSecondTitsProductComplex (g * a * gᴴ) (g * B * hᴴ) (g * c * gᴴ) (g * D * hᴴ) =
      g * compactSecondTitsProductComplex a B c D * gᴴ := by
  have hg' := tits_left_unitary hg
  have hh' := tits_left_unitary hh
  have hgc := tits_cancel hg'
  have hhc := tits_cancel hh'
  have hmul (X Y : TitsComplexMatrix) : (g * X * gᴴ) * (g * Y * gᴴ) = g * (X * Y) * gᴴ := by
    simp only [Matrix.mul_assoc, hgc]
  have hgram (X Y : TitsComplexMatrix) :
      (g * X * hᴴ) * (g * Y * hᴴ)ᴴ = g * (X * Yᴴ) * gᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      hhc]
  unfold compactSecondTitsProductComplex
  rw [hmul, hmul, hgram, hgram, tits_trace_conj hg']
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, hg]

/-- Hidden product covariance under `(a, B) ↦ (g a gᴴ, g B hᴴ)`, `det g = det h`. -/
private theorem tits_productHidden_two {g h : TitsComplexMatrix} (hg : g * gᴴ = 1)
    (hh : h * hᴴ = 1) (hdet : g.det = h.det) (a B c D : TitsComplexMatrix) :
    compactSecondTitsProductHidden (g * a * gᴴ) (g * B * hᴴ) (g * c * gᴴ) (g * D * hᴴ) =
      g * compactSecondTitsProductHidden a B c D * hᴴ := by
  have hg' := tits_left_unitary hg
  have hgc := tits_cancel hg'
  have hlin (s : ℂ) (X Y : TitsComplexMatrix) :
      (s • (1 : TitsComplexMatrix) - g * X * gᴴ) * (g * Y * hᴴ) =
        g * ((s • (1 : TitsComplexMatrix) - X) * Y) * hᴴ := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_assoc, hgc]
  have hsum : g * B * hᴴ + g * D * hᴴ = g * (B + D) * hᴴ := by
    rw [Matrix.mul_add, Matrix.add_mul]
  unfold compactSecondTitsProductHidden
  rw [tits_trace_conj hg', tits_trace_conj hg', hlin, hlin, hsum,
    tits_adjugate_two_sided hg hh hdet, tits_adjugate_two_sided hg hh hdet,
    tits_adjugate_two_sided hg hh hdet]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul]

/-- The native map of the two-sided Tits action (an automorphism for unitary `g, h` with
`det g = det h`, `titsTwoSided_isNativeAut`). -/
def titsTwoSided (g h : TitsComplexMatrix) : Glennie.Albert →ₗ[ℝ] Glennie.Albert where
  toFun x := Elim.mkPoint (g * hermitianMatrix (toTitsCoordinates x) * gᴴ)
    (Matrix.isHermitian_mul_mul_conjTranspose g (hermitianMatrix_isHermitian _))
    (g * (toTitsCoordinates x).2.2 * hᴴ)
  map_add' := by
    intro x y
    apply nativeTitsMatrixPair_injective
    rw [map_add, Elim.mkPoint_pair, Elim.mkPoint_pair, Elim.mkPoint_pair]
    have hxy := nativeTitsMatrixPair.map_add x y
    have h1 : hermitianMatrix (toTitsCoordinates (x + y)) =
        hermitianMatrix (toTitsCoordinates x) + hermitianMatrix (toTitsCoordinates y) :=
      congrArg Prod.fst hxy
    have h2 : (toTitsCoordinates (x + y)).2.2 =
        (toTitsCoordinates x).2.2 + (toTitsCoordinates y).2.2 :=
      congrArg Prod.snd hxy
    rw [h1, h2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_add, Matrix.add_mul]
    rfl
  map_smul' := by
    intro r x
    apply nativeTitsMatrixPair_injective
    rw [map_smul, Elim.mkPoint_pair, Elim.mkPoint_pair, RingHom.id_apply]
    have hrx := nativeTitsMatrixPair.map_smul r x
    have h1 : hermitianMatrix (toTitsCoordinates (r • x)) =
        r • hermitianMatrix (toTitsCoordinates x) :=
      congrArg Prod.fst hrx
    have h2 : (toTitsCoordinates (r • x)).2.2 = r • (toTitsCoordinates x).2.2 :=
      congrArg Prod.snd hrx
    rw [h1, h2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
    rfl

theorem titsTwoSided_pair (g h : TitsComplexMatrix) (x : Glennie.Albert) :
    nativeTitsMatrixPair (titsTwoSided g h x) =
      (g * (nativeTitsMatrixPair x).1 * gᴴ, g * (nativeTitsMatrixPair x).2 * hᴴ) := by
  change nativeTitsMatrixPair (Elim.mkPoint _ _ _) = _
  rw [Elim.mkPoint_pair]
  rfl

/-- The native trace is the real part of the trace of the visible block. -/
private theorem tits_trace_pair (x : Glennie.Albert) :
    ((Glennie.trace x : ℝ) : ℂ) = (nativeTitsMatrixPair x).1.trace :=
  (hermitianMatrix_trace (toTitsCoordinates x)).symm

/-- Jordan law and trace: the two-sided action by unitaries with equal determinant is a native
automorphism. Classical (Yokota, arXiv:0902.0431, Thm 2.12.2); proved here from the accepted
second Tits product formula `native_tits_product_pair`. -/
theorem titsTwoSided_isNativeAut {g h : TitsComplexMatrix} (hg : g * gᴴ = 1) (hh : h * hᴴ = 1)
    (hdet : g.det = h.det) : IsNativeAut (titsTwoSided g h) where
  jordan x y := by
    apply nativeTitsMatrixPair_injective
    have hp (u v : Glennie.Albert) :
        nativeTitsMatrixPair (Glennie.jordan u v) =
          compactSecondTitsProduct (nativeTitsMatrixPair u) (nativeTitsMatrixPair v) :=
      native_tits_product_pair u v
    simp only [titsTwoSided_pair, hp]
    apply Prod.ext
    · exact (tits_productComplex_two hg hh _ _ _ _).symm
    · exact (tits_productHidden_two hg hh hdet _ _ _ _).symm
  trace x := by
    apply Complex.ofReal_injective
    rw [tits_trace_pair, tits_trace_pair, titsTwoSided_pair,
      tits_trace_conj (tits_left_unitary hg)]

theorem titsTwoSided_comp (g h g' h' : TitsComplexMatrix) :
    titsTwoSided g h ∘ₗ titsTwoSided g' h' = titsTwoSided (g * g') (h * h') := by
  apply LinearMap.ext
  intro x
  apply nativeTitsMatrixPair_injective
  rw [LinearMap.comp_apply, titsTwoSided_pair, titsTwoSided_pair, titsTwoSided_pair]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem titsTwoSided_one : titsTwoSided 1 1 = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply nativeTitsMatrixPair_injective
  rw [titsTwoSided_pair, LinearMap.id_apply]
  simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem titsTwoSided_bijective {g h : TitsComplexMatrix} (hg : g * gᴴ = 1) (hh : h * hᴴ = 1) :
    Function.Bijective (titsTwoSided g h) := by
  rw [Function.bijective_iff_has_inverse]
  refine ⟨titsTwoSided gᴴ hᴴ, fun x => ?_, fun x => ?_⟩
  · have := LinearMap.congr_fun (titsTwoSided_comp gᴴ hᴴ g h) x
    rw [LinearMap.comp_apply, tits_left_unitary hg, tits_left_unitary hh,
      titsTwoSided_one] at this
    exact this
  · have := LinearMap.congr_fun (titsTwoSided_comp g h gᴴ hᴴ) x
    rw [LinearMap.comp_apply, hg, hh, titsTwoSided_one] at this
    exact this

theorem titsTwoSided_includeHermitianMatrix (g h : TitsComplexMatrix)
    (a : {a : TitsComplexMatrix // a.IsHermitian}) :
    titsTwoSided g h (includeHermitianMatrix a) =
      includeHermitianMatrix ⟨g * a.1 * gᴴ, Matrix.isHermitian_mul_mul_conjTranspose g a.2⟩ := by
  apply nativeTitsMatrixPair_injective
  rw [titsTwoSided_pair, includeHermitianMatrix_pair, includeHermitianMatrix_pair]
  simp only [Matrix.mul_zero, Matrix.zero_mul]

theorem titsTwoSided_complementaryPoint {g : TitsComplexMatrix} (hg : g * gᴴ = 1)
    (h U : TitsComplexMatrix) :
    titsTwoSided g h (nativeComplementaryPoint U) = nativeComplementaryPoint (g * U * hᴴ) := by
  apply nativeTitsMatrixPair_injective
  rw [titsTwoSided_pair, nativeComplementaryPoint_pair, nativeComplementaryPoint_pair]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hg]

theorem coordEnd_titsTwoSided_mem_autC {g h : TitsComplexMatrix} (hg : g * gᴴ = 1)
    (hh : h * hᴴ = 1) (hdet : g.det = h.det) : coordEnd (titsTwoSided g h) ∈ autC := by
  rw [mem_autC_iff_isNativeAut, AlgEquiv.symm_apply_apply]
  exact ⟨titsTwoSided_bijective hg hh, titsTwoSided_isNativeAut hg hh hdet⟩

end CKM.NativeFourFamily

#print axioms CKM.NativeFourFamily.titsTwoSided
#print axioms CKM.NativeFourFamily.titsTwoSided_pair
#print axioms CKM.NativeFourFamily.titsTwoSided_isNativeAut
#print axioms CKM.NativeFourFamily.titsTwoSided_comp
#print axioms CKM.NativeFourFamily.titsTwoSided_one
#print axioms CKM.NativeFourFamily.titsTwoSided_bijective
#print axioms CKM.NativeFourFamily.titsTwoSided_includeHermitianMatrix
#print axioms CKM.NativeFourFamily.titsTwoSided_complementaryPoint
#print axioms CKM.NativeFourFamily.coordEnd_titsTwoSided_mem_autC
