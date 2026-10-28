module

public import A3Family

@[expose] public section

/-!
# Anchor H2: the transport `T₂⁻¹` in Tits coordinates, and its action on the four point shapes

* `t2Tits`: the explicit Tits-coordinate form of `transportTinv 1` (a signed real coordinate
  permutation, here written with complex conjugations).
* `transportTinv_one_fromTits`: `T₂⁻¹ (fromTitsCoordinates q) = fromTitsCoordinates (t2Tits q)`.
* Four shape lemmas, all with free complex parameters: phase projectors and the three hidden monomial
  shapes. No phase value is fixed here.
-/

noncomputable section

namespace CKM.NativeFirstOrder

namespace Anchor2

open CompactAlbert

/-- `T₂⁻¹` in Tits coordinates `(diagonal, cyclic scalars, B)`. -/
def t2Tits (q : TitsCoordinates) : TitsCoordinates :=
  (q.1, ![q.2.2 0 0, -q.2.2 1 2, q.2.2 2 1],
    !![star (q.2.1 0), star (q.2.2 0 2), q.2.2 0 1;
      star (q.2.2 1 1), -q.2.2 1 0, star (q.2.1 1);
      -q.2.2 2 2, -star (q.2.1 2), star (q.2.2 2 0)])

theorem T2pinv_eq : TitsS.Transport.T2pinv =
    ![0, 1, 2, 7, 8, 9, 10, 3, 4, 5, 6, 17, 18, 15, 16, 13, 14, 11, 12, 21, 22, 19, 20, 25, 26, 23, 24] := by
  funext k; fin_cases k <;> rfl

theorem T2si_eq : TitsS.Transport.T2si =
    ![1, 1, 1, -1, 1, -1, 1, 1, 1, 1, 1, -1, 1, 1, -1, -1, -1, 1, 1, -1, 1, -1, -1, 1, 1, 1, -1] := by
  funext k; fin_cases k <;> rfl

theorem upper_transportTinv_one (x : Glennie.Albert) :
    NativePolynomial.upperCoordinates (transportTinv 1 x) =
      fun k => (TitsS.Transport.T2si k : ℝ) *
        NativePolynomial.upperCoordinates x (TitsS.Transport.T2pinv k) := by
  funext k
  change NativePolynomial.upperCoordinateEquiv (NativePolynomial.upperCoordinateEquiv.symm _) k = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem transportTinv_one_fromTits (q : TitsCoordinates) :
    transportTinv 1 (fromTitsCoordinates q) = fromTitsCoordinates (t2Tits q) := by
  apply NativePolynomial.upperCoordinateEquiv.injective
  change NativePolynomial.upperCoordinates _ = NativePolynomial.upperCoordinates _
  rw [upper_transportTinv_one, T2pinv_eq, T2si_eq]
  funext k
  fin_cases k <;>
    simp [NativePolynomial.upperCoordinates, fromTitsCoordinates, octonionFromTitsRow, t2Tits,
      Glennie.octConj]

theorem includeHermitianMatrix_eq_fromTits (P : {a : TitsComplexMatrix // a.IsHermitian}) :
    includeHermitianMatrix P = fromTitsCoordinates (fromHermitianPair (P, 0)) := rfl

theorem nativeComplementaryPoint_eq_fromTits (U : TitsComplexMatrix) :
    nativeComplementaryPoint U =
      fromTitsCoordinates ((fun _ => (1 / 3 : ℝ)), 0, (1 / 3 : ℂ) • U) := rfl

theorem rankOne_entry (u : Fin 3 → ℂ) (i j : Fin 3) :
    ((1 / 3 : ℂ) • Matrix.vecMulVec u (star u)) i j = (1 / 3) * (u i * star (u j)) := by
  rw [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  rfl

/-- Hermitian points with vanishing off-diagonal entries are fixed by `T₂⁻¹`. -/
theorem transportTinv_one_diagonal (P : {a : TitsComplexMatrix // a.IsHermitian})
    (h12 : P.val 1 2 = 0) (h20 : P.val 2 0 = 0) (h01 : P.val 0 1 = 0) :
    transportTinv 1 (includeHermitianMatrix P) = includeHermitianMatrix P := by
  rw [includeHermitianMatrix_eq_fromTits, transportTinv_one_fromTits]
  congr 1
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext r; fin_cases r <;> simp [t2Tits, fromHermitianPair, h12, h20, h01]
  · ext r c; fin_cases r <;> fin_cases c <;> simp [t2Tits, fromHermitianPair, h12, h20, h01]

/-- `T₂⁻¹` of a rank-one projector `(1/3) u u*` with `u = (1, x, y)`, `x, y` unit. -/
theorem transportTinv_one_rankOne (P : {a : TitsComplexMatrix // a.IsHermitian}) (x y : ℂ)
    (hx : Complex.normSq x = 1) (hy : Complex.normSq y = 1)
    (hP : P.val = (1 / 3 : ℂ) • Matrix.vecMulVec ![1, x, y] (star ![1, x, y])) :
    transportTinv 1 (includeHermitianMatrix P) =
      nativeComplementaryPoint !![star x * y, 0, 0; 0, 0, star y; 0, -x, 0] := by
  rw [includeHermitianMatrix_eq_fromTits, nativeComplementaryPoint_eq_fromTits,
    transportTinv_one_fromTits]
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext r
    fin_cases r <;> simp only [t2Tits, fromHermitianPair, hP, rankOne_entry] <;>
      simp [Complex.mul_conj, hx, hy]
  · funext r; fin_cases r <;> simp [t2Tits, fromHermitianPair]
  · ext r c
    fin_cases r <;> fin_cases c <;> simp only [t2Tits, fromHermitianPair, hP, rankOne_entry] <;>
      simp

theorem transportTinv_one_two (x y : ℂ) :
    transportTinv 1 (nativeComplementaryPoint
        (QuadraticCertificate.ExactCKMThreeHiddenFrames.twoInputMatrix x y)) =
      nativeComplementaryPoint !![0, star (x * y), 0; -y, 0, 0; 0, 0, x] := by
  rw [nativeComplementaryPoint_eq_fromTits, nativeComplementaryPoint_eq_fromTits,
    transportTinv_one_fromTits]
  congr 1
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext r; fin_cases r <;>
      simp [t2Tits, QuadraticCertificate.ExactCKMThreeHiddenFrames.twoInputMatrix]
  · ext r c
    fin_cases r <;> fin_cases c <;>
      simp [t2Tits, QuadraticCertificate.ExactCKMThreeHiddenFrames.twoInputMatrix]

theorem transportTinv_one_nj (x y : ℂ) :
    transportTinv 1 (nativeComplementaryPoint
        (QuadraticCertificate.ExactCKMCDFrames.njMatrix x y)) =
      nativeComplementaryPoint !![0, 0, x * y; 0, star y, 0; -star x, 0, 0] := by
  rw [nativeComplementaryPoint_eq_fromTits, nativeComplementaryPoint_eq_fromTits,
    transportTinv_one_fromTits]
  congr 1
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext r; fin_cases r <;>
      simp [t2Tits, QuadraticCertificate.ExactCKMCDFrames.njMatrix]
  · ext r c
    fin_cases r <;> fin_cases c <;>
      simp [t2Tits, QuadraticCertificate.ExactCKMCDFrames.njMatrix]

/-- `T₂⁻¹` sends the A/B hidden shape to the rank-one projector of `(1, x, conj y)`. -/
theorem transportTinv_one_ell (P : {a : TitsComplexMatrix // a.IsHermitian}) (x y : ℂ)
    (hx : Complex.normSq x = 1) (hy : Complex.normSq y = 1)
    (hP : P.val = (1 / 3 : ℂ) • Matrix.vecMulVec ![1, x, star y] (star ![1, x, star y])) :
    transportTinv 1 (nativeComplementaryPoint
        (QuadraticCertificate.ExactCKMABFrames.ellNMatrix x y)) = includeHermitianMatrix P := by
  rw [includeHermitianMatrix_eq_fromTits, nativeComplementaryPoint_eq_fromTits,
    transportTinv_one_fromTits]
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext r
    fin_cases r <;> simp only [t2Tits, fromHermitianPair, hP, rankOne_entry] <;>
      simp [Complex.mul_conj, hx, ← Complex.normSq_apply, hy]
  · funext r; fin_cases r <;> simp only [t2Tits, fromHermitianPair, hP, rankOne_entry] <;>
      simp [QuadraticCertificate.ExactCKMABFrames.ellNMatrix]
  · ext r c
    fin_cases r <;> fin_cases c <;>
      simp [t2Tits, fromHermitianPair, QuadraticCertificate.ExactCKMABFrames.ellNMatrix]

end Anchor2

end CKM.NativeFirstOrder
