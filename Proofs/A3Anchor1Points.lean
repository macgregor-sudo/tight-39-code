module

public import A3Family

@[expose] public section

/-!
# Anchor H1, part 1: `T₁⁻¹` in Tits coordinates and its action on the literal points

`transportTinv 0` fixes the diagonal and acts on the Tits scalars `c` and matrix `B` by an explicit
signed, partly conjugated entry permutation (`tinvTits`). Every literal point is (by `A3Family`) an
included Hermitian matrix or a complementary point, so the image is computed entrywise.
-/

noncomputable section

namespace CKM.NativeFirstOrder

open NativePolynomial CompactAlbert UnitaryErrorBases.ComplexQuartet

namespace Anchor1

/-- `T₁⁻¹` read in Tits coordinates `(diagonal, cyclic scalars c, matrix B)`. -/
def tinvTits (x : TitsCoordinates) : TitsCoordinates :=
  (x.1, ![star (x.2.2 0 2), star (x.2.2 1 1), -star (x.2.2 2 0)],
    !![x.2.2 0 1, star (x.2.2 0 0), x.2.1 0;
       star (x.2.2 1 2), -x.2.1 1, -x.2.2 1 0;
       x.2.1 2, -x.2.2 2 2, star (x.2.2 2 1)])

/-- Native components of `T₁⁻¹`: the signed coordinate permutation written out. -/
theorem transportTinv_zero_apply (x : Glennie.Albert) :
    transportTinv 0 x =
      ⟨x.d0, x.d1, x.d2,
        (⟨x.o01.1.imJ, x.o01.1.imK, -x.o01.1.re, x.o01.1.imI⟩,
          ⟨-x.o01.2.imJ, x.o01.2.imK, x.o01.2.re, x.o01.2.imI⟩),
        (⟨x.o02.2.re, -x.o02.2.imI, x.o02.2.imJ, x.o02.2.imK⟩,
          ⟨-x.o02.1.re, -x.o02.1.imI, -x.o02.1.imJ, x.o02.1.imK⟩),
        (⟨-x.o12.2.imJ, x.o12.2.imK, x.o12.2.re, x.o12.2.imI⟩,
          ⟨x.o12.1.imJ, -x.o12.1.imK, -x.o12.1.re, -x.o12.1.imI⟩)⟩ := by
  simp only [transportTinv, signedTransport, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply]
  change fromUpperCoordinates _ = _
  simp only [fromUpperCoordinates, upperCoordinateEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk]
  simp [TitsS.Transport.T1pinv, TitsS.Transport.T1si, TitsS.permOfList, TitsS.sgnOfList,
    T1_inv_perm, T1_inv_sign, upperCoordinates]

/-- `T₁⁻¹` in Tits coordinates. -/
theorem transportTinv_zero_eq (x : Glennie.Albert) :
    transportTinv 0 x = fromTitsCoordinates (tinvTits (toTitsCoordinates x)) := by
  rw [transportTinv_zero_apply]
  apply Glennie.Albert.ext <;>
    simp [fromTitsCoordinates, tinvTits, toTitsCoordinates, octonionFromTitsRow,
      octonionToTitsRow, Glennie.octConj]

/-! ## Images of included matrices and complementary points -/

/-- `T₁⁻¹` fixes an included diagonal matrix. -/
theorem transportTinv_zero_includeHermitianMatrix_diag (P : {a : TitsComplexMatrix // a.IsHermitian})
    (h01 : P.val 0 1 = 0) (h12 : P.val 1 2 = 0) (h20 : P.val 2 0 = 0) :
    transportTinv 0 (includeHermitianMatrix P) = includeHermitianMatrix P := by
  rw [transportTinv_zero_eq, includeHermitianMatrix, toTitsCoordinates_fromTitsCoordinates]
  congr 1
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext r
    fin_cases r <;> simp [tinvTits, fromHermitianPair, h01, h12, h20]
  · funext r c
    fin_cases r <;> fin_cases c <;> simp [tinvTits, fromHermitianPair, h01, h12, h20]

/-- `T₁⁻¹` sends an included matrix with diagonal `1/3` to a complementary point. -/
theorem transportTinv_zero_includeHermitianMatrix_third
    (P : {a : TitsComplexMatrix // a.IsHermitian}) (hd : ∀ i, (P.val i i).re = 1 / 3) :
    transportTinv 0 (includeHermitianMatrix P) =
      nativeComplementaryPoint
        !![0, 0, 3 * P.val 1 2; 0, -(3 * P.val 2 0), 0; 3 * P.val 0 1, 0, 0] := by
  rw [transportTinv_zero_eq, includeHermitianMatrix, toTitsCoordinates_fromTitsCoordinates,
    nativeComplementaryPoint]
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext r
    fin_cases r <;> simp [tinvTits, fromHermitianPair, hd]
  · funext r
    fin_cases r <;> simp [tinvTits, fromHermitianPair]
  · funext r c
    fin_cases r <;> fin_cases c <;> simp [tinvTits, fromHermitianPair]

/-- The hidden matrix of a complementary point after `T₁⁻¹` (zero antidiagonal input). -/
def tinvB (U : TitsComplexMatrix) : TitsComplexMatrix :=
  !![U 0 1, star (U 0 0), 0; star (U 1 2), 0, -U 1 0; 0, -U 2 2, star (U 2 1)]

/-- `T₁⁻¹` keeps a complementary point with zero antidiagonal complementary. -/
theorem transportTinv_zero_complementary_hidden (U : TitsComplexMatrix)
    (h02 : U 0 2 = 0) (h11 : U 1 1 = 0) (h20 : U 2 0 = 0) :
    transportTinv 0 (nativeComplementaryPoint U) = nativeComplementaryPoint (tinvB U) := by
  rw [transportTinv_zero_eq, nativeComplementaryPoint, toTitsCoordinates_fromTitsCoordinates]
  congr 1
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext r
    fin_cases r <;> simp [tinvTits, h02, h11, h20]
  · funext r c
    fin_cases r <;> fin_cases c <;> simp [tinvTits, tinvB, h02, h11, h20]

/-- `T₁⁻¹` sends a complementary point with antidiagonal matrix to an included matrix. -/
theorem transportTinv_zero_complementary_visible (U : TitsComplexMatrix)
    (Q : {a : TitsComplexMatrix // a.IsHermitian})
    (h00 : U 0 0 = 0) (h01 : U 0 1 = 0) (h10 : U 1 0 = 0) (h12 : U 1 2 = 0)
    (h21 : U 2 1 = 0) (h22 : U 2 2 = 0) (hd : ∀ i, (Q.val i i).re = 1 / 3)
    (hQ12 : Q.val 1 2 = star (U 0 2) / 3) (hQ20 : Q.val 2 0 = star (U 1 1) / 3)
    (hQ01 : Q.val 0 1 = -star (U 2 0) / 3) :
    transportTinv 0 (nativeComplementaryPoint U) = includeHermitianMatrix Q := by
  rw [transportTinv_zero_eq, nativeComplementaryPoint, toTitsCoordinates_fromTitsCoordinates,
    includeHermitianMatrix]
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext r
    fin_cases r <;> simp [tinvTits, fromHermitianPair, hd]
  · funext r
    fin_cases r <;> simp [tinvTits, fromHermitianPair, hQ12, hQ20, hQ01] <;> ring
  · funext r c
    fin_cases r <;> fin_cases c <;>
      simp [tinvTits, fromHermitianPair, h00, h01, h10, h12, h21, h22]

/-! ## Characters of `ZMod 3` -/

local notation "χ" => UnitaryErrorBases.ThreeCycleFourier.character
local notation "ω" => UnitaryErrorBases.ThreeCycleFourier.omega

theorem omega_pow_mod (n : ℕ) : ω ^ (n % 3) = ω ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul,
    UnitaryErrorBases.ThreeCycleFourier.omega_cube, one_pow, one_mul]

theorem star_omega : star ω = ω ^ 2 := by
  rw [UnitaryErrorBases.ThreeCycleFourier.omega_sq]
  apply Complex.ext <;>
    simp [UnitaryErrorBases.ThreeCycleFourier.omega] <;> ring

theorem char_add (a b : PhaseIndex) : χ (a + b) = χ a * χ b := by
  simp only [UnitaryErrorBases.ThreeCycleFourier.character, ZMod.val_add, omega_pow_mod, pow_add]

theorem char_cube (a : PhaseIndex) : χ a ^ 3 = 1 := by
  rw [UnitaryErrorBases.ThreeCycleFourier.character, ← pow_mul, mul_comm, pow_mul,
    UnitaryErrorBases.ThreeCycleFourier.omega_cube, one_pow]

theorem char_neg (a : PhaseIndex) : χ (-a) = χ a ^ 2 := by
  have h : χ (-a) * χ a = 1 := by
    rw [← char_add, neg_add_cancel]
    simp [UnitaryErrorBases.ThreeCycleFourier.character]
  calc χ (-a) = χ (-a) * χ a ^ 3 := by rw [char_cube, mul_one]
    _ = (χ (-a) * χ a) * χ a ^ 2 := by ring
    _ = χ a ^ 2 := by rw [h, one_mul]

theorem char_sub (a b : PhaseIndex) : χ (a - b) = χ a * χ b ^ 2 := by
  rw [sub_eq_add_neg, char_add, char_neg]

theorem star_char (a : PhaseIndex) : star (χ a) = χ a ^ 2 := by
  simp only [UnitaryErrorBases.ThreeCycleFourier.character, star_pow, star_omega, ← pow_mul,
    mul_comm 2]

theorem star_eq_inv_of_normSq {z : ℂ} (hz : Complex.normSq z = 1) : star z = z⁻¹ := by
  rw [Complex.inv_def, hz]
  simp

/-- Power reductions for a cube root of unity. -/
theorem cube_pows {u : ℂ} (hu : u ^ 3 = 1) :
    u ^ 4 = u ∧ u ^ 5 = u ^ 2 ∧ u ^ 6 = 1 ∧ u ^ 7 = u ∧ u ^ 8 = u ^ 2 ∧ u ^ 9 = 1 ∧
      u ^ 10 = u ∧ u ^ 11 = u ^ 2 ∧ u ^ 12 = 1 := by
  have h : ∀ n : ℕ, u ^ (n + 3) = u ^ n := fun n => by rw [pow_add, hu, mul_one]
  have h4 : u ^ 4 = u := by simpa using h 1
  have h5 : u ^ 5 = u ^ 2 := h 2
  have h6 : u ^ 6 = 1 := (h 3).trans hu
  exact ⟨h4, h5, h6, (h 4).trans h4, (h 5).trans h5, (h 6).trans h6, ((h 7).trans (h 4)).trans h4,
    ((h 8).trans (h 5)).trans h5, ((h 9).trans (h 6)).trans h6⟩

-- Close a monomial identity in characters `χ s`, `χ t` (cube roots of unity, with the power
-- reductions `u4 … u12`, `v4 … v12` in scope) and nonzero phases.
set_option hygiene false in
macro "cube_close" : tactic => `(tactic| first
  | ring1
  | (field_simp; done)
  | (field_simp; ring1)
  | (ring_nf; (try simp only [hu, hv, u4, u5, u6, u7, u8, u9, u10, u11, u12, v4, v5, v6, v7, v8, v9, v10,
      v11, v12]); (try ring_nf); done)
  | (field_simp; (try ring_nf); (try simp only [hu, hv, u4, u5, u6, u7, u8, u9, u10, u11, u12, v4, v5, v6, v7,
      v8, v9, v10, v11, v12]); (try ring_nf); done))

/-! ## The quartet: original frames 0 and 4–6 -/

/-- The diagonal conjugation `g = diag(1, −1, −1)` of the H1 quartet. -/
def gQ : TitsComplexMatrix := Matrix.diagonal ![1, -1, -1]

theorem gQ_unitary : gQ * gQ.conjTranspose = 1 := by
  rw [gQ, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  fin_cases j <;> simp

/-- The anchored quartet `g · std · gᴴ`. -/
def q1 (k : Fin 4) (t : Fin 3) : {a : TitsComplexMatrix // a.IsHermitian} :=
  ⟨gQ * (stdQuartet k t).val * gQ.conjTranspose,
    Matrix.isHermitian_mul_mul_conjTranspose gQ (stdQuartet k t).property⟩

theorem gQ_conj_apply (P : TitsComplexMatrix) (i j : Fin 3) :
    (gQ * P * gQ.conjTranspose) i j = ![1, -1, -1] i * P i j * ![1, -1, -1] j := by
  rw [gQ, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases j <;> simp

/-- Original frame 0 is fixed by `T₁⁻¹` and equals the conjugated coordinate frame. -/
theorem quartet_frame_zero (t : Fin 3) :
    transportTinv 0 (includeHermitianMatrix (stdQuartet 0 t)) = includeHermitianMatrix (q1 0 t) := by
  have hP : ∀ i j : Fin 3, i ≠ j → (stdQuartet 0 t).val i j = 0 := by
    intro i j hij
    simp [stdQuartet, coordinateProjector, Matrix.diagonal_apply_ne _ hij]
  rw [transportTinv_zero_includeHermitianMatrix_diag _ (hP 0 1 (by decide)) (hP 1 2 (by decide))
    (hP 2 0 (by decide))]
  congr 1
  apply Subtype.ext
  ext i j
  change _ = (gQ * (stdQuartet 0 t).val * gQ.conjTranspose) i j
  rw [gQ_conj_apply]
  by_cases hij : i = j
  · subst hij
    fin_cases i <;> simp
  · rw [hP i j hij]
    simp

theorem phaseRay_normSq (s t : PhaseIndex) (i : Fin 3) :
    phaseRay s t i * star (phaseRay s t i) = 1 := by
  fin_cases i <;>
    simp [phaseRay, star_char, ← pow_succ', char_cube]

/-- Original frame `4 + s`, outcome `−t`, goes to the conjugated phase projector `(s, t)`. -/
theorem quartet_frame_phase (ξ : Fin 4 → ℂ) (s t : PhaseIndex) :
    transportTinv 0 (nativeComplementaryPoint (hiddenMatrix ξ 0 s (-t))) =
      includeHermitianMatrix
        ⟨gQ * phaseProjector s t * gQ.conjTranspose,
          Matrix.isHermitian_mul_mul_conjTranspose gQ (phaseProjector_isHermitian s t)⟩ := by
  have hu := char_cube s
  have hv := char_cube t
  obtain ⟨u4, u5, u6, u7, u8, u9, u10, u11, u12⟩ := cube_pows hu
  obtain ⟨v4, v5, v6, v7, v8, v9, v10, v11, v12⟩ := cube_pows hv
  apply transportTinv_zero_complementary_visible <;>
    simp only [hiddenMatrix, QuadraticCertificate.ExactCKMThreeHiddenFrames.twoInputMatrix,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.tail_cons, Matrix.head_fin_const]
  · intro i
    rw [gQ_conj_apply, phaseProjector, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      phaseRay_normSq]
    fin_cases i <;> simp
  all_goals
    rw [gQ_conj_apply, phaseProjector, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply]
    simp only [phaseRay, char_add, char_sub, char_neg, star_mul', star_pow, star_char, star_neg,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, smul_eq_mul, star_one]
    first
    | ring1
    | (ring_nf; simp only [u4, v5, v8])

end Anchor1

end CKM.NativeFirstOrder
