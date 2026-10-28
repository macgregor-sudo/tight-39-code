module

public import A5Gauge
public import A5SU3

@[expose] public section

/-!
# The original equations on the raw families (piece ANCHF)

No accepted theorem covers `stdAnchored q W` for a general unitary error basis `W`; it is proved
here directly from accepted ingredients (as A3's `literalCfg_originalEquations`): hidden frames
`native_central_triples_are_frames`, hidden-hidden overlaps `nativeComplementaryPoint_overlap`
with UEB orthogonality, quartet-hidden overlaps `native_trace_jordan_includeHermitianMatrix`, and the
quartet's own equations (a unitary conjugate of the standard complete quartet in `H₃(ℂ)`, through
`native_tits_product_pair` at `B = D = 0`). Frame-preserving relabelling permutes the 2184 rows.
Pullback by the native transport and saturation by `G` use `originalF_actC`.
-/

noncomputable section

open CKM.NativeFirstOrder CKM.NativeGroupSlice CompactAlbert UnitaryErrorBases
open scoped Matrix Topology

namespace CKM.NativeFourFamily

/-- The hidden family is a unitary error basis: a two-sided unitary gauge of the monomial basis
(`monomial_family_is_unitary_error_basis`), with unit-modulus rephasing; its members have
determinant `c³ · det g · det L · det E · det R · conj (det h) = 1`. -/
theorem isUnitaryErrorBasis_hidFamily {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4)
    {g h : Mat} (hg : g ∈ Matrix.specialUnitaryGroup Index ℂ)
    (hh : h ∈ Matrix.specialUnitaryGroup Index ℂ) (d : PhaseTriple) :
    IsUnitaryErrorBasis (hidFamily ξ₀ H g h d) := by
  obtain ⟨hgu, hgd⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hg
  obtain ⟨hhu, hhd⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hh
  have hg1 : gᴴ * g = 1 := Matrix.mem_unitaryGroup_iff'.mp hgu
  have hh1 : hᴴ * h = 1 := Matrix.mem_unitaryGroup_iff'.mp hhu
  have hE := ThreeCycleMatrix.monomial_family_is_unitary_error_basis d
  have hL := gaugeLeft_unitary hξ₀ H
  have hR := gaugeRight_unitary hξ₀ H
  refine Anchor0.isUnitaryErrorBasis_of_gauge (monomialFamily d) _ hE
    (g * gaugeLeft ξ₀ H) (gaugeRight ξ₀ H * hᴴ) ?_ ?_ (gaugeScalar H) (gaugeScalar_normSq H)
    (gaugeLabel H) ?_ ?_
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg1, Matrix.one_mul, hL]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc hᴴ, hh1, Matrix.one_mul, hR]
  · intro p
    simp only [hidFamily, Matrix.mul_assoc]
  · intro p
    have hEd : (monomialFamily d (gaugeLabel H p)).det = 1 := (hE.1 _).2
    rw [hidFamily, Matrix.det_smul, ZMod.card, gaugeScalar_cube, one_mul]
    simp only [Matrix.det_mul, Matrix.det_conjTranspose, hgd, hhd, hEd, star_one, one_mul,
      mul_one]
    exact gauge_det hξ₀ H

/-! ## The standard anchored form: helpers -/

/-- The native unit in Tits matrix-pair coordinates.

Adapted from the private lemma `native_pair_unit` (lines 128–138) of the accepted first-party
closure source `NativeExactCKMSharedPhaseFrames.lean`
(`option2-lean-sprint-20261025/operator/selection-original-f-regularity-chain-v2-r1/returned-original-f-regularity-v2-r2`,
namespace `QuadraticCertificate.ExactCKMSharedFrames`; native-model project, no release license
assigned; it builds on compact-albert-recognition
`https://github.com/macgregor-sudo/compact-albert-recognition` at commit
`40d3b344180d9ddb78aaa2876873377c1e631515`, SPDX-License-Identifier: Apache-2.0).
Modification: renamed and re-declared privately here (the original is private). Thanks to the
native-model and compact-library authors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to
Robert Hooke, 1676. -/
private theorem anchf_pair_unit : nativeTitsMatrixPair (1 : Glennie.Albert) = (1, 0) := by
  change toMatrixPair (toTitsCoordinates (1 : Glennie.Albert)) = (1, 0)
  have hu := compactTitsCoordinateEquiv_unit
  change toTitsCoordinates (1 : Glennie.Albert) = titsUnit at hu
  rw [hu]
  apply Prod.ext
  · ext r c
    fin_cases r <;> fin_cases c <;>
      norm_num [toMatrixPair, hermitianMatrix, titsUnit, Matrix.one_apply]
  · rfl

/-- `includeHermitianMatrix` is a Jordan embedding of `H₃(ℂ)` (`native_tits_product_pair` at
`B = D = 0`). -/
private theorem anchf_jordan_incl_pair (P Q : {a : TitsComplexMatrix // a.IsHermitian}) :
    nativeTitsMatrixPair (Glennie.jordan (includeHermitianMatrix P) (includeHermitianMatrix Q)) =
      ((1 / 2 : ℂ) • (P.val * Q.val + Q.val * P.val), 0) := by
  have h := native_tits_product_pair (includeHermitianMatrix P) (includeHermitianMatrix Q)
  change nativeTitsMatrixPair _ =
    compactSecondTitsProduct (nativeTitsMatrixPair _) (nativeTitsMatrixPair _) at h
  rw [h, includeHermitianMatrix_pair, includeHermitianMatrix_pair]
  simp [compactSecondTitsProduct, compactSecondTitsProductComplex,
    compactSecondTitsProductHidden, Matrix.adjugate_zero]

private theorem anchf_conj_mul (u : TitsComplexMatrix) (hu : uᴴ * u = 1) (X Y : TitsComplexMatrix) :
    u * X * uᴴ * (u * Y * uᴴ) = u * (X * Y) * uᴴ := by
  calc u * X * uᴴ * (u * Y * uᴴ) = u * X * (uᴴ * u) * Y * uᴴ := by
        simp only [Matrix.mul_assoc]
    _ = u * (X * Y) * uᴴ := by rw [hu, Matrix.mul_one]; simp only [Matrix.mul_assoc]

private theorem anchf_trace_conj (u : TitsComplexMatrix) (hu : uᴴ * u = 1) (X : TitsComplexMatrix) :
    (u * X * uᴴ).trace = X.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hu, Matrix.one_mul]

/-- Jordan products of conjugated included matrices are conjugated. -/
private theorem anchf_jordan_conj (u : TitsComplexMatrix) (hu : uᴴ * u = 1)
    (P Q a b : {x : TitsComplexMatrix // x.IsHermitian})
    (ha : a.val = u * P.val * uᴴ) (hb : b.val = u * Q.val * uᴴ) :
    nativeTitsMatrixPair (Glennie.jordan (includeHermitianMatrix a) (includeHermitianMatrix b)) =
      (u * (nativeTitsMatrixPair
        (Glennie.jordan (includeHermitianMatrix P) (includeHermitianMatrix Q))).1 * uᴴ, 0) := by
  rw [anchf_jordan_incl_pair, anchf_jordan_incl_pair, ha, hb, anchf_conj_mul u hu,
    anchf_conj_mul u hu]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]

/-- The native trace pairing of two included matrices is `Re tr (a b)`. -/
private theorem anchf_trace_incl (a b : {x : TitsComplexMatrix // x.IsHermitian}) :
    Glennie.trace (Glennie.jordan (includeHermitianMatrix a) (includeHermitianMatrix b)) =
      (a.val * b.val).trace.re := by
  rw [native_trace_jordan_includeHermitianMatrix]
  have h := includeHermitianMatrix_pair a
  change toMatrixPair (toTitsCoordinates (includeHermitianMatrix a)) = _ at h
  have h1 : hermitianMatrix (toTitsCoordinates (includeHermitianMatrix a)) = a.val :=
    congrArg Prod.fst h
  rw [h1]

private theorem anchf_trace_incl_conj (u : TitsComplexMatrix) (hu : uᴴ * u = 1)
    (P Q a b : {x : TitsComplexMatrix // x.IsHermitian})
    (ha : a.val = u * P.val * uᴴ) (hb : b.val = u * Q.val * uᴴ) :
    Glennie.trace (Glennie.jordan (includeHermitianMatrix a) (includeHermitianMatrix b)) =
      Glennie.trace (Glennie.jordan (includeHermitianMatrix P) (includeHermitianMatrix Q)) := by
  rw [anchf_trace_incl, anchf_trace_incl, ha, hb, anchf_conj_mul u hu, anchf_trace_conj u hu]

/-- A unitary conjugate of an included native frame is an included native frame. -/
private theorem anchf_frame_conj (u : TitsComplexMatrix) (hu : uᴴ * u = 1)
    (P a : Fin 3 → {x : TitsComplexMatrix // x.IsHermitian})
    (ha : ∀ t, (a t).val = u * (P t).val * uᴴ)
    (hP : Glennie.Frame fun t => includeHermitianMatrix (P t)) :
    Glennie.Frame fun t => includeHermitianMatrix (a t) := by
  have huu : u * uᴴ = 1 := mul_eq_one_comm.mp hu
  have hidem : ∀ t, Glennie.jordan (includeHermitianMatrix (a t)) (includeHermitianMatrix (a t)) =
      includeHermitianMatrix (a t) := by
    intro t
    apply nativeTitsMatrixPair_injective
    rw [anchf_jordan_conj u hu (P t) (P t) (a t) (a t) (ha t) (ha t), hP.idempotent t,
      includeHermitianMatrix_pair, includeHermitianMatrix_pair, ha t]
  refine ⟨fun t => ?_, hidem, fun s t hst => ?_, ?_⟩
  · rw [← hidem t, anchf_trace_incl_conj u hu (P t) (P t) (a t) (a t) (ha t) (ha t),
      hP.idempotent t]
    exact hP.trace_one t
  · apply nativeTitsMatrixPair_injective
    rw [anchf_jordan_conj u hu (P s) (P t) (a s) (a t) (ha s) (ha t), hP.orthogonal s t hst,
      map_zero]
    simp
  · have hs := hP.sum_unit
    apply nativeTitsMatrixPair_injective
    have hs' := congrArg nativeTitsMatrixPair hs
    simp only [map_add, includeHermitianMatrix_pair, anchf_pair_unit, Prod.mk_add_mk,
      add_zero] at hs' ⊢
    rw [Prod.mk.injEq] at hs'
    rw [ha 0, ha 1, ha 2, ← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.mul_add,
      hs'.1, Matrix.mul_one, huu]

/-- The standard complete quartet is a family of four included native frames. -/
private theorem anchf_std_frame (k : Fin 4) :
    Glennie.Frame fun t => includeHermitianMatrix (stdQuartet k t) := by
  have h := literal_low_frame (fun _ => 1) (Fin.castLE (by omega) k) (by simp; omega)
  simpa only [literalPoint_quartet] using h

private theorem anchf_literal_quartet (ξ : Fin 4 → ℂ) (i : Fin 39) (hi : i.val < 12) :
    literalPoint ξ i = includeHermitianMatrix (stdQuartet ⟨i.val / 3, by omega⟩ ⟨i.val % 3, by omega⟩) := by
  rw [← literalPoint_quartet ξ ⟨i.val / 3, by omega⟩ ⟨i.val % 3, by omega⟩]
  congr 1
  apply Fin.ext
  simp only [NativePolynomial.ConfigurationResiduals.framePointIndex_val, Fin.val_castLE]
  omega

private theorem anchf_std_vis (q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian})
    (W : Family) (i : Fin 39) (hi : i.val < 12) :
    stdAnchored q W i = includeHermitianMatrix (q ⟨i.val / 3, by omega⟩ ⟨i.val % 3, by omega⟩) := by
  rw [stdAnchored, dite_eq_left_of_eq_true (eq_true hi)]

private theorem anchf_std_hid (q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian})
    (W : Family) (i : Fin 39) (hi : ¬ i.val < 12) :
    stdAnchored q W i = nativeComplementaryPoint
      ((UnitaryErrorBases.ThreeCycleFourier.omega ^ (i.val % 3)) •
        W (hiddenFrameEquiv.symm ⟨i.val / 3 - 4, by have := i.isLt; omega⟩)) := by
  rw [stdAnchored, dite_eq_right_of_eq_false (eq_false hi)]

/-- All thirteen frames of `stdAnchored q W` are native frames. -/
private theorem anchf_frame (u : TitsComplexMatrix) (hu : uᴴ * u = 1)
    (q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian})
    (hq : ∀ k t, (q k t).val = u * (stdQuartet k t).val * uᴴ)
    (W : Family) (hW : IsUnitaryErrorBasis W) (f : Fin 13) :
    Glennie.Frame fun a => stdAnchored q W (NativePolynomial.ConfigurationResiduals.framePointIndex f a) := by
  by_cases hf : f.val < 4
  · obtain ⟨k, hk⟩ : ∃ k : Fin 4, Fin.castLE (by omega : 4 ≤ 13) k = f :=
      ⟨⟨f.val, hf⟩, Fin.ext rfl⟩
    rw [← hk]
    simp only [Anchor3.stdAnchored_vis]
    exact anchf_frame_conj u hu (stdQuartet k) (q k) (hq k) (anchf_std_frame k)
  · have hf13 := f.isLt
    obtain ⟨l, rfl⟩ : ∃ l : Label, hiddenFrame l = f :=
      ⟨hiddenFrameEquiv.symm ⟨f.val - 4, by omega⟩, by
        apply Fin.ext
        show 4 + (hiddenFrameEquiv (hiddenFrameEquiv.symm _)).val = f.val
        rw [Equiv.apply_symm_apply]
        show 4 + (f.val - 4) = f.val
        omega⟩
    simp only [Anchor3.stdAnchored_hid]
    have htr : (fun a : Fin 3 => nativeComplementaryPoint
        (UnitaryErrorBases.ThreeCycleFourier.omega ^ (a : Fin 3).val • W l)) =
        nativeCentralTriple (W l) := by
      funext a
      fin_cases a <;> simp [nativeCentralTriple] <;> rfl
    rw [htr]
    exact (native_central_triples_are_frames (W l)
      ⟨mul_eq_one_comm.mp (hW.1 l).1, (hW.1 l).2⟩).1

section anchf_std
open NativePolynomial NativePolynomial.ConfigurationResiduals

private theorem anchf_originalEquations_std (u : TitsComplexMatrix) (hu : u * uᴴ = 1)
    (q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian})
    (hq : ∀ k t, (q k t).val = u * (stdQuartet k t).val * uᴴ)
    (W : Family) (hW : IsUnitaryErrorBasis W) :
    NativePolynomial.PartialAction.OriginalEquations (1 / 2 : ℝ) (1 / 3)
      (fun i => NativePolynomial.upperCoordinates (stdAnchored q W i)) := by
  have hu' : uᴴ * u = 1 := mul_eq_one_comm.mp hu
  have hfr := anchf_frame u hu' q hq W hW
  have hpt : ∀ i : Fin 39, stdAnchored q W i =
      (fun t : Fin 3 => stdAnchored q W (framePointIndex ⟨i.val / 3, by omega⟩ t))
        ⟨i.val % 3, by omega⟩ := fun i => by
    simp only [framePointIndex_div_mod]
  have hpair : ∀ x y : Glennie.Albert,
      CoordinateMaps.coordinatePairing (upperCoordinates x) (upperCoordinates y) =
        Glennie.trace (Glennie.jordan x y) :=
    CoordinateMaps.coordinatePairing_upperCoordinates_eq_native_trace
  refine ⟨fun i => ?_, fun i => ?_, fun f => ?_, fun ij => ?_⟩
  · -- idempotency
    show CoordinateMaps.coordinateProduct (1 / 2 : ℝ) (upperCoordinates (stdAnchored q W i))
      (upperCoordinates (stdAnchored q W i)) = upperCoordinates (stdAnchored q W i)
    rw [CoordinateMaps.coordinateProduct_real_eq_native_coordinates (1/2 : ℝ) (by norm_num),
      fromUpperCoordinates_upperCoordinates, hpt i, (hfr ⟨i.val / 3, by omega⟩).idempotent]
  · -- trace one
    show CoordinateMaps.coordinateTrace (upperCoordinates (stdAnchored q W i)) = 1
    have h1 : Glennie.trace (stdAnchored q W i) = 1 := by
      rw [hpt i]
      exact (hfr ⟨i.val / 3, by omega⟩).trace_one ⟨i.val % 3, by omega⟩
    rw [CoordinateMaps.coordinateTrace_apply, ← h1]
    simp only [upperCoordinates, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Glennie.trace]
  · -- frame sums
    have hs := (hfr f).sum_unit
    show ∑ a : Fin 3, upperCoordinates (stdAnchored q W (framePointIndex f a)) = _
    rw [Fin.sum_univ_three, ← upperCoordinates_add, ← upperCoordinates_add, hs,
      QuadraticCertificate.ExactCKMFrameValueRows.upperCoordinates_unit_eq_coordinateUnit]
  · -- pairs
    obtain ⟨⟨i, j⟩, hij⟩ := ij
    change i < j at hij
    have hij' : i.val < j.val := hij
    show CoordinateMaps.coordinatePairing (upperCoordinates (stdAnchored q W i))
      (upperCoordinates (stdAnchored q W j)) = if i.val / 3 = j.val / 3 then 0 else 1 / 3
    rw [hpair]
    by_cases hj : j.val < 12
    · -- both in the quartet: compare with the seed
      have hi : i.val < 12 := by omega
      rw [anchf_std_vis q W i hi, anchf_std_vis q W j hj,
        anchf_trace_incl_conj u hu' _ _ _ _ (hq _ _) (hq _ _)]
      have h := seed_originalEquations.pair ⟨(i, j), hij⟩
      simp only [literalCfg, hpair] at h
      rw [anchf_literal_quartet _ i hi, anchf_literal_quartet _ j hj] at h
      exact h
    by_cases hf : i.val / 3 = j.val / 3
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hf)]
      have hfr' := hfr ⟨j.val / 3, by omega⟩
      have ho := hfr'.orthogonal ⟨i.val % 3, by omega⟩ ⟨j.val % 3, by omega⟩
        (by intro h; have := congrArg Fin.val h; simp only at this; omega)
      have hi' : framePointIndex ⟨j.val / 3, by omega⟩ ⟨i.val % 3, by omega⟩ = i := by
        apply Fin.ext
        show 3 * (j.val / 3) + i.val % 3 = i.val
        omega
      simp only [hi', framePointIndex_div_mod] at ho
      rw [ho]
      exact map_zero Glennie.traceLinear
    rw [ite_eq_right_of_eq_false _ _ (eq_false hf), anchf_std_hid q W j hj]
    by_cases hi : i.val < 12
    · -- quartet against hidden
      rw [anchf_std_vis q W i hi, Glennie.jordan_comm, native_trace_jordan_includeHermitianMatrix,
        hq]
      have h := quartet_complementary_trace (fun _ => 1) i hi
        ((UnitaryErrorBases.ThreeCycleFourier.omega ^ (j.val % 3)) •
          W (hiddenFrameEquiv.symm ⟨j.val / 3 - 4, by have := j.isLt; omega⟩))
      rw [anchf_literal_quartet _ i hi, Glennie.jordan_comm,
        native_trace_jordan_includeHermitianMatrix] at h
      rw [← h]
      have hp := nativeComplementaryPoint_pair
        ((UnitaryErrorBases.ThreeCycleFourier.omega ^ (j.val % 3)) •
          W (hiddenFrameEquiv.symm ⟨j.val / 3 - 4, by have := j.isLt; omega⟩))
      change toMatrixPair (toTitsCoordinates _) = _ at hp
      have hp1 := congrArg Prod.fst hp
      simp only [toMatrixPair] at hp1
      rw [hp1, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.one_mul,
        Matrix.trace_smul, Matrix.trace_smul, anchf_trace_conj u hu']
    · -- hidden against hidden
      rw [anchf_std_hid q W i hi]
      have hne : hiddenFrameEquiv.symm ⟨j.val / 3 - 4, by have := j.isLt; omega⟩ ≠
          hiddenFrameEquiv.symm ⟨i.val / 3 - 4, by have := i.isLt; omega⟩ := by
        intro h
        have := congrArg Fin.val (hiddenFrameEquiv.symm.injective h)
        simp only at this
        omega
      have h0 : ((UnitaryErrorBases.ThreeCycleFourier.omega ^ (i.val % 3) •
          W (hiddenFrameEquiv.symm ⟨i.val / 3 - 4, by have := i.isLt; omega⟩)) *
          (UnitaryErrorBases.ThreeCycleFourier.omega ^ (j.val % 3) •
          W (hiddenFrameEquiv.symm ⟨j.val / 3 - 4, by have := j.isLt; omega⟩))ᴴ : Mat).trace = 0 := by
        rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
          Matrix.trace_smul, Matrix.trace_mul_comm, hW.2 _ _ hne, smul_zero, smul_zero]
      have key : ∀ w : ℂ, w = 0 → (1 / 3 : ℝ) + 2 / 9 * w.re = 1 / 3 := fun w hw => by
        rw [hw]; simp
      exact (nativeComplementaryPoint_overlap _ _).trans (key _ h0)

end anchf_std

/-- **Original equations on the standard anchored form.** For a unitary conjugate `q` of the
standard complete quartet and any unitary error basis `W`, the 39 points `stdAnchored q W` satisfy
all original equations: field by field as A3's `literalCfg_originalEquations` (frames from
`native_central_triples_are_frames` and the conjugated quartet, quartet pairs from the seed,
quartet–hidden pairs from `native_trace_jordan_includeHermitianMatrix`, hidden–hidden pairs from
`nativeComplementaryPoint_overlap` and the UEB orthogonality `tr (W_pᴴ W_q) = 0`). -/
theorem originalEquations_stdAnchored (u : TitsComplexMatrix) (hu : u * uᴴ = 1)
    (q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian})
    (hq : ∀ k t, (q k t).val = u * (stdQuartet k t).val * uᴴ)
    (W : Family) (hW : IsUnitaryErrorBasis W) :
    NativePolynomial.PartialAction.OriginalEquations (1 / 2 : ℝ) (1 / 3)
      (fun i => NativePolynomial.upperCoordinates (stdAnchored q W i)) :=
  anchf_originalEquations_std u hu q hq W hW

/-! ## Relabelling -/

private theorem anchf_pairing_comm (x y : Fin 27 → ℝ) :
    NativePolynomial.CoordinateMaps.coordinatePairing x y =
      NativePolynomial.CoordinateMaps.coordinatePairing y x := by
  unfold NativePolynomial.CoordinateMaps.coordinatePairing
  exact Finset.sum_congr rfl fun _ _ => mul_right_comm _ _ _

/-- The pair rows, read for any two distinct labels. -/
private theorem anchf_pair_ne {C : NativePolynomial.PartialAction.Configuration ℝ}
    (hC : NativePolynomial.PartialAction.OriginalEquations (1 / 2 : ℝ) (1 / 3) C)
    (i j : Fin 39) (hne : i ≠ j) :
    NativePolynomial.CoordinateMaps.coordinatePairing (C i) (C j) =
      if i.val / 3 = j.val / 3 then 0 else 1 / 3 := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact hC.pair ⟨(i, j), h⟩
  · rw [anchf_pairing_comm]
    have h' := hC.pair ⟨(j, i), h⟩
    simp only at h'
    rw [h']
    split_ifs with h1 h2 h2 <;> first | rfl | omega

private theorem anchf_relabel_div (fperm : Equiv.Perm (Fin 13)) (τ : Fin 13 → Equiv.Perm (Fin 3))
    (i : Fin 39) : (pointRelabel fperm τ i).val / 3 = (fperm ⟨i.val / 3, by omega⟩).val := by
  have h := pointRelabel_framePointIndex fperm τ ⟨i.val / 3, by omega⟩ ⟨i.val % 3, by omega⟩
  rw [framePointIndex_div_mod] at h
  rw [h, NativePolynomial.ConfigurationResiduals.framePointIndex_val]
  omega

private theorem anchf_relabel_frame_iff (fperm : Equiv.Perm (Fin 13))
    (τ : Fin 13 → Equiv.Perm (Fin 3)) (i j : Fin 39) :
    (pointRelabel fperm τ i).val / 3 = (pointRelabel fperm τ j).val / 3 ↔
      i.val / 3 = j.val / 3 := by
  rw [anchf_relabel_div, anchf_relabel_div, ← Fin.ext_iff, fperm.injective.eq_iff, Fin.mk.injEq]

section anchf_rel
open NativePolynomial NativePolynomial.ConfigurationResiduals

private theorem anchf_originalEquations_relabel (fperm : Equiv.Perm (Fin 13))
    (τ : Fin 13 → Equiv.Perm (Fin 3)) (C : NativePolynomial.PartialAction.Configuration ℝ) :
    NativePolynomial.PartialAction.OriginalEquations (1 / 2 : ℝ) (1 / 3) (C ∘ pointRelabel fperm τ) ↔
      NativePolynomial.PartialAction.OriginalEquations (1 / 2 : ℝ) (1 / 3) C := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun i => ?_, fun f => ?_, fun ij => ?_⟩
    · simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
        h.idempotent ((pointRelabel fperm τ).symm i)
    · simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
        h.trace_one ((pointRelabel fperm τ).symm i)
    · have hs := h.frame_sum (fperm.symm f)
      simp only [Function.comp_apply, pointRelabel_framePointIndex, Equiv.apply_symm_apply] at hs
      rw [← hs]
      exact (Equiv.sum_comp (τ (fperm.symm f)) (fun a => C (framePointIndex f a))).symm
    · obtain ⟨⟨i, j⟩, hij⟩ := ij
      have hij' : i ≠ j := ne_of_lt hij
      show CoordinateMaps.coordinatePairing (C i) (C j) = if i.val / 3 = j.val / 3 then 0 else 1 / 3
      have hne : (pointRelabel fperm τ).symm i ≠ (pointRelabel fperm τ).symm j :=
        fun e => hij' ((pointRelabel fperm τ).symm.injective e)
      have h' := anchf_pair_ne h _ _ hne
      simp only [Function.comp_apply, Equiv.apply_symm_apply] at h'
      rw [h']
      have hiff := anchf_relabel_frame_iff fperm τ ((pointRelabel fperm τ).symm i)
        ((pointRelabel fperm τ).symm j)
      simp only [Equiv.apply_symm_apply] at hiff
      by_cases hc : i.val / 3 = j.val / 3
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_left_of_eq_true _ _ (eq_true (hiff.mp hc))]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hc),
          ite_eq_right_of_eq_false _ _ (eq_false (fun e => hc (hiff.mpr e)))]
  · intro h
    refine ⟨fun i => h.idempotent _, fun i => h.trace_one _, fun f => ?_, fun ij => ?_⟩
    · simp only [Function.comp_apply, pointRelabel_framePointIndex]
      rw [Equiv.sum_comp (τ f) (fun a => C (framePointIndex (fperm f) a))]
      exact h.frame_sum (fperm f)
    · obtain ⟨⟨i, j⟩, hij⟩ := ij
      have hij' : i ≠ j := ne_of_lt hij
      show CoordinateMaps.coordinatePairing (C (pointRelabel fperm τ i))
        (C (pointRelabel fperm τ j)) = if i.val / 3 = j.val / 3 then 0 else 1 / 3
      have hne : pointRelabel fperm τ i ≠ pointRelabel fperm τ j :=
        fun e => hij' ((pointRelabel fperm τ).injective e)
      rw [anchf_pair_ne h _ _ hne]
      have hiff := anchf_relabel_frame_iff fperm τ i j
      by_cases hc : i.val / 3 = j.val / 3
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_left_of_eq_true _ _ (eq_true (hiff.mpr hc))]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hc),
          ite_eq_right_of_eq_false _ _ (eq_false (fun e => hc (hiff.mp e)))]

end anchf_rel

/-- **Frame-preserving relabelling preserves the original equations**: idempotency and trace rows
are permuted, each frame sum is a frame sum (reordered by `τ f`), and pairs keep the same-frame
relation. -/
theorem originalEquations_pointRelabel (fperm : Equiv.Perm (Fin 13)) (τ : Fin 13 → Equiv.Perm (Fin 3))
    (C : NativePolynomial.PartialAction.Configuration ℝ) :
    NativePolynomial.PartialAction.OriginalEquations (1 / 2 : ℝ) (1 / 3) (C ∘ pointRelabel fperm τ) ↔
      NativePolynomial.PartialAction.OriginalEquations (1 / 2 : ℝ) (1 / 3) C :=
  anchf_originalEquations_relabel fperm τ C

/-! ## Pullback and saturation -/

private theorem anchf_relabel_exists (H : Fin 4) :
    ∃ (fperm : Equiv.Perm (Fin 13)) (τ : Fin 13 → Equiv.Perm (Fin 3)),
      anchorRelabel H = pointRelabel fperm τ := by
  fin_cases H <;> exact ⟨_, _, rfl⟩

private theorem anchf_originalF_of_OE {C : Cfg}
    (h : NativePolynomial.PartialAction.OriginalEquations (1 / 2 : ℝ) (1 / 3) C) :
    Option2.NativeStress.AnalyticDerivative.originalF C = 0 := by
  funext r
  exact (NativePolynomial.PartialAction.originalEquations_iff_all_fRows _ _ _).mp h r

private theorem anchf_Ψinv_mem (H : Fin 4) : coordEnd (anchorΨinv H) ∈ autC := by
  rw [mem_autC_iff_isNativeAut, AlgEquiv.symm_apply_apply]
  refine ⟨Function.bijective_iff_has_inverse.mpr ⟨anchorΨ H, fun x => ?_, fun x => ?_⟩,
    anchorΨinv_isNativeAut H⟩
  · exact LinearMap.congr_fun (anchorΨ_comp_anchorΨinv H) x
  · exact LinearMap.congr_fun (anchorΨinv_comp_anchorΨ H) x

/-- The raw family satisfies all original equations: the relabelled standard anchored form
(`originalEquations_stdAnchored`, `originalEquations_pointRelabel`) pulled back by the native
automorphism `anchorΨinv H` (`originalF_actC_eq_zero_iff`). -/
theorem originalF_preCfg {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) {g h : Mat}
    (hg : g ∈ Matrix.specialUnitaryGroup Index ℂ) (hh : h ∈ Matrix.specialUnitaryGroup Index ℂ)
    (d : PhaseTriple) :
    Option2.NativeStress.AnalyticDerivative.originalF (preCfg ξ₀ H g h d) = 0 := by
  obtain ⟨fperm, τ, hrel⟩ := anchf_relabel_exists H
  have hOE := originalEquations_stdAnchored (quartetConj ξ₀ H) (quartetConj_unitary hξ₀ H)
    (anchorQuartet ξ₀ H) (anchorQuartet_val ξ₀ H) _ (isUnitaryErrorBasis_hidFamily hξ₀ H hg hh d)
  have hOE1 : NativePolynomial.PartialAction.OriginalEquations (1 / 2 : ℝ) (1 / 3)
      ((fun i => NativePolynomial.upperCoordinates
        (stdAnchored (anchorQuartet ξ₀ H) (hidFamily ξ₀ H g h d) i)) ∘ (anchorRelabel H).symm) := by
    rw [← originalEquations_pointRelabel fperm τ, ← hrel]
    convert hOE using 1
    funext i
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
  have hpre : preCfg ξ₀ H g h d = actC (coordEnd (anchorΨinv H))
      ((fun i => NativePolynomial.upperCoordinates
        (stdAnchored (anchorQuartet ξ₀ H) (hidFamily ξ₀ H g h d) i)) ∘ (anchorRelabel H).symm) := by
    funext i
    rw [actC_apply, coordEnd_apply]
    simp only [preCfg, prePoint, Function.comp_apply,
      NativePolynomial.fromUpperCoordinates_upperCoordinates]
  rw [hpre, originalF_actC_eq_zero_iff (anchf_Ψinv_mem H)]
  exact anchf_originalF_of_OE hOE1

/-- `G`-saturation of the raw family (`groupChart_mem_autC`, `suExp_mem_specialUnitaryGroup`). -/
theorem originalF_rawMap {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) (p : RawParam) :
    Option2.NativeStress.AnalyticDerivative.originalF (rawMap ξ₀ hξ₀ H p) = 0 := by
  rw [rawMap, originalF_actC_eq_zero_iff (groupChart_mem_autC p.1), preMap]
  exact originalF_preCfg hξ₀ H (suExp_mem_specialUnitaryGroup _) (suExp_mem_specialUnitaryGroup _) _

/-- `G`-saturation of the literal phase family (A3's `literalCfg_all_original_F`; the phases
`ξ₀ · e^{iθ}` are unit phases). -/
theorem originalF_commonMap {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (p : CommonParam) :
    Option2.NativeStress.AnalyticDerivative.originalF (commonMap ξ₀ p) = 0 := by
  rw [commonMap, originalF_actC_eq_zero_iff (groupChart_mem_autC p.1)]
  have hu : IsUnitPhase (commonPhase ξ₀ p.2) := fun a => by
    rw [commonPhase, map_mul, hξ₀ a, one_mul, Complex.normSq_eq_norm_sq,
      Complex.norm_exp_ofReal_mul_I, one_pow]
  funext r
  exact literalCfg_all_original_F _ hu r

end CKM.NativeFourFamily

#print axioms CKM.NativeFourFamily.isUnitaryErrorBasis_hidFamily
#print axioms CKM.NativeFourFamily.originalEquations_stdAnchored
#print axioms CKM.NativeFourFamily.originalEquations_pointRelabel
#print axioms CKM.NativeFourFamily.originalF_preCfg
#print axioms CKM.NativeFourFamily.originalF_rawMap
#print axioms CKM.NativeFourFamily.originalF_commonMap
