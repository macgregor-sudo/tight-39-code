module

public import A3PhaseTriples
public import NativeExactCKMThreeHiddenFrames
public import NativeExactCKMABFrames
public import NativeExactCKMCDFrames
public import A3FamilyCross
public import NativeExactCKMAllF
public import NativeExactCKMAllFrames
public import NativeExactCKMFrameValueRows
public import NativeCoordinateTracePairing
public import NativeOriginalGIdempotencyDifferential

@[expose] public section

/-!
# The literal all-phase family: seed binding, standard Tits forms, all original equations
-/

noncomputable section

namespace CKM.NativeFirstOrder

open NativePolynomial NativePolynomial.ConfigurationResiduals CompactAlbert
open UnitaryErrorBases.ComplexQuartet

/-- Hidden matrices of the standard picture: group `g` (frames `4 + 3g + s`), outcome `t`. -/
def hiddenMatrix (ξ : Fin 4 → ℂ) (g : Fin 3) (s t : PhaseIndex) : TitsComplexMatrix :=
  match g with
  | 0 => QuadraticCertificate.ExactCKMThreeHiddenFrames.twoInputMatrix
      (UnitaryErrorBases.ThreeCycleFourier.character t)
      (UnitaryErrorBases.ThreeCycleFourier.character (s + t))
  | 1 => QuadraticCertificate.ExactCKMABFrames.ellNMatrix
      (ξ 0 * UnitaryErrorBases.ThreeCycleFourier.character t)
      (ξ 1 * UnitaryErrorBases.ThreeCycleFourier.character (s + t))
  | 2 => QuadraticCertificate.ExactCKMCDFrames.njMatrix
      (ξ 2 * UnitaryErrorBases.ThreeCycleFourier.character t)
      (ξ 3 * UnitaryErrorBases.ThreeCycleFourier.character (s + t))

theorem literalPoint_exactPhases :
    literalPoint QuadraticCertificate.ExactCKMConfiguration.exactPhases =
      QuadraticCertificate.ExactCKMConfiguration.nativePoint := by
  funext i
  rfl

/-! ## Index decoding of the literal family -/

theorem literalPoint_of_ge (ξ : Fin 4 → ℂ) (i : Fin 39) (h : 3 ≤ i.val) :
    literalPoint ξ i = literalFamilyPoint ξ ⟨(i.val - 3) / 9, by have := i.isLt; omega⟩
      (((i.val - 3) % 9 / 3 : ℕ) : PhaseIndex) (((i.val - 3) % 3 : ℕ) : PhaseIndex) := by
  unfold literalPoint
  split_ifs with h'
  · omega
  · rfl

/-- A point `12 + 9g + 3s + t` is the family point of group `g + 1`. -/
theorem literalPoint_eq_family (ξ : Fin 4 → ℂ) (g : Fin 3) (s t : PhaseIndex) (i : Fin 39)
    (hi : i.val = 12 + 9 * g.val + 3 * s.val + t.val) :
    literalPoint ξ i = literalFamilyPoint ξ g.succ s t := by
  have hs := ZMod.val_lt s
  have ht := ZMod.val_lt t
  have hg := g.isLt
  rw [literalPoint_of_ge ξ i (by omega)]
  have e0 : (⟨(i.val - 3) / 9, by have := i.isLt; omega⟩ : Fin 4) = g.succ := by
    apply Fin.ext
    simp only [Fin.val_succ]
    omega
  have e1 : (i.val - 3) % 9 / 3 = s.val := by omega
  have e2 : (i.val - 3) % 3 = t.val := by omega
  rw [e0, e1, e2, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

/-- The three hidden branches, through the phase-generic native binders. -/
theorem literalFamilyPoint_hidden (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (g : Fin 3)
    (s t : PhaseIndex) :
    literalFamilyPoint ξ g.succ s t = nativeComplementaryPoint (hiddenMatrix ξ g s t) := by
  fin_cases g
  · show literalFamilyPoint ξ 1 s t = _
    rw [literalFamilyPoint, ite_eq_right (by decide), ite_eq_left rfl]
    exact QuadraticCertificate.ExactCKMThreeHiddenFrames.nativeOuterProduct_j_ell_eq_complementary
      _ _ (character_normSq_eq_one t) (character_normSq_eq_one _)
  · show literalFamilyPoint ξ 2 s t = _
    rw [literalFamilyPoint, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
    exact QuadraticCertificate.ExactCKMABFrames.nativeOuterProduct_ell_n_eq_complementary _ _
      (FamilyCross.normSq_unit_mul_character _ (hξ 0) t)
      (FamilyCross.normSq_unit_mul_character _ (hξ 1) _)
  · show literalFamilyPoint ξ 3 s t = _
    rw [literalFamilyPoint, ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_right (by decide)]
    exact QuadraticCertificate.ExactCKMCDFrames.nativeOuterProduct_n_j_eq_complementary _ _
      (FamilyCross.normSq_unit_mul_character _ (hξ 2) t)
      (FamilyCross.normSq_unit_mul_character _ (hξ 3) _)

/-- Frames 0–3 are the standard complex quartet, at every phase. -/
theorem literalPoint_quartet (ξ : Fin 4 → ℂ) (k : Fin 4) (t : Fin 3) :
    literalPoint ξ (framePointIndex (Fin.castLE (by omega) k) t) =
      includeHermitianMatrix (stdQuartet k t) := by
  fin_cases k <;> fin_cases t
  all_goals first
    | (exact literalNativeCoordinatePoint_eq_included _)
    | (exact literalNativePhasePoint_eq_included _ _)

/-- Frames 4–12 are complementary points of explicit monomial matrices, at every unit phase. -/
theorem literalPoint_hidden (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (g : Fin 3) (s t : PhaseIndex) :
    literalPoint ξ (framePointIndex ⟨4 + 3 * g.val + s.val, by have := ZMod.val_lt s; omega⟩ t) =
      nativeComplementaryPoint (hiddenMatrix ξ g s t) := by
  rw [literalPoint_eq_family ξ g s t _
      (by show 3 * (4 + 3 * g.val + s.val) + ZMod.val t = _; ring),
    literalFamilyPoint_hidden ξ hξ]

/-! ## Phase-free points: the first twenty-one points are the seed points -/

theorem literalPoint_low (ξ : Fin 4 → ℂ) (i : Fin 39) (hi : i.val < 21) :
    literalPoint ξ i = QuadraticCertificate.ExactCKMConfiguration.nativePoint i := by
  unfold literalPoint QuadraticCertificate.ExactCKMConfiguration.nativePoint
  split_ifs with h
  · rfl
  · dsimp only
    unfold literalFamilyPoint QuadraticCertificate.ExactCKMConfiguration.nativeFamilyPoint
    split_ifs with h0 h1
    · rfl
    · rfl
    all_goals
      exfalso
      rcases (show (i.val - 3) / 9 = 0 ∨ (i.val - 3) / 9 = 1 by omega) with e | e
      · exact h0 (Fin.ext e)
      · exact h1 (Fin.ext e)

/-- Decoding of the hidden points `i ≥ 12`. -/
theorem hidden_decode (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (i : Fin 39) (hi : 12 ≤ i.val) :
    ∃ (g : Fin 3) (s t : PhaseIndex), i.val / 3 = 4 + 3 * g.val + s.val ∧
      literalPoint ξ i = nativeComplementaryPoint (hiddenMatrix ξ g s t) := by
  have hi39 := i.isLt
  let g : Fin 3 := ⟨(i.val - 12) / 9, by omega⟩
  let s : PhaseIndex := (((i.val - 12) % 9 / 3 : ℕ) : PhaseIndex)
  let t : PhaseIndex := (((i.val - 12) % 3 : ℕ) : PhaseIndex)
  have hs : s.val = (i.val - 12) % 9 / 3 := by simp only [s, ZMod.val_natCast]; omega
  have ht : t.val = (i.val - 12) % 3 := by simp only [t, ZMod.val_natCast]; omega
  have hg : g.val = (i.val - 12) / 9 := rfl
  refine ⟨g, s, t, by omega, ?_⟩
  rw [literalPoint_eq_family ξ g s t i (by omega)]
  exact literalFamilyPoint_hidden ξ hξ g s t

/-! ## Frames -/

theorem literal_low_frame (ξ : Fin 4 → ℂ) (f : Fin 13) (hf : f.val < 7) :
    Glennie.Frame (fun t : Fin 3 => literalPoint ξ (framePointIndex f t)) := by
  have h : (fun t : Fin 3 => literalPoint ξ (framePointIndex f t)) =
      fun t => QuadraticCertificate.ExactCKMConfiguration.nativePoint (framePointIndex f t) := by
    funext t
    apply literalPoint_low
    show 3 * f.val + t.val < 21
    omega
  rw [h]
  exact QuadraticCertificate.ExactCKMAllFrames.nativePoint_all_frames f

/-- A hidden frame of group `1` or `2` is the reverse central triple of a special unitary. -/
theorem hidden_frame (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (g : Fin 3) (hg : g ≠ 0)
    (s : PhaseIndex) :
    Glennie.Frame (fun t : Fin 3 => nativeComplementaryPoint (hiddenMatrix ξ g s t)) := by
  have key : ∃ U : TitsComplexMatrix,
      (U * U.conjTranspose = 1 ∧ U.det = 1) ∧
        ∀ t, hiddenMatrix ξ g s t =
          star (UnitaryErrorBases.ThreeCycleFourier.character t) • U := by
    fin_cases g
    · exact absurd rfl hg
    · refine ⟨_, QuadraticCertificate.ExactCKMABFrames.ellNMatrix_specialUnitary _ _
        (FamilyCross.mul_star_of_normSq _ (FamilyCross.normSq_unit_mul_character _ (hξ 0) 0))
        (FamilyCross.mul_star_of_normSq _
          (FamilyCross.normSq_unit_mul_character _ (hξ 1) (s + 0))), fun t => ?_⟩
      exact FamilyCross.ellN_scaling (ξ 0) (ξ 1) s t
    · refine ⟨_, QuadraticCertificate.ExactCKMCDFrames.njMatrix_specialUnitary _ _
        (FamilyCross.mul_star_of_normSq _ (FamilyCross.normSq_unit_mul_character _ (hξ 2) 0))
        (FamilyCross.mul_star_of_normSq _
          (FamilyCross.normSq_unit_mul_character _ (hξ 3) (s + 0))), fun t => ?_⟩
      exact FamilyCross.nj_scaling (ξ 2) (ξ 3) s t
  obtain ⟨U, hU, hM⟩ := key
  have htriple : (fun t : Fin 3 => nativeComplementaryPoint (hiddenMatrix ξ g s t)) =
      nativeReverseCentralTriple U := by
    funext t
    fin_cases t
    · show nativeComplementaryPoint (hiddenMatrix ξ g s 0) = nativeComplementaryPoint U
      rw [hM, FamilyCross.character_zero, star_one, one_smul]
    · show nativeComplementaryPoint (hiddenMatrix ξ g s 1) =
        nativeComplementaryPoint ((UnitaryErrorBases.ThreeCycleFourier.omega ^ 2) • U)
      rw [hM, FamilyCross.character_one, FamilyCross.star_omega]
    · show nativeComplementaryPoint (hiddenMatrix ξ g s 2) =
        nativeComplementaryPoint (UnitaryErrorBases.ThreeCycleFourier.omega • U)
      rw [hM, FamilyCross.character_two, FamilyCross.star_omega_sq]
  rw [htriple]
  exact (native_central_triples_are_frames U hU).2

/-- Every one of the thirteen frames of the literal family is a native Jordan frame. -/
theorem literal_frame (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (f : Fin 13) :
    Glennie.Frame (fun t : Fin 3 => literalPoint ξ (framePointIndex f t)) := by
  by_cases hf : f.val < 7
  · exact literal_low_frame ξ f hf
  · have hf13 := f.isLt
    let g : Fin 3 := ⟨(f.val - 4) / 3, by omega⟩
    let s : PhaseIndex := (((f.val - 4) % 3 : ℕ) : PhaseIndex)
    have hg : g ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp only [g, Fin.val_zero] at this
      omega
    have hs : s.val = (f.val - 4) % 3 := by simp only [s, ZMod.val_natCast]; omega
    have hgv : g.val = (f.val - 4) / 3 := rfl
    have h : (fun t : Fin 3 => literalPoint ξ (framePointIndex f t)) =
        fun t : Fin 3 => nativeComplementaryPoint (hiddenMatrix ξ g s t) := by
      funext t
      have ht : (framePointIndex f t).val = 12 + 9 * g.val + 3 * s.val + ZMod.val (n := 3) t := by
        show 3 * f.val + t.val = _
        rw [hs, hgv]
        show 3 * f.val + t.val = _ + t.val
        omega
      rw [literalPoint_eq_family ξ g s t _ ht]
      exact literalFamilyPoint_hidden ξ hξ g s t
    rw [h]
    exact hidden_frame ξ hξ g hg s

/-! ## Cross overlaps -/

/-- Quartet against hidden: `1/3` for every hidden matrix. -/
theorem quartet_complementary_trace (ξ : Fin 4 → ℂ) (i : Fin 39) (hi : i.val < 12)
    (U : TitsComplexMatrix) :
    Glennie.trace (Glennie.jordan (literalPoint ξ i) (nativeComplementaryPoint U)) = 1 / 3 := by
  rw [Glennie.jordan_comm]
  unfold literalPoint
  split_ifs with h
  · exact (nativeComplementaryPoint_literal_readouts U).1 _
  · dsimp only
    rw [literalFamilyPoint, ite_eq_left (Fin.ext (show (i.val - 3) / 9 = 0 by omega))]
    exact (nativeComplementaryPoint_literal_readouts U).2 _ _

/-- Hidden against hidden in distinct frames: the complex cross trace vanishes, symbolically in
the unit phases. -/
theorem hidden_trace_zero (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (g g' : Fin 3)
    (s s' t t' : PhaseIndex) (h : g ≠ g' ∨ s ≠ s') :
    (hiddenMatrix ξ g s t * (hiddenMatrix ξ g' s' t').conjTranspose).trace = 0 := by
  have hu : ∀ a, ξ a * star (ξ a) = 1 := fun a => FamilyCross.mul_star_of_normSq _ (hξ a)
  have cases3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases cases3 g with rfl | rfl | rfl <;> rcases cases3 g' with rfl | rfl | rfl
  · have hs := h.resolve_left (fun h => h rfl)
    show (QuadraticCertificate.ExactCKMThreeHiddenFrames.twoInputMatrix _ _ *
      (QuadraticCertificate.ExactCKMThreeHiddenFrames.twoInputMatrix _ _).conjTranspose).trace = 0
    rw [FamilyCross.trace_twoInput_twoInput]
    simpa only [one_mul] using
      FamilyCross.pattern_sum_zero 1 1 (by simp only [star_one, mul_one])
        (by simp only [star_one, mul_one]) s t s' t' hs
  · exact FamilyCross.trace_twoInput_ellN _ _ _ _
  · exact FamilyCross.trace_twoInput_nj _ _ _ _
  · exact FamilyCross.trace_ellN_twoInput _ _ _ _
  · have hs := h.resolve_left (fun h => h rfl)
    show (QuadraticCertificate.ExactCKMABFrames.ellNMatrix _ _ *
      (QuadraticCertificate.ExactCKMABFrames.ellNMatrix _ _).conjTranspose).trace = 0
    rw [FamilyCross.trace_ellN_ellN]
    exact FamilyCross.pattern_sum_zero _ _ (hu 0) (hu 1) s t s' t' hs
  · exact FamilyCross.trace_ellN_nj _ _ _ _
  · exact FamilyCross.trace_nj_twoInput _ _ _ _
  · exact FamilyCross.trace_nj_ellN _ _ _ _
  · have hs := h.resolve_left (fun h => h rfl)
    show (QuadraticCertificate.ExactCKMCDFrames.njMatrix _ _ *
      (QuadraticCertificate.ExactCKMCDFrames.njMatrix _ _).conjTranspose).trace = 0
    rw [FamilyCross.trace_nj_nj]
    exact FamilyCross.pattern_sum_zero _ _ (hu 2) (hu 3) s t s' t' hs

/-! ## The configuration equations -/

theorem pack_literalCfg_exactPhases :
    PartialAction.pack (literalCfg QuadraticCertificate.ExactCKMConfiguration.exactPhases) =
      QuadraticCertificate.ExactCKMConfiguration.pointCoordinates := by
  funext v
  rfl

theorem seed_originalEquations :
    PartialAction.OriginalEquations (1/2 : ℝ) (1/3 : ℝ)
      (literalCfg QuadraticCertificate.ExactCKMConfiguration.exactPhases) :=
  (PartialAction.originalEquations_iff_all_fRows _ _ _).mpr fun r => by
    rw [pack_literalCfg_exactPhases]
    exact QuadraticCertificate.ExactCKMAllF.all_fRow_eval_zero r

theorem literalCfg_low (ξ : Fin 4 → ℂ) (i : Fin 39) (hi : i.val < 21) :
    literalCfg ξ i = literalCfg QuadraticCertificate.ExactCKMConfiguration.exactPhases i := by
  simp only [literalCfg, literalPoint_low ξ i hi, literalPoint_low _ i hi]

theorem framePointIndex_div_mod (i : Fin 39) :
    framePointIndex ⟨i.val / 3, by omega⟩ ⟨i.val % 3, by omega⟩ = i := by
  apply Fin.ext
  show 3 * (i.val / 3) + i.val % 3 = i.val
  omega

theorem literalCfg_originalEquations (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    PartialAction.OriginalEquations (1/2 : ℝ) (1/3 : ℝ) (literalCfg ξ) := by
  have hpt : ∀ i : Fin 39, literalPoint ξ i =
      (fun t : Fin 3 => literalPoint ξ (framePointIndex ⟨i.val / 3, by omega⟩ t))
        ⟨i.val % 3, by omega⟩ := fun i => by
    simp only [framePointIndex_div_mod]
  have hpair : ∀ x y : Glennie.Albert,
      CoordinateMaps.coordinatePairing (upperCoordinates x) (upperCoordinates y) =
        Glennie.trace (Glennie.jordan x y) :=
    CoordinateMaps.coordinatePairing_upperCoordinates_eq_native_trace
  refine ⟨fun i => ?_, fun i => ?_, fun f => ?_, fun ij => ?_⟩
  · -- idempotency
    simp only [literalCfg]
    rw [CoordinateMaps.coordinateProduct_real_eq_native_coordinates (1/2 : ℝ) (by norm_num),
      fromUpperCoordinates_upperCoordinates, hpt i,
      (literal_frame ξ hξ ⟨i.val / 3, by omega⟩).idempotent]
  · -- trace one
    simp only [literalCfg]
    have h1 : Glennie.trace (literalPoint ξ i) = 1 := by
      rw [hpt i]
      exact (literal_frame ξ hξ ⟨i.val / 3, by omega⟩).trace_one ⟨i.val % 3, by omega⟩
    rw [CoordinateMaps.coordinateTrace_apply, ← h1]
    simp only [upperCoordinates, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Glennie.trace]
  · -- frame sums
    have hs := (literal_frame ξ hξ f).sum_unit
    simp only [literalCfg, Fin.sum_univ_three]
    rw [← upperCoordinates_add, ← upperCoordinates_add, hs,
      QuadraticCertificate.ExactCKMFrameValueRows.upperCoordinates_unit_eq_coordinateUnit]
  · -- pairs
    obtain ⟨⟨i, j⟩, hij⟩ := ij
    change i < j at hij
    have hij' : i.val < j.val := hij
    simp only
    by_cases hj : j.val < 21
    · have h := seed_originalEquations.pair ⟨(i, j), hij⟩
      simp only at h
      rw [literalCfg_low ξ i (by omega), literalCfg_low ξ j hj]
      exact h
    simp only [literalCfg, hpair]
    by_cases hf : i.val / 3 = j.val / 3
    · rw [ite_eq_left hf]
      have hfr := literal_frame ξ hξ ⟨j.val / 3, by omega⟩
      have ho := hfr.orthogonal ⟨i.val % 3, by omega⟩ ⟨j.val % 3, by omega⟩
        (by intro h; have := congrArg Fin.val h; simp only at this; omega)
      have hi' : framePointIndex ⟨j.val / 3, by omega⟩ ⟨i.val % 3, by omega⟩ = i := by
        apply Fin.ext
        show 3 * (j.val / 3) + i.val % 3 = i.val
        omega
      simp only [hi', framePointIndex_div_mod] at ho
      rw [ho]
      exact map_zero Glennie.traceLinear
    rw [ite_eq_right hf]
    obtain ⟨g', s', t', hj3, hjp⟩ := hidden_decode ξ hξ j (by omega)
    rw [hjp]
    by_cases hi : i.val < 12
    · exact quartet_complementary_trace ξ i hi _
    obtain ⟨g, s, t, hi3, hip⟩ := hidden_decode ξ hξ i (by omega)
    rw [hip, nativeComplementaryPoint_overlap]
    have hne : g ≠ g' ∨ s ≠ s' := by
      by_cases hgg : g = g'
      · right
        rintro rfl
        subst hgg
        exact hf (hi3.trans hj3.symm)
      · exact Or.inl hgg
    rw [hidden_trace_zero ξ hξ g g' s s' t t' hne, Complex.zero_re, mul_zero, add_zero]

/-- All 2184 original residual rows vanish at the literal configuration, at every unit phase. -/
theorem literalCfg_all_original_F (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (r : Fin 2184) :
    MvPolynomial.eval (PartialAction.pack (literalCfg ξ)) (fRow (1/2 : ℝ) (1/3 : ℝ) r) = 0 := by
  exact (PartialAction.originalEquations_iff_all_fRows _ _ _).mp
    (literalCfg_originalEquations ξ hξ) r

end CKM.NativeFirstOrder

