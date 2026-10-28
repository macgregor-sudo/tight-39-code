module

public import A5Analytic
public import A5Fixer

@[expose] public section

/-!
# The derivative kernel of the saturated family is the right gauge (piece RANK)

`preDer` is injective on all eighteen parameters at every unit phase (MASTER §6.7: the identity label
gives `X = Y`-type agreement, the clock and shift labels force a scalar, tracelessness kills it, then
the `(0,2)` label kills the torus direction). An element `(D, X, Y, e)` of `ker rawDer` has
`D` vanishing on the quartet points (`preVar` does not move them), so `D = gaugeDer H k`
(`mem_quartetFixer_iff`); `gaugeDer H k • P = -preDer (0, k, 0)` then forces `(X, Y, e) = (0, k, 0)`.
Hence the kernel is exactly the eight-dimensional right gauge, and the complement `h = 1` gives an
injective 62-parameter derivative.
-/

noncomputable section

open CKM.NativeFirstOrder CKM.NativeGroupSlice CompactAlbert UnitaryErrorBases
open scoped Matrix Topology

namespace CKM.NativeFourFamily

/-! ## Elementary rank helpers -/

private lemma rank_indexCases (i : Index) : i = 0 ∨ i = 1 ∨ i = 2 :=
  (by decide : ∀ j : Index, j = 0 ∨ j = 1 ∨ j = 2) i

@[simp] private lemma rank_val0 : (0 : Index).val = 0 := rfl
@[simp] private lemma rank_val1 : (1 : Index).val = 1 := rfl
@[simp] private lemma rank_val2 : (2 : Index).val = 2 := rfl

private lemma rank_sum_three (f : Index → ℂ) : ∑ i, f i = f 0 + f 1 + f 2 :=
  Fin.sum_univ_three f

private lemma rank_omega_im : UnitaryErrorBases.omega.im = Real.sqrt 3 / 2 := by
  simp [UnitaryErrorBases.omega]

private lemma rank_omega_sq : UnitaryErrorBases.omega ^ 2 = -1 - UnitaryErrorBases.omega :=
  ThreeCycleFourier.omega_sq

private lemma rank_omega_pow_ne (i j : Index) (hij : i ≠ j) :
    UnitaryErrorBases.omega ^ i.val ≠ UnitaryErrorBases.omega ^ j.val := by
  have hs : 0 < Real.sqrt 3 := by positivity
  have i0 : (UnitaryErrorBases.omega ^ (0 : Index).val).im = 0 := by simp
  have i1 : (UnitaryErrorBases.omega ^ (1 : Index).val).im = Real.sqrt 3 / 2 := by
    rw [rank_val1, pow_one, rank_omega_im]
  have i2 : (UnitaryErrorBases.omega ^ (2 : Index).val).im = -(Real.sqrt 3 / 2) := by
    rw [rank_val2, rank_omega_sq, Complex.sub_im, rank_omega_im]
    simp
  intro h
  have him := congrArg Complex.im h
  rcases rank_indexCases i with rfl | rfl | rfl <;> rcases rank_indexCases j with rfl | rfl | rfl <;>
    simp only [i0, i1, i2] at him <;> first | exact hij rfl | linarith

/-- A matrix commuting with clock and shift, of trace zero, vanishes. -/
private lemma rank_scalar_zero (M : Mat) (hc : M * clock = clock * M) (hs : M * shift = shift * M)
    (ht : M.trace = 0) : M = 0 := by
  have hc' : ∀ i j, M i j * (UnitaryErrorBases.omega ^ j.val - UnitaryErrorBases.omega ^ i.val) = 0 := by
    intro i j
    have := congrFun (congrFun hc i) j
    simp only [clock, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    rw [mul_sub, this]
    ring
  have hoff : ∀ i j, i ≠ j → M i j = 0 := fun i j hij =>
    (mul_eq_zero.mp (hc' i j)).resolve_right (sub_ne_zero.mpr (rank_omega_pow_ne j i (Ne.symm hij)))
  have hs' : ∀ i j, M i (j + 1) = M (i - 1) j := by
    intro i j
    rw [← ThreeCycleMatrix.mul_shift_apply M i j, ← ThreeCycleMatrix.shift_mul_apply M i j, hs]
  have hd : ∀ j : Index, M (j + 1) (j + 1) = M j j := fun j => by rw [hs', add_sub_cancel_right]
  have htr : M 0 0 + M 1 1 + M 2 2 = 0 := by
    rw [← ht, Matrix.trace, rank_sum_three]
    rfl
  have e1 : M 1 1 = M 0 0 := hd 0
  have e2 : M 2 2 = M 1 1 := hd 1
  have e0 : M 0 0 = 0 := by
    rw [e2, e1] at htr
    have : (3 : ℂ) * M 0 0 = 0 := by rw [← htr]; ring
    simpa using this
  ext i j
  by_cases hij : i = j
  · subst hij
    rcases rank_indexCases i with rfl | rfl | rfl
    · exact e0
    · rw [e1, e0]; rfl
    · rw [e2, e1, e0]; rfl
  · exact hoff i j hij

private lemma rank_hiddenVec_pair (U : TitsComplexMatrix) :
    nativeTitsMatrixPair (hiddenVec U) = (0, (1 / 3 : ℂ) • U) :=
  Elim.mkPoint_pair _ _ _

private lemma rank_hiddenVec_add (U V : TitsComplexMatrix) :
    hiddenVec U + hiddenVec V = hiddenVec (U + V) := by
  apply nativeTitsMatrixPair_injective
  rw [map_add, rank_hiddenVec_pair, rank_hiddenVec_pair, rank_hiddenVec_pair]
  ext <;> simp [mul_add]

private lemma rank_hiddenVec_zero : hiddenVec 0 = 0 := by
  apply nativeTitsMatrixPair_injective
  rw [map_zero, rank_hiddenVec_pair, smul_zero]
  rfl

private lemma rank_hiddenVec_eq_zero {U : TitsComplexMatrix} (h : hiddenVec U = 0) : U = 0 := by
  have := congrArg (fun x => (nativeTitsMatrixPair x).2) h
  simp only [rank_hiddenVec_pair, map_zero, Prod.snd_zero] at this
  have h3 : (3 : ℂ) • ((1 / 3 : ℂ) • U) = 0 := by rw [this, smul_zero]
  rwa [smul_smul, show (3 : ℂ) * (1 / 3) = 1 by norm_num, one_smul] at h3

private lemma rank_uc_zero : NativePolynomial.upperCoordinates 0 = 0 :=
  NativePolynomial.upperCoordinateEquiv.map_zero

private lemma rank_uc_injective : Function.Injective NativePolynomial.upperCoordinates :=
  NativePolynomial.upperCoordinateEquiv.injective

private lemma rank_Ψ_Ψinv (H : Fin 4) (x : Glennie.Albert) : anchorΨ H (anchorΨinv H x) = x :=
  LinearMap.congr_fun (anchorΨ_comp_anchorΨinv H) x

private lemma rank_Ψinv_eq_zero {H : Fin 4} {x : Glennie.Albert} (h : anchorΨinv H x = 0) : x = 0 := by
  rw [← rank_Ψ_Ψinv H x, h, map_zero]

/-- The hidden outcome-0 point of label `l`. -/
private lemma rank_stdAnchoredVar_label (V : Family) (l : Label) :
    stdAnchoredVar V ⟨12 + 3 * (hiddenFrameEquiv l).val, by have := (hiddenFrameEquiv l).isLt; omega⟩ =
      hiddenVec (V l) := by
  have h0 : ¬ ((⟨12 + 3 * (hiddenFrameEquiv l).val, by have := (hiddenFrameEquiv l).isLt; omega⟩ :
      Fin 39).val < 12) := by simp
  simp only [stdAnchoredVar, h0, ↓reduceDIte]
  have h1 : (12 + 3 * (hiddenFrameEquiv l).val) % 3 = 0 := by omega
  have h2 : (⟨(12 + 3 * (hiddenFrameEquiv l).val) / 3 - 4, by have := (hiddenFrameEquiv l).isLt; omega⟩ :
      Fin 9) = hiddenFrameEquiv l := Fin.ext (by simp only; omega)
  simp only [h1, pow_zero, one_smul, h2, Equiv.symm_apply_apply]

private lemma rank_stdAnchoredVar_low (V : Family) (j : Fin 39) (hj : j.val < 12) :
    stdAnchoredVar V j = 0 := by
  simp only [stdAnchoredVar, hj, ↓reduceDIte]

/-- Core matrix computation of MASTER §6.7. -/
private lemma rank_matrix_core (L R X Y : Mat) (d : PhaseTriple) (δ : Index → ℂ)
    (hL : Lᴴ * L = 1) (hR : R * Rᴴ = 1) (hX : X.trace = 0)
    (h : ∀ m, X * L * monomialFamily d m * R + L * monomialFamily d m * R * Yᴴ +
      L * monomialVar δ m * R = 0) :
    X = 0 ∧ Yᴴ = 0 ∧ δ = 0 := by
  have hL' : ∀ Z : Mat, Lᴴ * (L * Z) = Z := fun Z => by rw [← Matrix.mul_assoc, hL, Matrix.one_mul]
  have hLL : L * Lᴴ = 1 := mul_eq_one_comm.mp hL
  have hRR : Rᴴ * R = 1 := mul_eq_one_comm.mp hR
  set X' : Mat := Lᴴ * X * L with hX'
  set Y' : Mat := R * Yᴴ * Rᴴ with hY'
  have hm : ∀ m, X' * monomialFamily d m + monomialFamily d m * Y' + monomialVar δ m = 0 := by
    intro m
    have := congrArg (fun M => Lᴴ * M * Rᴴ) (h m)
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_zero, Matrix.zero_mul] at this
    simp only [Matrix.mul_assoc, hR, Matrix.mul_one, hL'] at this
    rw [hX', hY']
    simpa only [Matrix.mul_assoc] using this
  have h00 := hm ((0 : Index), (0 : Index))
  have h10 := hm ((1 : Index), (0 : Index))
  have h01 := hm ((0 : Index), (1 : Index))
  have h02 := hm ((0 : Index), (2 : Index))
  simp [monomialFamily, monomialVar, phaseMatrix,
    show (0 : Index) ≠ 2 by decide, show (1 : Index) ≠ 2 by decide] at h00 h10 h01 h02
  have hYX : Y' = -X' := eq_neg_of_add_eq_zero_right h00
  rw [hYX] at h10 h01 h02
  have hc : X' * clock = clock * X' := by
    have := h10; rw [Matrix.mul_neg, ← sub_eq_add_neg, sub_eq_zero] at this; exact this
  have hs : X' * shift = shift * X' := by
    have := h01; rw [Matrix.mul_neg, ← sub_eq_add_neg, sub_eq_zero] at this; exact this
  have ht : X'.trace = 0 := by
    rw [hX', Matrix.trace_mul_comm, ← Matrix.mul_assoc, hLL, Matrix.one_mul, hX]
  have hX0 : X' = 0 := rank_scalar_zero X' hc hs ht
  refine ⟨?_, ?_, ?_⟩
  · calc X = (L * Lᴴ) * X * (L * Lᴴ) := by rw [hLL, Matrix.one_mul, Matrix.mul_one]
      _ = L * X' * Lᴴ := by rw [hX']; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hX0, Matrix.mul_zero, Matrix.zero_mul]
  · calc Yᴴ = (Rᴴ * R) * Yᴴ * (Rᴴ * R) := by rw [hRR, Matrix.one_mul, Matrix.mul_one]
      _ = Rᴴ * Y' * R := by rw [hY']; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hYX, hX0, neg_zero, Matrix.mul_zero, Matrix.zero_mul]
  · rw [hX0, Matrix.zero_mul, neg_zero, Matrix.mul_zero, zero_add, zero_add] at h02
    funext j
    have := congrFun (congrFun h02 (j + 1 + 1)) j
    rw [pow_two, Matrix.mul_assoc, ThreeCycleMatrix.shift_mul_apply,
      ThreeCycleMatrix.shift_mul_apply, add_sub_cancel_right, add_sub_cancel_right,
      Matrix.diagonal_apply_eq] at this
    exact this

private lemma rank_torusVar_eq_zero (d₀ : PhaseTriple) (e : Fin 2 → ℝ) (h : torusVar d₀ e = 0) :
    e = 0 := by
  have hne : ∀ j, d₀.val j ≠ 0 := fun j hj => by
    have := d₀.2.1 j
    rw [hj, map_zero] at this
    exact zero_ne_one this
  have hang : ∀ j, torusAngles e j = 0 := by
    intro j
    have := congrFun h j
    simp only [torusVar, Pi.zero_apply, mul_eq_zero, hne j, false_or, Complex.I_ne_zero, or_false,
      Complex.ofReal_eq_zero] at this
    exact this
  funext i
  fin_cases i
  · simpa [torusAngles] using hang 0
  · simpa [torusAngles] using hang 1

private lemma rank_suMat_zero : suMat 0 = 0 := by simp [suMat]

/-! ## The eighteen-parameter derivative is injective -/

/-- `preVar p = 0` forces `p = 0` (MASTER §6.7). -/
private lemma rank_preVar_eq_zero {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) (p : PreParam)
    (hp : preVar ξ₀ hξ₀ H p = 0) : p = 0 := by
  set V := hidVar ξ₀ H (anchorTriple ξ₀ hξ₀ H) (suMat p.1) (suMat p.2.1)
    (torusVar (anchorTriple ξ₀ hξ₀ H) p.2.2) with hV
  have hvar : ∀ j : Fin 39, stdAnchoredVar V j = 0 := by
    intro j
    have := congrFun hp (anchorRelabel H j)
    simp only [preVar, Equiv.symm_apply_apply, Pi.zero_apply] at this
    rw [← hV] at this
    exact rank_Ψinv_eq_zero (rank_uc_injective (this.trans rank_uc_zero.symm))
  have hVl : ∀ l, V l = 0 := fun l =>
    rank_hiddenVec_eq_zero ((rank_stdAnchoredVar_label V l).symm.trans (hvar _))
  have hc : ∀ m, gaugeScalar H ((gaugeLabel H).symm m) ≠ 0 := fun m hc => by
    have := gaugeScalar_normSq H ((gaugeLabel H).symm m)
    rw [hc, map_zero] at this
    exact zero_ne_one this
  have hm := fun m => by
    have h1 := hVl ((gaugeLabel H).symm m)
    simp only [hV, hidVar, Equiv.apply_symm_apply] at h1
    exact (smul_eq_zero.mp h1).resolve_left (hc m)
  obtain ⟨hX, hY, hδ⟩ := rank_matrix_core (gaugeLeft ξ₀ H) (gaugeRight ξ₀ H) (suMat p.1)
    (suMat p.2.1) (anchorTriple ξ₀ hξ₀ H) (torusVar (anchorTriple ξ₀ hξ₀ H) p.2.2)
    (gaugeLeft_unitary hξ₀ H) (gaugeRight_unitary hξ₀ H) (suMat_trace p.1) hm
  have h1 : p.1 = 0 := suMat_injective (hX.trans rank_suMat_zero.symm)
  have h2 : p.2.1 = 0 :=
    suMat_injective ((Matrix.conjTranspose_eq_zero.mp hY).trans rank_suMat_zero.symm)
  have h3 : p.2.2 = 0 := rank_torusVar_eq_zero _ _ hδ
  exact Prod.ext h1 (Prod.ext h2 h3)

theorem preDer_injective {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    Function.Injective (preDer ξ₀ hξ₀ H) := by
  refine (injective_iff_map_eq_zero (preDer ξ₀ hξ₀ H)).2 fun p hp => ?_
  rw [preDer_apply] at hp
  exact rank_preVar_eq_zero hξ₀ H p hp

/-! ## The right gauge moves `P` against the gauge direction of the raw family -/

private lemma rank_hidden_sum (Z A B : TitsComplexMatrix) (h : A * Z + B = 0) :
    rightDer Z (nativeComplementaryPoint A) + hiddenVec B = 0 := by
  rw [rightDer_complementaryPoint, rank_hiddenVec_add, h, rank_hiddenVec_zero]

private lemma rank_torusVar_zero (d : PhaseTriple) : torusVar d (0 : Fin 2 → ℝ) = 0 := by
  funext j'
  fin_cases j' <;> simp [torusVar, torusAngles] <;> rfl

private lemma rank_hidVar_gauge (ξ₀ : Fin 4 → ℂ) (H : Fin 4) (d : PhaseTriple) (X Y : Mat)
    (δ : Index → ℂ) (hX : X = 0) (hY : Yᴴ = -Y) (hδ : δ = 0) (l : Label) :
    hidVar ξ₀ H d X Y δ l = -(hidFamily ξ₀ H 1 1 d l * Y) := by
  subst hX hδ
  have hmv : ∀ m, monomialVar (0 : Index → ℂ) m = 0 := fun m => by simp [monomialVar]
  simp only [hidVar, hidFamily, hmv, hY, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, smul_neg,
    Matrix.smul_mul]

private lemma rank_smul_mul_add (c : ℂ) (A Z : TitsComplexMatrix) : (c • A) * Z + c • -(A * Z) = 0 := by
  rw [Matrix.smul_mul, smul_neg, add_neg_cancel]

theorem orbitMapC_gaugeDer {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) (k : Fin 8 → ℝ) :
    orbitMapC ξ₀ (gaugeDer H k) + preDer ξ₀ hξ₀ H (0, k, 0) = 0 := by
  rw [preDer_apply]
  funext i
  obtain ⟨j, rfl⟩ := (anchorRelabel H).surjective i
  rw [Pi.add_apply, orbitMapC_apply, Pi.zero_apply]
  simp only [preVar, Equiv.symm_apply_apply, gaugeDer, coordEnd_apply, literalCfg,
    NativePolynomial.fromUpperCoordinates_upperCoordinates, LinearMap.comp_apply]
  rw [anchor_form hξ₀ H j, ← NativePolynomial.upperCoordinates_add, ← map_add]
  have hzero : rightDer (suMat k) (stdAnchored (anchorQuartet ξ₀ H)
      (hidFamily ξ₀ H 1 1 (anchorTriple ξ₀ hξ₀ H)) j) +
      stdAnchoredVar (hidVar ξ₀ H (anchorTriple ξ₀ hξ₀ H) (suMat (0 : Fin 8 → ℝ)) (suMat k)
        (torusVar (anchorTriple ξ₀ hξ₀ H) (0 : Fin 2 → ℝ))) j = 0 := by
    unfold stdAnchored stdAnchoredVar
    split_ifs with hj
    · rw [rightDer_includeHermitianMatrix, add_zero]
    · refine rank_hidden_sum (suMat k) _ _ ?_
      rw [rank_hidVar_gauge ξ₀ H (anchorTriple ξ₀ hξ₀ H) (suMat 0) (suMat k) _ rank_suMat_zero
        (suMat_conjTranspose k) (rank_torusVar_zero _)]
      exact rank_smul_mul_add _ _ _
  rw [hzero, map_zero, rank_uc_zero]

/-! ## The kernel of the saturated derivative -/

private lemma rank_preVar_quartet {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) (p : PreParam)
    (j : Fin 12) : preVar ξ₀ hξ₀ H p (quartetLabel H j) = 0 := by
  simp only [preVar, quartetLabel, Equiv.symm_apply_apply]
  rw [rank_stdAnchoredVar_low _ _ (by simp), map_zero, rank_uc_zero]

theorem rawDer_eq_zero_iff {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) (v : RawParam) :
    rawDer ξ₀ hξ₀ H v = 0 ↔ ∃ k, (v.1 : CEnd) = gaugeDer H k ∧ v.2 = (0, k, 0) := by
  rw [rawDer_apply]
  constructor
  · intro h
    have hmem : (v.1 : CEnd) ∈ quartetFixer ξ₀ H := by
      refine Submodule.mem_inf.2 ⟨v.1.2, Submodule.mem_iInf _ |>.2 fun j => ?_⟩
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.apply_apply]
      have := congrFun h (quartetLabel H j)
      rw [Pi.add_apply, orbitMapC_apply, preDer_apply, rank_preVar_quartet, add_zero] at this
      exact this
    obtain ⟨k, hk⟩ := (mem_quartetFixer_iff hξ₀ H _).1 hmem
    refine ⟨k, hk, preDer_injective hξ₀ H ?_⟩
    have h2 := orbitMapC_gaugeDer hξ₀ H k
    rw [← hk] at h2
    exact add_left_cancel (h.trans h2.symm)
  · rintro ⟨k, hk, h2⟩
    rw [hk, h2]
    exact orbitMapC_gaugeDer hξ₀ H k

/-- The gauge directions `k ↦ (gaugeDer H k, 0, k, 0)` as a linear map. -/
private def rank_gaugeLin (H : Fin 4) : (Fin 8 → ℝ) →ₗ[ℝ] RawParam where
  toFun k := (⟨gaugeDer H k, gaugeDer_mem_derC H k⟩, (0, k, 0))
  map_add' k k' := by
    refine Prod.ext (Subtype.ext (gaugeDer_add H k k')) ?_
    simp
  map_smul' c k := by
    refine Prod.ext (Subtype.ext (gaugeDer_smul H c k)) ?_
    simp

private lemma rank_gaugeLin_injective (H : Fin 4) : Function.Injective (rank_gaugeLin H) := by
  intro k k' h
  have := congrArg (fun v : RawParam => v.2.2.1) h
  exact this

private lemma rank_ker_eq_range {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    LinearMap.ker (rawDer ξ₀ hξ₀ H : RawParam →ₗ[ℝ] Cfg) = LinearMap.range (rank_gaugeLin H) := by
  ext v
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, rawDer_eq_zero_iff, LinearMap.mem_range]
  constructor
  · rintro ⟨k, hk, h2⟩
    exact ⟨k, Prod.ext (Subtype.ext hk.symm) h2.symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl, rfl⟩

theorem finrank_ker_rawDer {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    Module.finrank ℝ ↥(LinearMap.ker (rawDer ξ₀ hξ₀ H : RawParam →ₗ[ℝ] Cfg)) = 8 := by
  rw [rank_ker_eq_range hξ₀ H, LinearMap.finrank_range_of_inj (rank_gaugeLin_injective H),
    Module.finrank_fin_fun]

/-- The group components of the kernel are exactly the pointwise quartet fixer. -/
theorem quartetFixer_eq_ker_fst {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) (D : CEnd) :
    D ∈ quartetFixer ξ₀ H ↔ ∃ v : RawParam, rawDer ξ₀ hξ₀ H v = 0 ∧ (v.1 : CEnd) = D := by
  rw [mem_quartetFixer_iff hξ₀ H]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨rank_gaugeLin H k, (rawDer_eq_zero_iff hξ₀ H _).2 ⟨k, rfl, rfl⟩, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨k, hk, -⟩ := (rawDer_eq_zero_iff hξ₀ H v).1 hv
    exact ⟨k, hk⟩

theorem rawDer62_injective {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    Function.Injective (rawDer62 ξ₀ hξ₀ H) := by
  have hg0 : gaugeDer H 0 = 0 := by
    have := gaugeDer_smul H 0 0
    rwa [zero_smul, zero_smul] at this
  have hzero : ∀ p : RawParam62, rawDer62 ξ₀ hξ₀ H p = 0 → p = 0 := by
    intro p hp
    rw [rawDer62_apply, rawDer_eq_zero_iff] at hp
    obtain ⟨k, hk, h2⟩ := hp
    have hk0 : k = 0 := (congrArg (fun q : PreParam => q.2.1) h2).symm
    subst hk0
    refine Prod.ext (Subtype.ext (hk.trans hg0)) (Prod.ext ?_ ?_)
    · exact congrArg (fun q : PreParam => q.1) h2
    · exact congrArg (fun q : PreParam => q.2.2) h2
  intro p q hpq
  have e1 : rawDer62 ξ₀ hξ₀ H (q + (p - q)) = rawDer62 ξ₀ hξ₀ H q + rawDer62 ξ₀ hξ₀ H (p - q) :=
    ContinuousLinearMap.map_add _ _ _
  have e2 : q + (p - q) = p := add_sub_cancel q p
  rw [e2] at e1
  exact sub_eq_zero.mp (hzero _ (add_left_cancel (e1.symm.trans (hpq.trans (add_zero _).symm))))

theorem finrank_range_rawDer {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) :
    Module.finrank ℝ ↥(LinearMap.range (rawDer ξ₀ hξ₀ H : RawParam →ₗ[ℝ] Cfg)) = 62 := by
  have h := LinearMap.finrank_range_add_finrank_ker (K := ℝ) (V := RawParam) (V₂ := Cfg)
    (rawDer ξ₀ hξ₀ H : RawParam →ₗ[ℝ] Cfg)
  have : Module.Free ℝ ↥derC := Module.Free.of_divisionRing ℝ ↥derC
  rw [finrank_ker_rawDer hξ₀ H, Module.finrank_prod, Module.finrank_prod, Module.finrank_prod,
    finrank_derC] at h
  simp only [Module.finrank_fin_fun] at h
  omega

end CKM.NativeFourFamily

#print axioms CKM.NativeFourFamily.preDer_injective
#print axioms CKM.NativeFourFamily.orbitMapC_gaugeDer
#print axioms CKM.NativeFourFamily.rawDer_eq_zero_iff
#print axioms CKM.NativeFourFamily.finrank_ker_rawDer
#print axioms CKM.NativeFourFamily.quartetFixer_eq_ker_fst
#print axioms CKM.NativeFourFamily.rawDer62_injective
#print axioms CKM.NativeFourFamily.finrank_range_rawDer
