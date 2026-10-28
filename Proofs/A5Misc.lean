module

public import A5Gauge
public import GSConsumer

@[expose] public section

/-!
# Phase predicate, phase variation and the central redundancy (piece MISC)

`IsGoodPhase` is equivalent to all four resonance counts vanishing (A3's `resonanceCount`); the
nonresonant phase `xiNonres` of the group/slice consumer is good; goodness is open within the unit
torus. The pre-saturation family `preCfg` has exactly the simultaneous central redundancy
`(g, h) ↦ (ζ g, ζ h)`, `ζ³ = 1` (MASTER §6.7: the identity label gives `g h'ᴴ`-agreement,
commuting with the clock and shift labels forces a scalar, the `(0,2)` label gives `d = d'`).
-/

noncomputable section

open CKM.NativeFirstOrder CKM.NativeGroupSlice CompactAlbert UnitaryErrorBases
open scoped Matrix Topology

namespace CKM.NativeFourFamily

private lemma misc_indexCases (i : Index) : i = 0 ∨ i = 1 ∨ i = 2 :=
  (by decide : ∀ j : Index, j = 0 ∨ j = 1 ∨ j = 2) i

private lemma misc_omega_ne_one : UnitaryErrorBases.omega ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  norm_num [UnitaryErrorBases.omega] at this

private lemma misc_omega_sq_ne_one : UnitaryErrorBases.omega ^ 2 ≠ 1 := by
  rw [← ThreeCycleMatrix.omega_star]
  intro h
  have := congrArg Complex.re h
  norm_num [UnitaryErrorBases.omega] at this

private lemma misc_omega_ne_sq : UnitaryErrorBases.omega ≠ UnitaryErrorBases.omega ^ 2 := by
  rw [← ThreeCycleMatrix.omega_star]
  intro h
  have := congrArg Complex.im h
  norm_num [UnitaryErrorBases.omega] at this
  have h3 : (0 : ℝ) < √3 := by positivity
  linarith

private lemma misc_val0 : (0 : Index).val = 0 := rfl
private lemma misc_val1 : (1 : Index).val = 1 := rfl
private lemma misc_val2 : (2 : Index).val = 2 := rfl

/-- A `3 × 3` matrix commuting with the clock and shift matrices is scalar (the clock has distinct
eigenvalues `1, ω, ω²`, so the matrix is diagonal; the shift permutes the diagonal cyclically). -/
private theorem misc_scalar_of_comm (A : Mat) (h1 : A * clock = clock * A)
    (h2 : A * shift = shift * A) : A = A 0 0 • 1 := by
  have hc : ∀ i j, A i j * UnitaryErrorBases.omega ^ (j : Index).val =
      UnitaryErrorBases.omega ^ (i : Index).val * A i j := by
    intro i j
    have := congrFun (congrFun h1 i) j
    simpa [clock, Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  have hs : ∀ i j, A i (j + 1) = A (i - 1) j := by
    intro i j
    have := congrFun (congrFun h2 i) j
    rwa [ThreeCycleMatrix.mul_shift_apply, ThreeCycleMatrix.shift_mul_apply] at this
  have hoff : ∀ i j, i ≠ j → A i j = 0 := by
    intro i j hij
    have hne : UnitaryErrorBases.omega ^ (j : Index).val ≠
        UnitaryErrorBases.omega ^ (i : Index).val := by
      rcases misc_indexCases i with rfl | rfl | rfl <;>
        rcases misc_indexCases j with rfl | rfl | rfl <;>
        simp only [misc_val0, misc_val1, misc_val2, pow_zero, pow_one] <;>
        first
        | exact absurd rfl hij
        | exact misc_omega_ne_one | exact misc_omega_ne_one.symm
        | exact misc_omega_sq_ne_one | exact misc_omega_sq_ne_one.symm
        | exact misc_omega_ne_sq | exact misc_omega_ne_sq.symm
    have h0 : A i j * (UnitaryErrorBases.omega ^ (j : Index).val -
        UnitaryErrorBases.omega ^ (i : Index).val) = 0 := by
      rw [mul_sub, hc i j]; ring
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hne
  have h11 : A 1 1 = A 0 0 := by
    have := hs 1 0
    rwa [zero_add, sub_self] at this
  have h22 : A 2 2 = A 1 1 := by
    have := hs 2 1
    rwa [show (1 : Index) + 1 = 2 by decide, show (2 : Index) - 1 = 1 by decide] at this
  ext i j
  by_cases hij : i = j
  · subst j
    rcases misc_indexCases i with rfl | rfl | rfl <;> simp [h11, h22]
  · simp [Matrix.one_apply_ne hij, hoff i j hij]


private lemma misc_mono00 (d : PhaseTriple) : monomialFamily d (0, 0) = 1 := by
  simp [monomialFamily, phaseMatrix, show (0 : Index) ≠ 2 by decide]

private lemma misc_mono10 (d : PhaseTriple) : monomialFamily d (1, 0) = clock := by
  simp [monomialFamily, phaseMatrix, misc_val1, show (0 : Index) ≠ 2 by decide]

private lemma misc_mono01 (d : PhaseTriple) : monomialFamily d (0, 1) = shift := by
  simp [monomialFamily, phaseMatrix, misc_val1, show (1 : Index) ≠ 2 by decide]

private lemma misc_mono02 (d : PhaseTriple) :
    monomialFamily d (0, 2) = shift ^ 2 * Matrix.diagonal d.val := by
  simp [monomialFamily, phaseMatrix, misc_val2]

private lemma misc_star_mul_of_cube {ζ : ℂ} (h : ζ ^ 3 = 1) : star ζ * ζ = 1 := by
  have hn : Complex.normSq ζ = 1 := by
    have h3 : Complex.normSq ζ ^ 3 = 1 := by rw [← map_pow, h, map_one]
    exact (pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg _) (by norm_num)).mp h3
  rw [show star ζ = (starRingEnd ℂ) ζ from rfl, ← Complex.normSq_eq_conj_mul_self, hn,
    Complex.ofReal_one]

private lemma misc_star_of_cube {ζ : ℂ} (h : ζ ^ 3 = 1) : star ζ = ζ ^ 2 := by
  calc star ζ = star ζ * ζ ^ 3 := by rw [h, mul_one]
    _ = (star ζ * ζ) * ζ ^ 2 := by ring
    _ = ζ ^ 2 := by rw [misc_star_mul_of_cube h, one_mul]


/-- Central redundancy of the hidden family: the identity, clock and shift labels force
`Lᴴ g'ᴴ g L` to be a scalar `ζ₀` with `ζ₀³ = 1` (determinants), so `g' = ζ₀² g`, `h' = ζ₀² h`; the
`(0,2)` label then gives `d = d'`. -/
private theorem misc_hidFamily_eq_iff {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4)
    {g h g' h' : Mat} (hg : g ∈ Matrix.specialUnitaryGroup Index ℂ)
    (hh : h ∈ Matrix.specialUnitaryGroup Index ℂ) (hg' : g' ∈ Matrix.specialUnitaryGroup Index ℂ)
    (d d' : PhaseTriple) :
    hidFamily ξ₀ H g h d = hidFamily ξ₀ H g' h' d' ↔
      ∃ ζ : ℂ, ζ ^ 3 = 1 ∧ g' = ζ • g ∧ h' = ζ • h ∧ d' = d := by
  have hL : (gaugeLeft ξ₀ H)ᴴ * gaugeLeft ξ₀ H = 1 := gaugeLeft_unitary hξ₀ H
  have hR : gaugeRight ξ₀ H * (gaugeRight ξ₀ H)ᴴ = 1 := gaugeRight_unitary hξ₀ H
  set L := gaugeLeft ξ₀ H with hLdef
  set R := gaugeRight ξ₀ H with hRdef
  have hL' : L * Lᴴ = 1 := mul_eq_one_comm.mp hL
  have hR' : Rᴴ * R = 1 := mul_eq_one_comm.mp hR
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff,
    Matrix.star_eq_conjTranspose] at hg hh hg'
  have hg'l : g'ᴴ * g' = 1 := mul_eq_one_comm.mp hg'.1
  have hhl : hᴴ * h = 1 := mul_eq_one_comm.mp hh.1
  constructor
  · intro hW
    have heq : ∀ m, g * (L * (monomialFamily d m * (R * hᴴ))) =
        g' * (L * (monomialFamily d' m * (R * h'ᴴ))) := by
      intro m
      have h1 := congrFun hW ((gaugeLabel H).symm m)
      simp only [hidFamily, Equiv.apply_symm_apply] at h1
      have hc : gaugeScalar H ((gaugeLabel H).symm m) ≠ 0 := by
        intro h0
        have := gaugeScalar_cube H ((gaugeLabel H).symm m)
        rw [h0] at this
        norm_num at this
      have h2 := smul_right_injective Mat hc h1
      simpa only [Matrix.mul_assoc] using h2
    set A := Lᴴ * (g'ᴴ * (g * L)) with hA
    have c1 : ∀ X : Mat, g'ᴴ * (g' * X) = X := fun X => by
      rw [← Matrix.mul_assoc, hg'l, Matrix.one_mul]
    have c2 : ∀ X : Mat, Lᴴ * (L * X) = X := fun X => by
      rw [← Matrix.mul_assoc, hL, Matrix.one_mul]
    have key : ∀ m, A * (monomialFamily d m * (R * hᴴ)) = monomialFamily d' m * (R * h'ᴴ) := by
      intro m
      have h1 := congrArg (fun X => Lᴴ * (g'ᴴ * X)) (heq m)
      simp only [c1, c2] at h1
      rw [hA]
      simpa only [Matrix.mul_assoc] using h1
    have key0 : A * (R * hᴴ) = R * h'ᴴ := by simpa [misc_mono00] using key (0, 0)
    have comm : ∀ m, A * monomialFamily d m = monomialFamily d' m * A := by
      intro m
      have h1 := key m
      rw [← key0] at h1
      have h2 := congrArg (fun X => X * (h * Rᴴ)) h1
      have c3 : R * (hᴴ * (h * Rᴴ)) = 1 := by
        rw [← Matrix.mul_assoc hᴴ, hhl, Matrix.one_mul, hR]
      simpa only [Matrix.mul_assoc, c3, Matrix.mul_one] using h2
    have hsc : A = A 0 0 • 1 := misc_scalar_of_comm A
      (by simpa [misc_mono10] using comm (1, 0)) (by simpa [misc_mono01] using comm (0, 1))
    set ζ0 := A 0 0 with hζ0
    have c4 : ∀ X : Mat, L * (Lᴴ * X) = X := fun X => by
      rw [← Matrix.mul_assoc, hL', Matrix.one_mul]
    have c5 : ∀ X : Mat, g' * (g'ᴴ * X) = X := fun X => by
      rw [← Matrix.mul_assoc, hg'.1, Matrix.one_mul]
    have hgg : g = ζ0 • g' := by
      have h1 : g' * (L * (A * Lᴴ)) = g := by
        rw [hA]
        simp only [Matrix.mul_assoc, c4, c5, hL', Matrix.mul_one]
      rw [hsc] at h1
      simpa only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, hL', Matrix.mul_one] using h1.symm
    have hζ3 : ζ0 ^ 3 = 1 := by
      have := congrArg Matrix.det hgg
      rw [Matrix.det_smul, hg.2, hg'.2] at this
      simpa using this.symm
    have hstar := misc_star_of_cube hζ3
    refine ⟨ζ0 ^ 2, by rw [← pow_mul, mul_comm, pow_mul, hζ3, one_pow], ?_, ?_, ?_⟩
    · rw [hgg, smul_smul, show ζ0 ^ 2 * ζ0 = ζ0 ^ 3 by ring, hζ3, one_smul]
    · have h1 : h'ᴴ = ζ0 • hᴴ := by
        have := congrArg (fun X => Rᴴ * X) key0
        rw [hsc] at this
        simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, ← Matrix.mul_assoc, hR'] at this
        exact this.symm
      calc h' = (h'ᴴ)ᴴ := (Matrix.conjTranspose_conjTranspose h').symm
        _ = ζ0 ^ 2 • h := by
          rw [h1, Matrix.conjTranspose_smul, Matrix.conjTranspose_conjTranspose, hstar]
    · have hζne : ζ0 ≠ 0 := by
        rintro h0
        rw [h0] at hζ3
        norm_num at hζ3
      have h1 := comm (0, 2)
      rw [misc_mono02, misc_mono02, hsc] at h1
      simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one] at h1
      have h2 := smul_right_injective Mat hζne h1
      apply Subtype.ext
      funext j
      have h3 := congrFun (congrFun h2 (j + 2)) j
      have hs2 : (shift ^ 2) (j + 2) j = 1 := by
        have := ThreeCycleMatrix.shift_pow_apply 2 (j + 2) j
        rw [misc_val2] at this
        simpa using this
      simp only [Matrix.mul_diagonal, hs2, one_mul] at h3
      exact h3.symm
  · rintro ⟨ζ, hζ, rfl, rfl, rfl⟩
    have h1 : star ζ * ζ = 1 := misc_star_mul_of_cube hζ
    funext l
    simp only [hidFamily]
    congr 1
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h1,
      one_smul]


/-- Equal raw configurations have equal hidden families: `upperCoordinates`, `anchorΨinv H` and
`nativeComplementaryPoint` are injective and `anchorRelabel H` is a bijection. -/
private theorem misc_preCfg_eq_iff_hid (ξ₀ : Fin 4 → ℂ) (H : Fin 4) (g h g' h' : Mat)
    (d d' : PhaseTriple) :
    preCfg ξ₀ H g h d = preCfg ξ₀ H g' h' d' ↔ hidFamily ξ₀ H g h d = hidFamily ξ₀ H g' h' d' := by
  constructor
  · intro hc
    funext l
    have hi := congrFun hc (anchorRelabel H
      (NativePolynomial.ConfigurationResiduals.framePointIndex (hiddenFrame l) 0))
    simp only [preCfg, prePoint, Equiv.symm_apply_apply] at hi
    have h1 := NativePolynomial.upperCoordinateEquiv.injective hi
    have key : ∀ x, anchorΨ H (anchorΨinv H x) = x := fun x =>
      LinearMap.congr_fun (anchorΨ_comp_anchorΨinv H) x
    have h2 := congrArg (anchorΨ H) h1
    rw [key, key, Anchor3.stdAnchored_hid, Anchor3.stdAnchored_hid] at h2
    have inj : ∀ U V : TitsComplexMatrix,
        nativeComplementaryPoint U = nativeComplementaryPoint V → U = V := by
      intro U V hUV
      have h3 := congrArg Prod.snd (congrArg nativeTitsMatrixPair hUV)
      rw [nativeComplementaryPoint_pair, nativeComplementaryPoint_pair] at h3
      have h13 : (1 / 3 : ℂ) ≠ 0 := by norm_num
      exact smul_right_injective TitsComplexMatrix h13 h3
    have h4 := inj _ _ h2
    simp only [Fin.val_zero, pow_zero, one_smul] at h4
    exact h4
  · intro hW
    funext i
    simp only [preCfg, prePoint, hW]

theorem isGoodPhase_iff (ξ : Fin 4 → ℂ) :
    IsGoodPhase ξ ↔ ∃ hξ : IsUnitPhase ξ, ∀ H, resonanceCount (anchorTriple ξ hξ H) = 0 := by
  constructor
  · rintro ⟨hξ, h⟩
    refine ⟨hξ, fun H => ?_⟩
    rw [resonanceCount, Fintype.card_eq_zero_iff]
    exact ⟨fun j => h H j.1 j.2⟩
  · rintro ⟨hξ, h⟩
    refine ⟨hξ, fun H j hj => ?_⟩
    have h0 := h H
    rw [resonanceCount, Fintype.card_eq_zero_iff] at h0
    exact h0.false ⟨j, hj⟩

theorem isGoodPhase_xiNonres : IsGoodPhase CKM.NativeGroupSliceConsumer.xiNonres :=
  ⟨CKM.NativeGroupSliceConsumer.isUnitPhase_xiNonres,
    fun H j => CKM.NativeGroupSliceConsumer.xiNonres_phase_cube_ne_one H j⟩

theorem isUnitPhase_commonPhase {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (θ : Fin 4 → ℝ) :
    IsUnitPhase (commonPhase ξ₀ θ) := by
  intro a
  show Complex.normSq (ξ₀ a * Complex.exp ((θ a : ℂ) * Complex.I)) = 1
  rw [map_mul, hξ₀ a, one_mul, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]

theorem commonPhase_zero (ξ₀ : Fin 4 → ℂ) : commonPhase ξ₀ 0 = ξ₀ := by
  funext a
  simp [commonPhase]

theorem torusPhase_zero (d₀ : PhaseTriple) : torusPhase d₀ 0 = d₀ := by
  apply Subtype.ext
  funext j
  rcases misc_indexCases j with rfl | rfl | rfl <;> simp [torusPhase, torusAngles]

/-- Goodness is open within the unit torus. -/
theorem exists_nhds_isGoodPhase {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsGoodPhase ξ₀) :
    ∃ V ∈ 𝓝 ξ₀, ∀ ξ ∈ V, IsUnitPhase ξ → IsGoodPhase ξ := by
  have hne : ∀ a, ξ₀ a ≠ 0 := fun a h0 => by
    have := hξ₀.1 a
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hcont : ∀ H j, ContinuousAt (fun ξ : Fin 4 → ℂ => anchorPhases ξ H j ^ 3) ξ₀ := by
    intro H j
    have hc : ∀ a, ContinuousAt (fun ξ : Fin 4 → ℂ => ξ a) ξ₀ := fun a => continuousAt_apply a ξ₀
    have hi : ∀ a, ContinuousAt (fun ξ : Fin 4 → ℂ => (ξ a)⁻¹) ξ₀ := fun a =>
      (hc a).inv₀ (hne a)
    rcases misc_indexCases j with rfl | rfl | rfl <;> fin_cases H <;>
      simp only [anchorPhases, Matrix.cons_val]
    · exact (((hc 0).mul (hc 1)).div (hc 2) (hne 2)).pow 3
    · exact ((hc 0).mul (hc 2) |>.mul (hc 3)).pow 3
    · exact ((hc 2).mul (hc 3)).neg.pow 3
    · exact (hi 0).neg.pow 3
    · exact (((hc 0).mul (hc 3)).inv₀ (mul_ne_zero (hne 0) (hne 3))).pow 3
    · exact ((hc 1).div (hc 2) (hne 2)).neg.pow 3
    · exact (hi 2).pow 3
    · exact (hi 1).neg.pow 3
    · exact (((hc 2).mul (hc 3)).div (hc 1) (hne 1)).pow 3
    · exact ((((hc 0).mul (hc 1)).mul (hc 3)).inv₀
        (mul_ne_zero (mul_ne_zero (hne 0) (hne 1)) (hne 3))).neg.pow 3
    · exact (hi 3).neg.pow 3
    · exact ((hc 0).mul (hc 1)).pow 3
  have hev : ∀ᶠ ξ in 𝓝 ξ₀, ∀ H j, anchorPhases ξ H j ^ 3 ≠ 1 :=
    Filter.eventually_all.2 fun H => Filter.eventually_all.2 fun j =>
      (hcont H j).eventually_ne (hξ₀.2 H j)
  exact ⟨_, hev, fun ξ hξ hu => ⟨hu, hξ⟩⟩

theorem eventually_isGoodPhase_commonPhase {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsGoodPhase ξ₀) :
    ∀ᶠ θ in 𝓝 (0 : Fin 4 → ℝ), IsGoodPhase (commonPhase ξ₀ θ) := by
  obtain ⟨V, hV, hgood⟩ := exists_nhds_isGoodPhase hξ₀
  have hc : Continuous (commonPhase ξ₀) := by
    unfold commonPhase
    fun_prop
  have ht : Filter.Tendsto (commonPhase ξ₀) (𝓝 0) (𝓝 ξ₀) := by
    have := hc.tendsto 0
    rwa [commonPhase_zero] at this
  filter_upwards [ht hV] with θ hθ
  exact hgood _ hθ (isUnitPhase_commonPhase hξ₀.1 θ)

/-- The only redundancy of the eighteen-parameter model is the simultaneous central one. -/
theorem preCfg_eq_iff {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (H : Fin 4) {g h g' h' : Mat}
    (hg : g ∈ Matrix.specialUnitaryGroup Index ℂ) (hh : h ∈ Matrix.specialUnitaryGroup Index ℂ)
    (hg' : g' ∈ Matrix.specialUnitaryGroup Index ℂ) (hh' : h' ∈ Matrix.specialUnitaryGroup Index ℂ)
    (d d' : PhaseTriple) :
    preCfg ξ₀ H g h d = preCfg ξ₀ H g' h' d' ↔
      ∃ ζ : ℂ, ζ ^ 3 = 1 ∧ g' = ζ • g ∧ h' = ζ • h ∧ d' = d := by
  rw [misc_preCfg_eq_iff_hid, misc_hidFamily_eq_iff hξ₀ H hg hh hg' d d']

end CKM.NativeFourFamily

#print axioms CKM.NativeFourFamily.isGoodPhase_iff
#print axioms CKM.NativeFourFamily.isGoodPhase_xiNonres
#print axioms CKM.NativeFourFamily.isUnitPhase_commonPhase
#print axioms CKM.NativeFourFamily.commonPhase_zero
#print axioms CKM.NativeFourFamily.torusPhase_zero
#print axioms CKM.NativeFourFamily.exists_nhds_isGoodPhase
#print axioms CKM.NativeFourFamily.eventually_isGoodPhase_commonPhase
#print axioms CKM.NativeFourFamily.preCfg_eq_iff
