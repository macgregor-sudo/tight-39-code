module

public import A5Analytic
public import A5Fixer

@[expose] public section

/-!
# The four phase directions are independent modulo the orbit

If `D • P + phaseDer θ = 0` with `D` a derivation, `D` kills the 21 phase-independent points
(`literalPoint_low`), among them the anchor-0 quartet, so `D = gaugeDer 0 k`; on the nine
phase-independent hidden points `p(U)` (`U` invertible) it acts by `U ↦ U suMat k`, which vanishes
only for `k = 0`. Then `phaseDer θ = 0`, and the explicit derivative of the literal family forces
`θ = 0`. Hence the common family has an injective 56-parameter derivative at every unit phase.
-/

noncomputable section

open CKM.NativeFirstOrder CKM.NativeGroupSlice CompactAlbert UnitaryErrorBases
open scoped Matrix Topology

namespace CKM.NativeFourFamily

/-! ## Phase-independence helpers -/

private lemma phase_hiddenVec_pair (U : TitsComplexMatrix) :
    nativeTitsMatrixPair (hiddenVec U) = (0, (1 / 3 : ℂ) • U) :=
  Elim.mkPoint_pair _ _ _

private lemma phase_hiddenVec_eq_zero {U : TitsComplexMatrix} (h : hiddenVec U = 0) : U = 0 := by
  have := congrArg (fun x => (nativeTitsMatrixPair x).2) h
  simp only [phase_hiddenVec_pair, map_zero, Prod.snd_zero] at this
  have h3 : (3 : ℂ) • ((1 / 3 : ℂ) • U) = 0 := by rw [this, smul_zero]
  rwa [smul_smul, show (3 : ℂ) * (1 / 3) = 1 by norm_num, one_smul] at h3

private lemma phase_uc_injective : Function.Injective NativePolynomial.upperCoordinates :=
  NativePolynomial.upperCoordinateEquiv.injective

private lemma phase_uc_zero : NativePolynomial.upperCoordinates 0 = 0 :=
  NativePolynomial.upperCoordinateEquiv.map_zero

private lemma phase_suMat_zero : suMat 0 = 0 := by simp [suMat]

private lemma phase_gaugeDer_zero (H : Fin 4) : gaugeDer H 0 = 0 := by
  have := gaugeDer_smul H 0 0
  rwa [zero_smul, zero_smul] at this

private lemma phase_commonPhase_unit {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (θ : Fin 4 → ℝ) :
    IsUnitPhase (commonPhase ξ₀ θ) := fun a => by
  rw [commonPhase, map_mul, hξ₀ a, one_mul, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_ofReal_mul_I, one_pow]

/-- Directional derivative of a continuous linear reading of the literal phase family. -/
private lemma phase_hasDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (θ : Fin 4 → ℝ) (L : Cfg →L[ℝ] F) :
    HasDerivAt (fun s : ℝ => L (literalCfg (commonPhase ξ₀ (s • θ)))) (L (phaseDer ξ₀ θ)) 0 := by
  have h1 : HasDerivAt (fun s : ℝ => s • θ) θ 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const θ
  have h2 := (hasStrictFDerivAt_literalPhase hξ₀).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1
    (by simp)
  exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2

/-- The phase derivative vanishes at the 21 phase-independent points. -/
private lemma phaseDer_low {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (θ : Fin 4 → ℝ) (i : Fin 39)
    (hi : i.val < 21) : phaseDer ξ₀ θ i = 0 := by
  have hd := phase_hasDerivAt hξ₀ θ (ContinuousLinearMap.proj i)
  have hconst : (fun s : ℝ => (ContinuousLinearMap.proj i : Cfg →L[ℝ] (Fin 27 → ℝ))
      (literalCfg (commonPhase ξ₀ (s • θ)))) =
      fun _ => NativePolynomial.upperCoordinates (QuadraticCertificate.ExactCKMConfiguration.nativePoint i) := by
    funext s
    simp only [ContinuousLinearMap.proj_apply, literalCfg]
    rw [literalPoint_low _ i hi]
  rw [hconst] at hd
  exact hd.unique (hasDerivAt_const _ _)

/-- The hidden entry `(r, c)` of point `i`, a continuous real-linear functional on `Cfg`. -/
private def phase_entry (i : Fin 39) (r c : Fin 3) : Cfg →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun C => (nativeTitsMatrixPair (NativePolynomial.upperCoordinateEquiv.symm (C i))).2 r c
      map_add' := fun x y => by
        simp only [Pi.add_apply, map_add, Prod.snd_add, Matrix.add_apply]
      map_smul' := fun a x => by
        simp only [Pi.smul_apply, map_smul, Prod.smul_snd, Matrix.smul_apply, RingHom.id_apply] }

private lemma phase_entry_literal (ξ : Fin 4 → ℂ) (i : Fin 39) (r c : Fin 3) (U : TitsComplexMatrix)
    (hU : literalPoint ξ i = nativeComplementaryPoint U) :
    phase_entry i r c (literalCfg ξ) = (1 / 3 : ℂ) * U r c := by
  change (nativeTitsMatrixPair (NativePolynomial.fromUpperCoordinates
    (NativePolynomial.upperCoordinates (literalPoint ξ i)))).2 r c = _
  rw [NativePolynomial.fromUpperCoordinates_upperCoordinates, hU, nativeComplementaryPoint_pair]
  rfl

/-- One phase angle is detected by one explicit hidden entry. -/
private lemma phase_coord_zero {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (θ : Fin 4 → ℝ)
    (hθ : phaseDer ξ₀ θ = 0) (a : Fin 4) (i : Fin 39) (r c : Fin 3) (σ : ℂ) (hσ : σ ≠ 0)
    (hform : ∀ ξ, IsUnitPhase ξ → phase_entry i r c (literalCfg ξ) = σ * star (ξ a)) :
    θ a = 0 := by
  set w : ℂ := -((θ a : ℂ) * Complex.I) with hw
  have hd1 := phase_hasDerivAt hξ₀ θ (phase_entry i r c)
  have hfun : (fun s : ℝ => phase_entry i r c (literalCfg (commonPhase ξ₀ (s • θ)))) =
      fun s : ℝ => (σ * star (ξ₀ a)) * NormedSpace.exp (s • w) := by
    funext s
    rw [hform _ (phase_commonPhase_unit hξ₀ _)]
    simp only [commonPhase, Pi.smul_apply, smul_eq_mul]
    rw [star_mul', mul_assoc, Complex.star_def, ← Complex.exp_conj,
      ← Complex.exp_eq_exp_ℂ, map_mul, Complex.conj_ofReal, Complex.conj_I, hw, Complex.real_smul]
    congr 3
    push_cast
    ring
  rw [hfun] at hd1
  have hd2 : HasDerivAt (fun s : ℝ => (σ * star (ξ₀ a)) * NormedSpace.exp (s • w))
      ((σ * star (ξ₀ a)) * (NormedSpace.exp ((0 : ℝ) • w) * w)) 0 :=
    (hasDerivAt_exp_smul_const w (0 : ℝ)).const_mul _
  have heq := hd1.unique hd2
  rw [hθ, map_zero, zero_smul, NormedSpace.exp_zero, one_mul] at heq
  have hstar : star (ξ₀ a) ≠ 0 := by
    intro h0
    have := hξ₀ a
    rw [← star_star (ξ₀ a), h0, star_zero, map_zero] at this
    exact zero_ne_one this
  have hw0 : w = 0 := by
    rcases mul_eq_zero.mp heq.symm with h | h
    · exact absurd h (mul_ne_zero hσ hstar)
    · exact h
  rw [hw, neg_eq_zero, mul_eq_zero] at hw0
  rcases hw0 with h | h
  · exact_mod_cast h
  · exact absurd h Complex.I_ne_zero

private lemma phase_point21 (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    literalPoint ξ ⟨21, by norm_num⟩ = nativeComplementaryPoint (hiddenMatrix ξ 1 0 0) :=
  literalPoint_hidden ξ hξ 1 0 0

private lemma phase_point30 (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    literalPoint ξ ⟨30, by norm_num⟩ = nativeComplementaryPoint (hiddenMatrix ξ 2 0 0) :=
  literalPoint_hidden ξ hξ 2 0 0

private lemma phase_point12 (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    literalPoint ξ ⟨12, by norm_num⟩ = nativeComplementaryPoint (hiddenMatrix ξ 0 0 0) :=
  literalPoint_hidden ξ hξ 0 0 0

/-- `phaseDer θ = 0` forces `θ = 0` (frame group `q = 2` reads `ξ 0, ξ 1`, `q = 3` reads `ξ 2, ξ 3`). -/
private lemma phase_theta_zero {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (θ : Fin 4 → ℝ)
    (hθ : phaseDer ξ₀ θ = 0) : θ = 0 := by
  funext a
  fin_cases a
  · refine phase_coord_zero hξ₀ θ hθ 0 ⟨21, by norm_num⟩ 2 1 (1 / 3) (by norm_num) fun ξ hξ => ?_
    rw [phase_entry_literal ξ _ 2 1 _ (phase_point21 ξ hξ)]
    simp [hiddenMatrix, QuadraticCertificate.ExactCKMABFrames.ellNMatrix,
      ThreeCycleFourier.character]
  · refine phase_coord_zero hξ₀ θ hθ 1 ⟨21, by norm_num⟩ 1 2 (-(1 / 3)) (by norm_num) fun ξ hξ => ?_
    rw [phase_entry_literal ξ _ 1 2 _ (phase_point21 ξ hξ)]
    simp [hiddenMatrix, QuadraticCertificate.ExactCKMABFrames.ellNMatrix,
      ThreeCycleFourier.character]
  · refine phase_coord_zero hξ₀ θ hθ 2 ⟨30, by norm_num⟩ 2 2 (1 / 3) (by norm_num) fun ξ hξ => ?_
    rw [phase_entry_literal ξ _ 2 2 _ (phase_point30 ξ hξ)]
    simp [hiddenMatrix, QuadraticCertificate.ExactCKMCDFrames.njMatrix,
      ThreeCycleFourier.character]
  · refine phase_coord_zero hξ₀ θ hθ 3 ⟨30, by norm_num⟩ 1 0 (-(1 / 3)) (by norm_num) fun ξ hξ => ?_
    rw [phase_entry_literal ξ _ 1 0 _ (phase_point30 ξ hξ)]
    simp [hiddenMatrix, QuadraticCertificate.ExactCKMCDFrames.njMatrix,
      ThreeCycleFourier.character]

private lemma phase_U0_sq (ξ : Fin 4 → ℂ) : hiddenMatrix ξ 0 0 0 * hiddenMatrix ξ 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hiddenMatrix, QuadraticCertificate.ExactCKMThreeHiddenFrames.twoInputMatrix,
      ThreeCycleFourier.character, Matrix.mul_apply, Fin.sum_univ_three]

private lemma phase_quartetLabel0 (j : Fin 12) : quartetLabel 0 j = ⟨j.val, by omega⟩ := by
  fin_cases j <;> rfl

/-! ## Independence modulo the orbit -/

theorem phase_indep_mod_orbit {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) (D : CEnd) (hD : D ∈ derC)
    (θ : Fin 4 → ℝ) (h : orbitMapC ξ₀ D + phaseDer ξ₀ θ = 0) : D = 0 ∧ θ = 0 := by
  have hlow : ∀ i : Fin 39, i.val < 21 → D (literalCfg ξ₀ i) = 0 := by
    intro i hi
    have := congrFun h i
    rwa [Pi.add_apply, orbitMapC_apply, phaseDer_low hξ₀ θ i hi, add_zero] at this
  have hmem : D ∈ quartetFixer ξ₀ 0 := by
    refine Submodule.mem_inf.2 ⟨hD, Submodule.mem_iInf _ |>.2 fun j => ?_⟩
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.apply_apply,
      phase_quartetLabel0]
    exact hlow _ (by simp only; omega)
  obtain ⟨k, rfl⟩ := (mem_quartetFixer_iff hξ₀ 0 _).1 hmem
  have h12 := hlow ⟨12, by norm_num⟩ (by norm_num)
  have hk : k = 0 := by
    simp only [gaugeDer, coordEnd_apply, literalCfg, NativePolynomial.fromUpperCoordinates_upperCoordinates,
      LinearMap.comp_apply] at h12
    rw [phase_point12 ξ₀ hξ₀] at h12
    change NativePolynomial.upperCoordinates (rightDer (suMat k)
      (nativeComplementaryPoint (hiddenMatrix ξ₀ 0 0 0))) = 0 at h12
    rw [rightDer_complementaryPoint] at h12
    have hUZ := phase_hiddenVec_eq_zero (phase_uc_injective (h12.trans phase_uc_zero.symm))
    have hZ : suMat k = 0 := by
      rw [← Matrix.one_mul (suMat k), ← phase_U0_sq ξ₀, Matrix.mul_assoc, hUZ, Matrix.mul_zero]
    exact suMat_injective (hZ.trans phase_suMat_zero.symm)
  subst hk
  rw [phase_gaugeDer_zero] at h ⊢
  rw [map_zero, zero_add] at h
  exact ⟨rfl, phase_theta_zero hξ₀ θ h⟩

theorem commonDer_injective {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) :
    Function.Injective (commonDer ξ₀) := by
  intro p q hpq
  rw [commonDer_apply hξ₀, commonDer_apply hξ₀] at hpq
  have hsum : orbitMapC ξ₀ ((p.1 : CEnd) - q.1) + phaseDer ξ₀ (p.2 - q.2) = 0 := by
    rw [map_sub, map_sub, sub_add_sub_comm, hpq, sub_self]
  obtain ⟨h1, h2⟩ := phase_indep_mod_orbit hξ₀ _ (sub_mem p.1.2 q.1.2) _ hsum
  exact Prod.ext (Subtype.ext (sub_eq_zero.mp h1)) (sub_eq_zero.mp h2)

theorem phaseDer_injective {ξ₀ : Fin 4 → ℂ} (hξ₀ : IsUnitPhase ξ₀) :
    Function.Injective (phaseDer ξ₀) := by
  intro θ θ' h
  have : phaseDer ξ₀ (θ - θ') = 0 := by rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp (phase_theta_zero hξ₀ _ this)

end CKM.NativeFourFamily

#print axioms CKM.NativeFourFamily.phase_indep_mod_orbit
#print axioms CKM.NativeFourFamily.commonDer_injective
#print axioms CKM.NativeFourFamily.phaseDer_injective
