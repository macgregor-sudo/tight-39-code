module

public import A3Interfaces

@[expose] public section

/-!
# Generic transport of the native first-order system

Automorphisms, outcome/frame relabellings, compensated actions, their composition, and the transport
of fixed subspaces through an `AnchorBinding`. No phase or anchor computation occurs here.
-/

noncomputable section

namespace CKM.NativeFirstOrder

open NativePolynomial NativePolynomial.ConfigurationResiduals CompactAlbert

theorem compensated_apply (g : Glennie.Albert →ₗ[ℝ] Glennie.Albert) (π : Equiv.Perm (Fin 39))
    (δ : Fin 39 → Glennie.Albert) (i : Fin 39) : compensated g π δ i = g (δ (π i)) := by
  rfl

theorem compensated_mul (g h : Glennie.Albert →ₗ[ℝ] Glennie.Albert) (π π' : Equiv.Perm (Fin 39)) :
    compensated g π * compensated h π' = compensated (g * h) (π' * π) := by
  rfl

theorem outcomeShift_mul (σ σ' : Fin 13 → Fin 3) :
    outcomeShift σ * outcomeShift σ' = outcomeShift (σ + σ') := by
  ext i
  simp only [outcomeShift, pointRelabel, Equiv.Perm.mul_apply, Equiv.trans_apply,
    Equiv.symm_apply_apply, Equiv.prodShear_apply, Equiv.refl_apply, Equiv.coe_addRight,
    Pi.add_apply]
  congr 3
  abel

/-- The original point order `3f + a` is `finProdFinEquiv`. -/
private theorem framePointIndex_eq_finProdFinEquiv (f : Fin 13) (a : Fin 3) :
    framePointIndex f a = (finProdFinEquiv : Fin 13 × Fin 3 ≃ Fin 39) (f, a) := by
  apply Fin.ext
  simp only [framePointIndex_val, finProdFinEquiv_apply_val]
  omega

theorem pointRelabel_framePointIndex (fperm : Equiv.Perm (Fin 13)) (τ : Fin 13 → Equiv.Perm (Fin 3))
    (f : Fin 13) (a : Fin 3) :
    pointRelabel fperm τ (framePointIndex f a) = framePointIndex (fperm f) (τ f a) := by
  rw [framePointIndex_eq_finProdFinEquiv, framePointIndex_eq_finProdFinEquiv]
  simp only [pointRelabel, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodShear_apply]

/-! ## A symmetric reformulation of the first-order system -/

/-- The first-order conditions over all ordered pairs of distinct outcomes / distinct frames. -/
private def IsFirstOrderSymm (p u : Fin 39 → Glennie.Albert) : Prop :=
  (∀ i : Fin 39, (2 : ℝ) • Glennie.jordan (p i) (u i) = u i) ∧
  (∀ (f : Fin 13) (a b : Fin 3), a ≠ b →
    Glennie.jordan (p (framePointIndex f a)) (u (framePointIndex f b)) +
      Glennie.jordan (u (framePointIndex f a)) (p (framePointIndex f b)) = 0) ∧
  (∀ f : Fin 13, (∑ a : Fin 3, u (framePointIndex f a)) = 0) ∧
  (∀ (f g : Fin 13), f ≠ g → ∀ (a b : Fin 3),
    Glennie.trace (Glennie.jordan (p (framePointIndex f a)) (u (framePointIndex g b))) +
      Glennie.trace (Glennie.jordan (u (framePointIndex f a)) (p (framePointIndex g b))) = 0)

private theorem isFirstOrder_iff_symm (p u : Fin 39 → Glennie.Albert) :
    IsFirstOrder p u ↔ IsFirstOrderSymm p u := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, fun f a b hab => ?_, h3, fun f g hfg a b => ?_⟩
    · rcases lt_or_gt_of_ne hab with hlt | hlt
      · have h := h2 f (ConfigurationResidualIndices.withinPair.symm ⟨(a, b), hlt⟩)
        simp only [Equiv.apply_symm_apply] at h
        exact h
      · have h := h2 f (ConfigurationResidualIndices.withinPair.symm ⟨(b, a), hlt⟩)
        simp only [Equiv.apply_symm_apply] at h
        calc
          _ = Glennie.jordan (p (framePointIndex f b)) (u (framePointIndex f a)) +
              Glennie.jordan (u (framePointIndex f b)) (p (framePointIndex f a)) := by
            rw [Glennie.jordan_comm (p (framePointIndex f b)),
              Glennie.jordan_comm (u (framePointIndex f b)), add_comm]
          _ = 0 := h
    · rcases lt_or_gt_of_ne hfg with hlt | hlt
      · exact h4 ⟨(f, g), hlt⟩ a b
      · have h := h4 ⟨(g, f), hlt⟩ b a
        dsimp only at h
        calc
          _ = Glennie.trace (Glennie.jordan (p (framePointIndex g b)) (u (framePointIndex f a))) +
              Glennie.trace (Glennie.jordan (u (framePointIndex g b)) (p (framePointIndex f a))) := by
            rw [Glennie.jordan_comm (p (framePointIndex g b)),
              Glennie.jordan_comm (u (framePointIndex g b)), add_comm]
          _ = 0 := h
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, fun f s => ?_, h3, fun fg a b => ?_⟩
    · exact h2 f _ _ (ne_of_lt (ConfigurationResidualIndices.withinPair s).property)
    · exact h4 fg.val.1 fg.val.2 (ne_of_lt fg.property) a b

private theorem mem_firstOrderSystem_iff_symm {p u : Fin 39 → Glennie.Albert} :
    u ∈ firstOrderSystem p ↔ IsFirstOrderSymm p u :=
  isFirstOrder_iff_symm p u

/-- One direction of automorphism transport; injectivity is not needed. -/
private theorem map_mem_firstOrderSystem (g : Glennie.Albert →ₗ[ℝ] Glennie.Albert)
    (hg : IsNativeAut g) {p δ : Fin 39 → Glennie.Albert} (hδ : δ ∈ firstOrderSystem p) :
    (fun i => g (δ i)) ∈ firstOrderSystem (fun i => g (p i)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  refine ⟨fun i => ?_, fun f s => ?_, fun f => ?_, fun fg a b => ?_⟩
  · simp only
    rw [← hg.jordan, ← map_smul, h1 i]
  · simp only
    rw [← hg.jordan, ← hg.jordan, ← map_add, h2 f s, map_zero]
  · simp only
    rw [← map_sum, h3 f, map_zero]
  · simp only
    rw [← hg.jordan, ← hg.jordan, hg.trace, hg.trace]
    exact h4 fg a b

/-- A native automorphism transports the first-order system between configurations. -/
theorem map_mem_firstOrderSystem_iff (g : Glennie.Albert →ₗ[ℝ] Glennie.Albert) (hg : IsNativeAut g)
    (hinj : Function.Injective g) (p δ : Fin 39 → Glennie.Albert) :
    (fun i => g (δ i)) ∈ firstOrderSystem (fun i => g (p i)) ↔ δ ∈ firstOrderSystem p := by
  refine ⟨fun h => ?_, map_mem_firstOrderSystem g hg⟩
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun i => ?_, fun f s => ?_, fun f => ?_, fun fg a b => ?_⟩
  · have h := h1 i
    simp only [← hg.jordan, ← map_smul] at h
    exact hinj h
  · have h := h2 f s
    simp only [← hg.jordan, ← map_add] at h
    exact hinj (h.trans (map_zero g).symm)
  · have h := h3 f
    simp only [← map_sum] at h
    exact hinj (h.trans (map_zero g).symm)
  · have h := h4 fg a b
    simp only [← hg.jordan, hg.trace] at h
    exact h

/-- Any frame and outcome relabelling transports the first-order system. -/
theorem relabel_mem_firstOrderSystem_iff (fperm : Equiv.Perm (Fin 13))
    (τ : Fin 13 → Equiv.Perm (Fin 3)) (p δ : Fin 39 → Glennie.Albert) :
    (fun i => δ (pointRelabel fperm τ i)) ∈ firstOrderSystem (fun i => p (pointRelabel fperm τ i)) ↔
      δ ∈ firstOrderSystem p := by
  rw [mem_firstOrderSystem_iff_symm, mem_firstOrderSystem_iff_symm]
  have hπ := pointRelabel_framePointIndex fperm τ
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun j => ?_, fun F A B hAB => ?_, fun F => ?_, fun F G hFG A B => ?_⟩
    · obtain ⟨i, rfl⟩ := (pointRelabel fperm τ).surjective j
      exact h1 i
    · have h := h2 (fperm.symm F) ((τ (fperm.symm F)).symm A) ((τ (fperm.symm F)).symm B)
        ((τ (fperm.symm F)).symm.injective.ne hAB)
      simp only [hπ, Equiv.apply_symm_apply] at h
      exact h
    · have h := h3 (fperm.symm F)
      simp only [hπ, Equiv.apply_symm_apply] at h
      rw [← h]
      exact (Equiv.sum_comp (τ (fperm.symm F)) (fun A => δ (framePointIndex F A))).symm
    · have h := h4 (fperm.symm F) (fperm.symm G) (fperm.symm.injective.ne hFG)
        ((τ (fperm.symm F)).symm A) ((τ (fperm.symm G)).symm B)
      simp only [hπ, Equiv.apply_symm_apply] at h
      exact h
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun i => h1 _, fun f a b hab => ?_, fun f => ?_, fun f g hfg a b => ?_⟩
    · simp only [hπ]
      exact h2 (fperm f) (τ f a) (τ f b) ((τ f).injective.ne hab)
    · simp only [hπ]
      rw [Equiv.sum_comp (τ f) (fun A => δ (framePointIndex (fperm f) A))]
      exact h3 (fperm f)
    · simp only [hπ]
      exact h4 (fperm f) (fperm g) (fperm.injective.ne hfg) (τ f a) (τ g b)

/-- A compensated automorphism fixing the configuration preserves its first-order system. -/
theorem compensated_mem_firstOrderSystem (g : Glennie.Albert →ₗ[ℝ] Glennie.Albert)
    (hg : IsNativeAut g) (σ : Fin 13 → Fin 3) (p : Fin 39 → Glennie.Albert)
    (hp : ∀ i, g (p (outcomeShift σ i)) = p i) {δ : Fin 39 → Glennie.Albert}
    (hδ : δ ∈ firstOrderSystem p) : compensated g (outcomeShift σ) δ ∈ firstOrderSystem p := by
  have hδ' : (fun i => δ (outcomeShift σ i)) ∈ firstOrderSystem (fun i => p (outcomeShift σ i)) :=
    (relabel_mem_firstOrderSystem_iff (Equiv.refl _) (fun f => Equiv.addRight (σ f)) p δ).2 hδ
  have hmap := map_mem_firstOrderSystem g hg hδ'
  have hpeq : (fun i => g (p (outcomeShift σ i))) = p := funext hp
  rw [hpeq] at hmap
  exact hmap

/-! ## The standard anchored form is fixed by `R0` with its shift -/

/-- The hidden points of the standard anchored form, in frame/outcome coordinates. -/
private theorem stdAnchored_hidden (q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian})
    (W : UnitaryErrorBases.Family) (f : Fin 13) (hf : 4 ≤ f.val) (a : Fin 3) :
    stdAnchored q W (framePointIndex f a) =
      nativeComplementaryPoint ((UnitaryErrorBases.ThreeCycleFourier.omega ^ a.val) •
        W (hiddenFrameEquiv.symm ⟨f.val - 4, by have := f.isLt; omega⟩)) := by
  have h0 : ¬ (framePointIndex f a).val < 12 := by
    rw [framePointIndex_val]; omega
  have h1 : (framePointIndex f a).val % 3 = a.val := by
    rw [framePointIndex_val]; omega
  have h2 : (framePointIndex f a).val / 3 - 4 = f.val - 4 := by
    rw [framePointIndex_val]; omega
  unfold stdAnchored
  simp only [h0, ↓reduceDIte, h1, h2]

/-- The visible points of the standard anchored form. -/
private theorem stdAnchored_visible (q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian})
    (W : UnitaryErrorBases.Family) (f : Fin 13) (hf : f.val < 4) (a : Fin 3) :
    ∃ h, stdAnchored q W (framePointIndex f a) = includeHermitianMatrix h := by
  have h0 : (framePointIndex f a).val < 12 := by
    rw [framePointIndex_val]; omega
  unfold stdAnchored
  simp only [h0, ↓reduceDIte]
  exact ⟨_, rfl⟩

private theorem omega_shift (a : Fin 3) :
    UnitaryErrorBases.ThreeCycleFourier.omega *
        UnitaryErrorBases.ThreeCycleFourier.omega ^ (a + 2).val =
      UnitaryErrorBases.ThreeCycleFourier.omega ^ a.val := by
  have h3 := UnitaryErrorBases.ThreeCycleFourier.omega_cube
  fin_cases a
  · simp only [Fin.zero_eta, Fin.isValue, zero_add, Fin.val_two, pow_zero]
    rw [← pow_succ', h3]
  · show _ * _ ^ ((1 : Fin 3) + 2).val = _ ^ (1 : Fin 3).val
    rw [show ((1 : Fin 3) + 2) = 0 from rfl]
    simp
  · show _ * _ ^ ((2 : Fin 3) + 2).val = _ ^ (2 : Fin 3).val
    rw [show ((2 : Fin 3) + 2) = 1 from rfl]
    simp [pow_two]

/-- `R0` with its compensating shift fixes the standard anchored configuration. -/
private theorem R0_stdAnchored' (q : Fin 4 → Fin 3 → {a : TitsComplexMatrix // a.IsHermitian})
    (W : UnitaryErrorBases.Family) (i : Fin 39) :
    R0 (stdAnchored q W (stdShift i)) = stdAnchored q W i := by
  obtain ⟨f, a, rfl⟩ : ∃ f a, i = framePointIndex f a :=
    ⟨⟨i.val / 3, by omega⟩, ⟨i.val % 3, by omega⟩,
      Fin.ext (by rw [framePointIndex_val]; show i.val = 3 * (i.val / 3) + i.val % 3; omega)⟩
  simp only [stdShift, outcomeShift, pointRelabel_framePointIndex, Equiv.refl_apply,
    Equiv.coe_addRight]
  by_cases hf : f.val < 4
  · simp only [hf, ↓reduceIte, add_zero]
    obtain ⟨h, hh⟩ := stdAnchored_visible q W f hf a
    rw [hh, R0]
    exact nativeRightMultiply_includeHermitianMatrix _ h
  · simp only [hf, ↓reduceIte]
    rw [stdAnchored_hidden q W f (by omega), stdAnchored_hidden q W f (by omega), R0]
    have key : ∀ (k : ℕ) (M : TitsComplexMatrix),
        (UnitaryErrorBases.ThreeCycleFourier.omega ^ k • M) *
            (UnitaryErrorBases.ThreeCycleFourier.omega • (1 : TitsComplexMatrix)) =
          (UnitaryErrorBases.ThreeCycleFourier.omega *
            UnitaryErrorBases.ThreeCycleFourier.omega ^ k) • M := by
      intro k M
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_comm]
    exact (nativeRightMultiply_complementaryPoint _ _).trans
      (congrArg nativeComplementaryPoint ((key _ _).trans (congrArg (· • _) (omega_shift a))))

/-- The anchor generator fixes the configuration, with its compensating shift, given a binding. -/
theorem AnchorBinding.generator_fixes {ρ : Module.End ℝ Glennie.Albert} {σ : Fin 13 → Fin 3}
    {P : Fin 39 → Glennie.Albert} {d : UnitaryErrorBases.PhaseTriple} (b : AnchorBinding ρ σ P d) :
    ∀ i, ρ (P (outcomeShift σ i)) = P i := by
  intro i
  obtain ⟨j, rfl⟩ := (pointRelabel b.fperm b.τ).surjective i
  apply b.Ψ_injective
  have hc : ∀ x, b.Ψ (ρ x) = R0 (b.Ψ x) := fun x => LinearMap.congr_fun b.conj x
  rw [hc, b.shift_compat, b.form, b.form, R0_stdAnchored']

/-- A binding gives a real-linear equivalence between the fixed first-order subspace and the standard
anchored one, by `δ ↦ (i ↦ Ψ (δ (λ i)))`. -/
theorem AnchorBinding.fixedEquiv {ρ : Module.End ℝ Glennie.Albert} {σ : Fin 13 → Fin 3}
    {P : Fin 39 → Glennie.Albert} {d : UnitaryErrorBases.PhaseTriple} (b : AnchorBinding ρ σ P d) :
    Nonempty (↥(fixedSpace (compensated ρ (outcomeShift σ)) ⊓ firstOrderSystem P) ≃ₗ[ℝ]
      ↥(fixedSpace (compensated R0 stdShift) ⊓ firstOrderSystem (stdAnchored b.q b.W))) := by
  have : FiniteDimensional ℝ Glennie.Albert := LinearEquiv.finiteDimensional upperCoordinateEquiv.symm
  set π := pointRelabel b.fperm b.τ with hπdef
  set Φ := compensated b.Ψ π with hΦdef
  have hΨsurj : Function.Surjective b.Ψ := LinearMap.injective_iff_surjective.mp b.Ψ_injective
  have hΦinj : Function.Injective Φ := by
    intro δ δ' h
    funext j
    obtain ⟨i, rfl⟩ := π.surjective j
    exact b.Ψ_injective (congr_fun h i)
  have hΦsurj : Function.Surjective Φ := by
    intro ε
    refine ⟨fun j => Function.surjInv hΨsurj (ε (π.symm j)), funext fun i => ?_⟩
    rw [hΦdef, compensated_apply, Function.surjInv_eq hΨsurj, Equiv.symm_apply_apply]
  let Φe : (Fin 39 → Glennie.Albert) ≃ₗ[ℝ] (Fin 39 → Glennie.Albert) :=
    LinearEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩
  have hc : ∀ x, b.Ψ (ρ x) = R0 (b.Ψ x) := fun x => LinearMap.congr_fun b.conj x
  have hcomm : ∀ δ, compensated R0 stdShift (Φ δ) = Φ (compensated ρ (outcomeShift σ) δ) := by
    intro δ
    funext i
    rw [compensated_apply, hΦdef, compensated_apply, compensated_apply, compensated_apply, hc,
      b.shift_compat]
  have hform : stdAnchored b.q b.W = fun i => b.Ψ (P (π i)) := funext fun i => (b.form i).symm
  have key : ∀ δ, Φ δ ∈ fixedSpace (compensated R0 stdShift) ⊓
      firstOrderSystem (stdAnchored b.q b.W) ↔
      δ ∈ fixedSpace (compensated ρ (outcomeShift σ)) ⊓ firstOrderSystem P := by
    intro δ
    rw [Submodule.mem_inf, Submodule.mem_inf, mem_fixedSpace, mem_fixedSpace, hcomm,
      hΦinj.eq_iff, hform]
    have hΦδ : Φ δ = fun i => b.Ψ ((fun j => δ (π j)) i) := funext fun i => compensated_apply _ _ _ _
    rw [hΦδ, map_mem_firstOrderSystem_iff b.Ψ b.Ψ_aut b.Ψ_injective (fun j => P (π j))
      (fun j => δ (π j)), hπdef, relabel_mem_firstOrderSystem_iff]
  have hmap : Submodule.map (Φe : (Fin 39 → Glennie.Albert) →ₗ[ℝ] (Fin 39 → Glennie.Albert))
      (fixedSpace (compensated ρ (outcomeShift σ)) ⊓ firstOrderSystem P) =
      fixedSpace (compensated R0 stdShift) ⊓ firstOrderSystem (stdAnchored b.q b.W) := by
    ext ε
    constructor
    · rintro ⟨δ, hδ, rfl⟩
      exact (key δ).2 hδ
    · intro hε
      obtain ⟨δ, rfl⟩ := hΦsurj ε
      exact ⟨δ, (key δ).1 hε, rfl⟩
  rw [← hmap]
  exact ⟨Φe.submoduleMap _⟩

/-- A binding transports the fixed first-order subspace to the standard anchored one. -/
theorem AnchorBinding.finrank_fixed_eq {ρ : Module.End ℝ Glennie.Albert} {σ : Fin 13 → Fin 3}
    {P : Fin 39 → Glennie.Albert} {d : UnitaryErrorBases.PhaseTriple} (b : AnchorBinding ρ σ P d) :
    Module.finrank ℝ ↥(fixedSpace (compensated ρ (outcomeShift σ)) ⊓ firstOrderSystem P) =
      Module.finrank ℝ ↥(fixedSpace (compensated R0 stdShift) ⊓ firstOrderSystem (stdAnchored b.q b.W)) := by
  obtain ⟨e⟩ := b.fixedEquiv
  exact e.finrank_eq

end CKM.NativeFirstOrder
