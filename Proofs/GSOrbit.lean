module

public import GSGroup
public import A4Orbit

@[expose] public section

/-!
# The labelled action on configurations, the free orbit and the normal space

* `Cfg = PartialAction.Configuration ℝ = Fin 39 → Fin 27 → ℝ`: the literal 39-point configuration
  space in its original 1053 real coordinates (the domain of `originalF`), i.e. `Fin 39 → J` read
  in upper coordinates (`decodeVariation`).
* `actC A C = (i ↦ A (C i))`, a continuous bilinear map; it is a monoid action.
* `actC_literalCfg_eq_iff`: at every unit phase the labelled stabilizer of the literal configuration
  `P = literalCfg ξ` is trivial (the 39 literal points span `J`: A4's `span_literalPoint`).
* `orbitMapC ξ A = actC A P`; on `derC` it is the derivative of the orbit map through the identity
  chart (`hasStrictFDerivAt_orbit`), it is injective, and its image `orbitC ξ` is A4's
  `orbitSpace ξ` (`orbitC_eq_orbitSpace`) of dimension 52.
* `cfgPairing`: the finite-sum trace inner product on configurations (`Σ_i coordinatePairing`, the
  original pair-overlap pairing, `= Σ_i trace (x_i ∘ y_i)`); it is `G`-invariant and positive
  definite. `normalC ξ = (orbitC ξ)ᗮ` for it, of dimension `1053 - 52 = 1001`, and it is a
  complement of `orbitC ξ`.
-/

noncomputable section

namespace CKM.NativeGroupSlice

open Glennie NativePolynomial CKM.NativeDerivationTriality CKM.NativeFirstOrder

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The literal labelled configuration space, in the original 1053 real coordinates. -/
abbrev Cfg := PartialAction.Configuration ℝ

/-- The pointwise action, linear in the endomorphism. -/
def actLin : CEnd →ₗ[ℝ] Cfg →L[ℝ] Cfg where
  toFun A := ContinuousLinearMap.pi fun i => A.comp (ContinuousLinearMap.proj i)
  map_add' := by
    intro A B
    ext C i j
    rfl
  map_smul' := by
    intro c A
    ext C i j
    rfl

/-- The labelled action `(A • C) i = A (C i)`, as a continuous bilinear map. -/
def actC : CEnd →L[ℝ] Cfg →L[ℝ] Cfg := LinearMap.toContinuousLinearMap actLin

theorem actC_apply (A : CEnd) (C : Cfg) (i : Fin 39) : actC A C i = A (C i) := by
  rfl

theorem actC_one : actC 1 = ContinuousLinearMap.id ℝ Cfg := by
  ext C i j
  rfl

theorem actC_mul (A B : CEnd) : actC (A * B) = (actC A).comp (actC B) := by
  ext C i j
  rfl

/-- The 39 literal points span the coordinate space (transport of A4's `span_literalPoint`). -/
theorem orbit_span_literalCfg (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Submodule.span ℝ (Set.range (literalCfg ξ)) = ⊤ := by
  have hr : Set.range (literalCfg ξ) =
      (upperCoordinateEquiv.toLinearMap : Albert →ₗ[ℝ] Coord) ''
        Set.range (CKM.NativeFirstOrder.literalPoint ξ) := by
    rw [← Set.range_comp]
    rfl
  rw [hr, Submodule.span_image, CKM.NativeIntrinsicTriality.span_literalPoint ξ hξ,
    Submodule.map_top, LinearEquiv.range]

/-- A continuous linear endomorphism vanishing on the 39 literal points is zero; one fixing them is
the identity. -/
theorem orbit_eq_of_literalCfg (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) {A B : CEnd}
    (h : ∀ i, A (literalCfg ξ i) = B (literalCfg ξ i)) : A = B := by
  have hl : (A : Coord →ₗ[ℝ] Coord) = (B : Coord →ₗ[ℝ] Coord) :=
    LinearMap.ext_on_range (orbit_span_literalCfg ξ hξ) h
  ext v : 1
  exact LinearMap.congr_fun hl v

/-- **Trivial labelled stabilizer** at every unit phase: a linear map fixing all 39 literal points is
the identity. -/
theorem actC_literalCfg_eq_iff (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (A : CEnd) :
    actC A (literalCfg ξ) = literalCfg ξ ↔ A = 1 := by
  constructor
  · intro h
    refine orbit_eq_of_literalCfg ξ hξ fun i => ?_
    rw [← actC_apply, h]
    rfl
  · rintro rfl
    rw [actC_one]
    rfl

/-- The orbit map at the literal configuration, `A ↦ (i ↦ A (P i))`. -/
def orbitMapC (ξ : Fin 4 → ℂ) : CEnd →L[ℝ] Cfg := actC.flip (literalCfg ξ)

theorem orbitMapC_apply (ξ : Fin 4 → ℂ) (A : CEnd) (i : Fin 39) :
    orbitMapC ξ A i = A (literalCfg ξ i) := by
  rfl

theorem orbitMapC_injective (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : Function.Injective (orbitMapC ξ) := by
  refine (injective_iff_map_eq_zero (orbitMapC ξ)).2 fun A hA => ?_
  refine orbit_eq_of_literalCfg ξ hξ fun i => ?_
  rw [← orbitMapC_apply, hA]
  rfl

/-- The actual orbit tangent: the image of all native derivations. -/
def orbitC (ξ : Fin 4 → ℂ) : Submodule ℝ Cfg := derC.map (orbitMapC ξ : CEnd →ₗ[ℝ] Cfg)

/-- The orbit map composed with the coordinate reading of native endomorphisms is A4's `evalDer`. -/
theorem orbit_orbitMapC_comp_coordEnd (ξ : Fin 4 → ℂ) :
    (orbitMapC ξ : CEnd →ₗ[ℝ] Cfg) ∘ₗ coordEnd.toLinearMap = CKM.NativeIntrinsicTriality.evalDer ξ := by
  refine LinearMap.ext fun g => funext fun i => ?_
  show orbitMapC ξ (coordEnd g) i = CKM.NativeIntrinsicTriality.evalDer ξ g i
  rw [orbitMapC_apply, coordEnd_apply, CKM.NativeIntrinsicTriality.evalDer_apply]
  rfl

theorem orbitC_eq_orbitSpace (ξ : Fin 4 → ℂ) : orbitC ξ = CKM.NativeIntrinsicTriality.orbitSpace ξ := by
  rw [orbitC, derC_eq_map, ← Submodule.map_comp, orbit_orbitMapC_comp_coordEnd]
  rfl

theorem finrank_orbitC (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : Module.finrank ℝ (orbitC ξ) = 52 := by
  rw [orbitC_eq_orbitSpace]
  exact CKM.NativeIntrinsicTriality.finrank_orbitSpace ξ hξ

/-- The derivative of the action on `P` through the identity chart is `D ↦ (i ↦ D (P i))`. -/
theorem hasStrictFDerivAt_orbit (ξ : Fin 4 → ℂ) :
    HasStrictFDerivAt (fun D : derC => actC (groupChart D) (literalCfg ξ))
      ((orbitMapC ξ).comp derC.subtypeL) 0 := by
  exact (orbitMapC ξ).hasStrictFDerivAt.comp (0 : derC) hasStrictFDerivAt_groupChart

/-! ## The finite-sum trace inner product and the normal space -/

/-- The finite-sum trace inner product on configurations. -/
def cfgPairing (C C' : Cfg) : ℝ := ∑ i, CoordinateMaps.coordinatePairing (C i) (C' i)

theorem cfgPairing_eq_trace (C C' : Cfg) :
    cfgPairing C C' = ∑ i, trace (jordan (fromUpperCoordinates (C i)) (fromUpperCoordinates (C' i))) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := CoordinateMaps.coordinatePairing_upperCoordinates_eq_native_trace
    (fromUpperCoordinates (C i)) (fromUpperCoordinates (C' i))
  rwa [upperCoordinates_fromUpperCoordinates, upperCoordinates_fromUpperCoordinates] at h

theorem cfgPairing_actC {A : CEnd} (hA : A ∈ autC) (C C' : Cfg) :
    cfgPairing (actC A C) (actC A C') = cfgPairing C C' := by
  simp only [cfgPairing, actC_apply, autC_pairing hA]

theorem cfgPairing_self_pos {C : Cfg} (hC : C ≠ 0) : 0 < cfgPairing C C := by
  rw [cfgPairing_eq_trace]
  obtain ⟨i, hi⟩ : ∃ i, C i ≠ 0 := by
    by_contra h
    push Not at h
    exact hC (funext h)
  refine Finset.sum_pos' (fun j _ => Glennie.inner_self_nonneg _) ⟨i, Finset.mem_univ _, ?_⟩
  refine lt_of_le_of_ne (Glennie.inner_self_nonneg _) fun h0 => hi ?_
  have hx := (Glennie.inner_self_eq_zero (fromUpperCoordinates (C i))).1 h0.symm
  rw [← upperCoordinates_fromUpperCoordinates (C i), hx]
  funext k
  fin_cases k <;> rfl

theorem orbit_cfgPairing_add_left (C C' D : Cfg) :
    cfgPairing (C + C') D = cfgPairing C D + cfgPairing C' D := by
  simp only [cfgPairing, CoordinateMaps.coordinatePairing, Pi.add_apply, mul_add, add_mul,
    Finset.sum_add_distrib]

theorem orbit_cfgPairing_smul_left (c : ℝ) (C D : Cfg) :
    cfgPairing (c • C) D = c * cfgPairing C D := by
  simp only [cfgPairing, CoordinateMaps.coordinatePairing, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem orbit_cfgPairing_comm (C D : Cfg) : cfgPairing C D = cfgPairing D C := by
  simp only [cfgPairing, CoordinateMaps.coordinatePairing]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem orbit_cfgPairing_add_right (C D D' : Cfg) :
    cfgPairing C (D + D') = cfgPairing C D + cfgPairing C D' := by
  rw [orbit_cfgPairing_comm, orbit_cfgPairing_add_left, orbit_cfgPairing_comm D,
    orbit_cfgPairing_comm D']

theorem orbit_cfgPairing_smul_right (c : ℝ) (C D : Cfg) :
    cfgPairing C (c • D) = c * cfgPairing C D := by
  rw [orbit_cfgPairing_comm, orbit_cfgPairing_smul_left, orbit_cfgPairing_comm]

/-- `cfgPairing` as a Mathlib bilinear form. -/
def orbitPairingForm : LinearMap.BilinForm ℝ Cfg :=
  LinearMap.mk₂ ℝ cfgPairing orbit_cfgPairing_add_left orbit_cfgPairing_smul_left
    orbit_cfgPairing_add_right orbit_cfgPairing_smul_right

theorem orbitPairingForm_apply (C D : Cfg) : orbitPairingForm C D = cfgPairing C D := rfl

/-- The normal space `N(ξ) = O(ξ)ᗮ` for the finite-sum trace inner product. -/
def normalC (ξ : Fin 4 → ℂ) : Submodule ℝ Cfg where
  carrier := {n | ∀ u ∈ orbitC ξ, cfgPairing u n = 0}
  add_mem' := by
    intro a b ha hb u hu
    rw [orbit_cfgPairing_add_right, ha u hu, hb u hu, add_zero]
  zero_mem' := by
    intro u _
    simpa using orbit_cfgPairing_smul_right 0 u 0
  smul_mem' := by
    intro c a ha u hu
    rw [orbit_cfgPairing_smul_right, ha u hu, mul_zero]

theorem mem_normalC_iff (ξ : Fin 4 → ℂ) (n : Cfg) :
    n ∈ normalC ξ ↔ ∀ u ∈ orbitC ξ, cfgPairing u n = 0 := Iff.rfl

/-- `normalC ξ` is the kernel of `n ↦ (u ↦ cfgPairing u n)` on `orbitC ξ`. -/
def orbitNormalMap (ξ : Fin 4 → ℂ) : Cfg →ₗ[ℝ] Module.Dual ℝ (orbitC ξ) :=
  (orbitC ξ).subtype.dualMap ∘ₗ orbitPairingForm.flip

theorem orbit_normalC_eq_ker (ξ : Fin 4 → ℂ) : normalC ξ = LinearMap.ker (orbitNormalMap ξ) := by
  ext n
  rw [mem_normalC_iff, LinearMap.mem_ker]
  constructor
  · intro h
    ext u
    exact h u.1 u.2
  · intro h u hu
    exact LinearMap.congr_fun h ⟨u, hu⟩

theorem finrank_cfg : Module.finrank ℝ Cfg = 1053 := by
  simp [Module.finrank_pi_fintype]

theorem orbit_inf_normalC (ξ : Fin 4 → ℂ) : orbitC ξ ⊓ normalC ξ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  by_contra hne
  exact (cfgPairing_self_pos hne).ne' (hx.2 x hx.1)

theorem orbit_isCompl (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : IsCompl (orbitC ξ) (normalC ξ) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (orbitNormalMap ξ)
  have hrange : Module.finrank ℝ (LinearMap.range (orbitNormalMap ξ)) ≤ 52 := by
    calc Module.finrank ℝ (LinearMap.range (orbitNormalMap ξ))
        ≤ Module.finrank ℝ (Module.Dual ℝ (orbitC ξ)) := Submodule.finrank_le _
      _ = 52 := by rw [Subspace.dual_finrank_eq, finrank_orbitC ξ hξ]
  rw [← orbit_normalC_eq_ker, finrank_cfg] at hrn
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (orbitC ξ) (normalC ξ)
  rw [orbit_inf_normalC, finrank_bot, finrank_orbitC ξ hξ] at hsup
  refine IsCompl.of_eq (orbit_inf_normalC ξ) (Submodule.eq_top_of_finrank_eq ?_)
  have hle := Submodule.finrank_le (orbitC ξ ⊔ normalC ξ)
  rw [finrank_cfg] at hle ⊢
  omega

theorem finrank_normalC (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : Module.finrank ℝ (normalC ξ) = 1001 := by
  have h := Submodule.finrank_add_eq_of_isCompl (orbit_isCompl ξ hξ)
  rw [finrank_orbitC ξ hξ, finrank_cfg] at h
  omega

theorem isCompl_orbitC_normalC (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : IsCompl (orbitC ξ) (normalC ξ) := by
  exact orbit_isCompl ξ hξ

end CKM.NativeGroupSlice

#print axioms CKM.NativeGroupSlice.actC_apply
#print axioms CKM.NativeGroupSlice.actC_one
#print axioms CKM.NativeGroupSlice.actC_mul
#print axioms CKM.NativeGroupSlice.actC_literalCfg_eq_iff
#print axioms CKM.NativeGroupSlice.orbitMapC_apply
#print axioms CKM.NativeGroupSlice.orbitMapC_injective
#print axioms CKM.NativeGroupSlice.orbitC_eq_orbitSpace
#print axioms CKM.NativeGroupSlice.finrank_orbitC
#print axioms CKM.NativeGroupSlice.hasStrictFDerivAt_orbit
#print axioms CKM.NativeGroupSlice.cfgPairing_eq_trace
#print axioms CKM.NativeGroupSlice.cfgPairing_actC
#print axioms CKM.NativeGroupSlice.cfgPairing_self_pos
#print axioms CKM.NativeGroupSlice.normalC
#print axioms CKM.NativeGroupSlice.finrank_cfg
#print axioms CKM.NativeGroupSlice.finrank_normalC
#print axioms CKM.NativeGroupSlice.isCompl_orbitC_normalC
