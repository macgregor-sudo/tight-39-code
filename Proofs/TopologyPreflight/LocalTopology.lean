module

public import TopologyPreflight.BrouwerAdapter
public import TopologyPreflight.ConditionalDimension

@[expose] public section

/-!
The local open-chart dimension interface. No native code, orbit action or
manifold model is introduced here. The interface is independent of native configuration geometry.
-/

namespace TopologyReuse

section RadialInjection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private noncomputable def radialUnit (x : E) : E := (1 + ‖x‖)⁻¹ • x

private theorem radialDenomPos (x : E) : 0 < 1 + ‖x‖ := by positivity

private theorem norm_radialUnit (x : E) :
    ‖radialUnit x‖ = ‖x‖ / (1 + ‖x‖) := by
  unfold radialUnit
  rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr (radialDenomPos x)).le,
    div_eq_mul_inv, mul_comm]

private theorem norm_radialUnit_lt_one (x : E) : ‖radialUnit x‖ < 1 := by
  rw [norm_radialUnit]
  exact (div_lt_one (radialDenomPos x)).mpr (by linarith)

private theorem continuous_radialUnit : Continuous (radialUnit : E → E) := by
  exact ((continuous_const.add continuous_norm).inv₀
    (fun x => (radialDenomPos x).ne')).smul continuous_id

private theorem injective_radialUnit : Function.Injective (radialUnit : E → E) := by
  intro x y hxy
  have hn : ‖x‖ = ‖y‖ := by
    have hnorm := congrArg norm hxy
    rw [norm_radialUnit, norm_radialUnit] at hnorm
    have hcross := (div_eq_div_iff (radialDenomPos x).ne'
      (radialDenomPos y).ne').mp hnorm
    nlinarith
  have hs := congrArg (fun z : E => (1 + ‖x‖) • z) hxy
  simpa only [radialUnit, hn, smul_smul,
    mul_inv_cancel₀ (radialDenomPos y).ne', one_smul] using hs

/-- A nonempty open set contains a continuous injective image of its model space. -/
theorem exists_continuous_injective_into_open {U : Set E}
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ f : E → U, Continuous f ∧ Function.Injective f := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU a ha
  let b : E → E := fun x => a + r • radialUnit x
  have hbmem (x : E) : b x ∈ U := by
    apply hball
    change dist (a + r • radialUnit x) a < r
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
    simpa only [mul_one] using
      mul_lt_mul_of_pos_left (norm_radialUnit_lt_one x) hr
  let f : E → U := fun x => ⟨b x, hbmem x⟩
  refine ⟨f, ?_, ?_⟩
  · exact (continuous_const.add (continuous_const.smul continuous_radialUnit)).subtype_mk _
  · intro x y hxy
    have hv : b x = b y := congrArg Subtype.val hxy
    have hs : r • radialUnit x = r • radialUnit y := add_left_cancel hv
    have ht := congrArg (fun z : E => r⁻¹ • z) hs
    apply injective_radialUnit
    simpa only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] using ht

end RadialInjection

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Homeomorphic nonempty open subsets have model spaces of the same dimension. -/
theorem finrank_eq_of_homeomorph_nonempty_open {U : Set E} {V : Set F}
    (hU : IsOpen U) (hV : IsOpen V) (hneU : U.Nonempty) (hneV : V.Nonempty)
    (e : U ≃ₜ V) : Module.finrank ℝ E = Module.finrank ℝ F := by
  obtain ⟨u, hu, hiu⟩ := exists_continuous_injective_into_open hU hneU
  obtain ⟨v, hv, hiv⟩ := exists_continuous_injective_into_open hV hneV
  have hEF : Module.finrank ℝ E ≤ Module.finrank ℝ F :=
    dim_le_of_injective_continuous (fun x => (e (u x) : F))
      (continuous_subtype_val.comp (e.continuous.comp hu))
      (Subtype.val_injective.comp (e.injective.comp hiu))
  have hFE : Module.finrank ℝ F ≤ Module.finrank ℝ E :=
    dim_le_of_injective_continuous (fun x => (e.symm (v x) : E))
      (continuous_subtype_val.comp (e.symm.continuous.comp hv))
      (Subtype.val_injective.comp (e.symm.injective.comp hiv))
  exact Nat.le_antisymm hEF hFE

end TopologyReuse
