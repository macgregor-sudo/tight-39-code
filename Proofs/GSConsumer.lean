module

public import GSMain

@[expose] public section

/-!
# Group/slice Consumer

Uses the endpoint with only the unit-phase hypothesis. It shows the actual group (all bijective
real-linear native maps preserving the native Jordan product) and all 2184 original residual rows
(literally `originalF`), and instantiates the endpoint at a resonant phase (`ξ = 1`, resonance counts
`r = 3, 1, 1, 1`) and at a nonresonant phase (`ξ = (1, i, −1, (3+4i)/5)`, all `r_H = 0`).
-/

noncomputable section

namespace CKM.NativeGroupSliceConsumer

open Glennie NativePolynomial CKM.NativeGroupSlice CKM.NativeFirstOrder ConfigurationResidualIndices
open Option2.NativeStress.AnalyticDerivative (originalF)
open scoped Topology

/-- The actual group `G`: exactly the bijective real-linear native maps preserving `jordan`. -/
example (A : CEnd) :
    A ∈ autC ↔ Function.Bijective (coordEnd.symm A) ∧
      ∀ x y, coordEnd.symm A (jordan x y) = jordan (coordEnd.symm A x) (coordEnd.symm A y) :=
  (native_group_slice (fun _ => 1) (fun _ => by simp)).1 A

/-- The residual map is literally all 2184 original rows with the constants `1/2` and `1/3`. -/
example (C : Cfg) (r : Fin 2184) :
    originalF C r =
      MvPolynomial.eval (PartialAction.pack C) (ConfigurationResiduals.fRow (1 / 2 : ℝ) (1 / 3 : ℝ) r) :=
  rfl

/-- Every original row, off shell, at an arbitrary group element and configuration. -/
example (A : CEnd) (hA : A ∈ autC) (C : Cfg) (r : Fin 2184) :
    originalF (actC A C) r = rowAction A (originalF C) r :=
  congrFun (originalF_actC hA C) r

/-- The endpoint at an arbitrary unit phase, used through its slice conclusions. -/
example (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Module.finrank ℝ (normalC ξ) = 1001 ∧
      (∀ A : CEnd, actC A (literalCfg ξ) = literalCfg ξ ↔ A = 1) ∧
      (∀ p, originalF (sliceChart ξ p) = 0 ↔ originalF (literalCfg ξ + p.2) = 0) ∧
      (∃ W ∈ 𝓝 (literalCfg ξ), ∀ s ∈ W ∩ sliceSet ξ, ∀ t ∈ W ∩ sliceSet ξ,
        ∀ A ∈ autC, actC A s = t → s = t) ∧
      ∃ W : Set Cfg, IsOpen W ∧ literalCfg ξ ∈ W ∧ Topology.IsOpenEmbedding (sliceToOrbit ξ W) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hstab, -, -, -, -, hN, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, hzero, -, hloc, hemb⟩ := native_group_slice ξ hξ
  exact ⟨hN, hstab, hzero, hloc, hemb⟩

/-- A3's resonance count of an anchor triple, through the literal phases (as in A4's Consumer). -/
theorem resonanceCount_anchorTriple (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) :
    UnitaryErrorBases.resonanceCount (anchorTriple ξ hξ H) =
      (if anchorPhases ξ H 0 ^ 3 = 1 then 1 else 0) + (if anchorPhases ξ H 1 ^ 3 = 1 then 1 else 0) +
        (if anchorPhases ξ H 2 ^ 3 = 1 then 1 else 0) :=
  UnitaryErrorBases.ThreeCycleMatrix.resonanceCount_eq_three_indicators _

/-- The CKM point `ξ = 1` is a unit phase. -/
theorem isUnitPhase_one : IsUnitPhase (fun _ => 1) := fun _ => by simp

/-- `ξ = 1` is resonant: `r = 3, 1, 1, 1`. -/
theorem resonanceCount_one (H : Fin 4) :
    UnitaryErrorBases.resonanceCount (anchorTriple (fun _ => 1) isUnitPhase_one H) = ![3, 1, 1, 1] H := by
  have hneg : ((-1 : ℂ)) ^ 3 ≠ 1 := by norm_num
  rw [resonanceCount_anchorTriple]
  fin_cases H <;> simp [anchorPhases, hneg]

/-- **Resonant use** (`ξ = 1`). -/
example :
    (∀ H, UnitaryErrorBases.resonanceCount (anchorTriple (fun _ => 1) isUnitPhase_one H) = ![3, 1, 1, 1] H) ∧
      originalF (literalCfg fun _ => 1) = 0 ∧
      Module.finrank ℝ (orbitC fun _ => 1) = 52 ∧
      Module.finrank ℝ (normalC fun _ => 1) = 1001 ∧
      (∀ A : CEnd, actC A (literalCfg fun _ => 1) = literalCfg (fun _ => 1) ↔ A = 1) ∧
      (∃ W ∈ 𝓝 (literalCfg fun _ => 1), ∀ s ∈ W ∩ sliceSet (fun _ => 1), ∀ t ∈ W ∩ sliceSet (fun _ => 1),
        ∀ A ∈ autC, actC A s = t → s = t) ∧
      ∃ W : Set Cfg, IsOpen W ∧ literalCfg (fun _ => 1) ∈ W ∧
        Topology.IsOpenEmbedding (sliceToOrbit (fun _ => 1) W) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hstab, -, -, -, hO, hN, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, hP, hloc, hemb⟩ := native_group_slice (fun _ => 1) isUnitPhase_one
  exact ⟨resonanceCount_one, hP, hO, hN, hstab, hloc, hemb⟩

/-- A nonresonant phase `ξ = (1, i, −1, (3+4i)/5)`. -/
def xiNonres : Fin 4 → ℂ := ![1, Complex.I, -1, ⟨3 / 5, 4 / 5⟩]

theorem isUnitPhase_xiNonres : IsUnitPhase xiNonres := by
  intro a
  fin_cases a <;> norm_num [xiNonres, Complex.normSq_apply]

/-- `q⁻¹ = conj q` for `q = (3+4i)/5`. -/
theorem xiNonres_q_inv : (⟨3 / 5, 4 / 5⟩ : ℂ)⁻¹ = ⟨3 / 5, -4 / 5⟩ := by
  apply inv_eq_of_mul_eq_one_right
  apply Complex.ext <;> simp <;> norm_num

/-- None of the twelve signed phases of `xiNonres` has cube one. -/
theorem xiNonres_phase_cube_ne_one (H : Fin 4) (j : Fin 3) : anchorPhases xiNonres H j ^ 3 ≠ 1 := by
  rw [Ne, Complex.ext_iff]
  fin_cases H <;> fin_cases j <;>
    simp [anchorPhases, xiNonres, xiNonres_q_inv, pow_succ, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.normSq_apply] <;> norm_num

/-- `xiNonres` is nonresonant: every `r_H = 0`. -/
theorem resonanceCount_xiNonres (H : Fin 4) :
    UnitaryErrorBases.resonanceCount (anchorTriple xiNonres isUnitPhase_xiNonres H) = 0 := by
  rw [resonanceCount_anchorTriple]
  simp only [Nat.add_eq_zero_iff, ite_eq_right_iff, one_ne_zero, imp_false]
  exact ⟨⟨xiNonres_phase_cube_ne_one H 0, xiNonres_phase_cube_ne_one H 1⟩, xiNonres_phase_cube_ne_one H 2⟩

/-- **Nonresonant use** (`ξ = (1, i, −1, (3+4i)/5)`). -/
example :
    (∀ H, UnitaryErrorBases.resonanceCount (anchorTriple xiNonres isUnitPhase_xiNonres H) = 0) ∧
      originalF (literalCfg xiNonres) = 0 ∧
      Module.finrank ℝ (orbitC xiNonres) = 52 ∧
      Module.finrank ℝ (normalC xiNonres) = 1001 ∧
      (∀ A : CEnd, actC A (literalCfg xiNonres) = literalCfg xiNonres ↔ A = 1) ∧
      (∃ W ∈ 𝓝 (literalCfg xiNonres), ∀ s ∈ W ∩ sliceSet xiNonres, ∀ t ∈ W ∩ sliceSet xiNonres,
        ∀ A ∈ autC, actC A s = t → s = t) ∧
      ∃ W : Set Cfg, IsOpen W ∧ literalCfg xiNonres ∈ W ∧
        Topology.IsOpenEmbedding (sliceToOrbit xiNonres W) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hstab, -, -, -, hO, hN, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, hP, hloc, hemb⟩ := native_group_slice xiNonres isUnitPhase_xiNonres
  exact ⟨resonanceCount_xiNonres, hP, hO, hN, hstab, hloc, hemb⟩

end CKM.NativeGroupSliceConsumer

#print axioms CKM.NativeGroupSlice.native_group_slice
#print axioms CKM.NativeGroupSliceConsumer.resonanceCount_one
#print axioms CKM.NativeGroupSliceConsumer.resonanceCount_xiNonres
