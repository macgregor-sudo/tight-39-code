module

public import NativeTrialityPeirce

/-!
# The diagonal-variation section and the splitting of the native derivations

For `v` in the Peirce slot `J_ij`, the literal inner derivation `δ_{ij,v} = 4 [L_v, L_{e_i}]` (the native
`innerDerLinear v e_i`, times four) satisfies `δ e_i = v`, `δ e_j = -v`, `δ e_k = 0`.

`diagonalVariation D = ((D e₀).o01, (D e₀).o02, (D e₁).o12)` records the three octonion directions in
which `D` moves the diagonal frame; `innerSection` is the linear section
`(a, b, c) ↦ δ_{01,a} + δ_{02,b} + δ_{12,c}`. A derivation lies in the diagonal fixer iff its diagonal
variation vanishes (differentiate `e_i² = e_i`, `e_i e_j = 0`, `Σ e_i = 1`), giving the real linear
decomposition `Der J ≃ (O × O × O) × (diagonal fixer)`. This is a vector-space splitting, not a direct
product of Lie algebras.
-/

@[expose] public section

noncomputable section

namespace CKM.NativeDerivationTriality

open Glennie Reuse

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## Helper products among idempotents and slots

Adapted from `RealOrbitSlice/Native/DerivationDimension/Rigidity.lean` (earlier first-party
work, package real-orbit-slice-2026-10-24), restated over the frozen `jordan_idem*_left` of
`NativeTrialityPeirce`. -/

theorem neg_o01 (x : Albert) : (-x).o01 = -x.o01 := rfl
theorem neg_o02 (x : Albert) : (-x).o02 = -x.o02 := rfl
theorem neg_o12 (x : Albert) : (-x).o12 = -x.o12 := rfl

theorem jordan_idem0_idem0 : jordan idem0 idem0 = idem0 := by
  rw [jordan_idem0_left]; apply Albert.extExplicit <;> simp [idem0]
theorem jordan_idem1_idem1 : jordan idem1 idem1 = idem1 := by
  rw [jordan_idem1_left]; apply Albert.extExplicit <;> simp [idem1]
theorem jordan_idem2_idem2 : jordan idem2 idem2 = idem2 := by
  rw [jordan_idem2_left]; apply Albert.extExplicit <;> simp [idem2]
theorem jordan_idem0_idem1 : jordan idem0 idem1 = 0 := by
  rw [jordan_idem0_left]; apply Albert.extExplicit <;> simp [idem1]
theorem jordan_idem0_idem2 : jordan idem0 idem2 = 0 := by
  rw [jordan_idem0_left]; apply Albert.extExplicit <;> simp [idem2]
theorem jordan_idem1_idem2 : jordan idem1 idem2 = 0 := by
  rw [jordan_idem1_left]; apply Albert.extExplicit <;> simp [idem2]
theorem jordan_idem1_idem0 : jordan idem1 idem0 = 0 := by
  rw [jordan_comm, jordan_idem0_idem1]
theorem jordan_idem2_idem0 : jordan idem2 idem0 = 0 := by
  rw [jordan_comm, jordan_idem0_idem2]
theorem jordan_idem2_idem1 : jordan idem2 idem1 = 0 := by
  rw [jordan_comm, jordan_idem1_idem2]

theorem jordan_idem0_slot01 (a : Octonion) : jordan idem0 (slot01 a) = (1/2 : ℝ) • slot01 a := by
  rw [jordan_idem0_left]; apply Albert.extExplicit <;> simp [slot01]
theorem jordan_idem1_slot01 (a : Octonion) : jordan idem1 (slot01 a) = (1/2 : ℝ) • slot01 a := by
  rw [jordan_idem1_left]; apply Albert.extExplicit <;> simp [slot01]
theorem jordan_idem2_slot01 (a : Octonion) : jordan idem2 (slot01 a) = 0 := by
  rw [jordan_idem2_left]; apply Albert.extExplicit <;> simp [slot01]
theorem jordan_idem0_slot02 (a : Octonion) : jordan idem0 (slot02 a) = (1/2 : ℝ) • slot02 a := by
  rw [jordan_idem0_left]; apply Albert.extExplicit <;> simp [slot02]
theorem jordan_idem2_slot02 (a : Octonion) : jordan idem2 (slot02 a) = (1/2 : ℝ) • slot02 a := by
  rw [jordan_idem2_left]; apply Albert.extExplicit <;> simp [slot02]
theorem jordan_idem1_slot02 (a : Octonion) : jordan idem1 (slot02 a) = 0 := by
  rw [jordan_idem1_left]; apply Albert.extExplicit <;> simp [slot02]
theorem jordan_idem1_slot12 (a : Octonion) : jordan idem1 (slot12 a) = (1/2 : ℝ) • slot12 a := by
  rw [jordan_idem1_left]; apply Albert.extExplicit <;> simp [slot12]
theorem jordan_idem2_slot12 (a : Octonion) : jordan idem2 (slot12 a) = (1/2 : ℝ) • slot12 a := by
  rw [jordan_idem2_left]; apply Albert.extExplicit <;> simp [slot12]
theorem jordan_idem0_slot12 (a : Octonion) : jordan idem0 (slot12 a) = 0 := by
  rw [jordan_idem0_left]; apply Albert.extExplicit <;> simp [slot12]

theorem slot01_add (a b : Octonion) : slot01 (a + b) = slot01 a + slot01 b := by
  apply Albert.extExplicit <;> simp [slot01]
theorem slot02_add (a b : Octonion) : slot02 (a + b) = slot02 a + slot02 b := by
  apply Albert.extExplicit <;> simp [slot02]
theorem slot12_add (a b : Octonion) : slot12 (a + b) = slot12 a + slot12 b := by
  apply Albert.extExplicit <;> simp [slot12]
theorem slot01_smul (r : ℝ) (a : Octonion) : slot01 (r • a) = r • slot01 a := by
  apply Albert.extExplicit <;> simp [slot01]
theorem slot02_smul (r : ℝ) (a : Octonion) : slot02 (r • a) = r • slot02 a := by
  apply Albert.extExplicit <;> simp [slot02]
theorem slot12_smul (r : ℝ) (a : Octonion) : slot12 (r • a) = r • slot12 a := by
  apply Albert.extExplicit <;> simp [slot12]

/-- The literal inner derivation `4 [L_v, L_e]`. -/
def peirceInner (v e : Albert) : Module.End ℝ Albert := (4 : ℝ) • innerDerLinear v e

theorem peirceInner_apply (v e z : Albert) :
    peirceInner v e z = (4 : ℝ) • (jordan v (jordan e z) - jordan e (jordan v z)) := rfl

theorem peirceInner_add_left (v w e : Albert) :
    peirceInner (v + w) e = peirceInner v e + peirceInner w e := by
  apply LinearMap.ext
  intro z
  simp only [LinearMap.add_apply, peirceInner_apply, jordan_add_left, jordan_add_right]
  module

theorem peirceInner_smul_left (r : ℝ) (v e : Albert) :
    peirceInner (r • v) e = r • peirceInner v e := by
  apply LinearMap.ext
  intro z
  simp only [LinearMap.smul_apply, peirceInner_apply, jordan_smul_left, jordan_smul_right]
  module

theorem peirceInner_mem (v e : Albert) : peirceInner v e ∈ jordanDerivations := by
  exact mem_jordanDerivations.mpr ((isJordanDerivation_innerDerLinear v e).smul 4)

/-! ## Peirce values (`δ e_i = v`, `δ e_j = -v`, `δ e_k = 0`) -/

theorem peirceInner_slot01_idem0 (a : Octonion) : peirceInner (slot01 a) idem0 idem0 = slot01 a := by
  rw [peirceInner_apply, jordan_idem0_idem0, jordan_comm (slot01 a) idem0, jordan_idem0_slot01,
    jordan_smul_right, jordan_idem0_slot01]
  module
theorem peirceInner_slot01_idem1 (a : Octonion) : peirceInner (slot01 a) idem0 idem1 = -slot01 a := by
  rw [peirceInner_apply, jordan_idem0_idem1, jordan_zero_right, jordan_comm (slot01 a) idem1,
    jordan_idem1_slot01, jordan_smul_right, jordan_idem0_slot01]
  module
theorem peirceInner_slot01_idem2 (a : Octonion) : peirceInner (slot01 a) idem0 idem2 = 0 := by
  rw [peirceInner_apply, jordan_idem0_idem2, jordan_zero_right, jordan_comm (slot01 a) idem2,
    jordan_idem2_slot01, jordan_zero_right]
  module
theorem peirceInner_slot02_idem0 (a : Octonion) : peirceInner (slot02 a) idem0 idem0 = slot02 a := by
  rw [peirceInner_apply, jordan_idem0_idem0, jordan_comm (slot02 a) idem0, jordan_idem0_slot02,
    jordan_smul_right, jordan_idem0_slot02]
  module
theorem peirceInner_slot02_idem2 (a : Octonion) : peirceInner (slot02 a) idem0 idem2 = -slot02 a := by
  rw [peirceInner_apply, jordan_idem0_idem2, jordan_zero_right, jordan_comm (slot02 a) idem2,
    jordan_idem2_slot02, jordan_smul_right, jordan_idem0_slot02]
  module
theorem peirceInner_slot02_idem1 (a : Octonion) : peirceInner (slot02 a) idem0 idem1 = 0 := by
  rw [peirceInner_apply, jordan_idem0_idem1, jordan_zero_right, jordan_comm (slot02 a) idem1,
    jordan_idem1_slot02, jordan_zero_right]
  module
theorem peirceInner_slot12_idem1 (a : Octonion) : peirceInner (slot12 a) idem1 idem1 = slot12 a := by
  rw [peirceInner_apply, jordan_idem1_idem1, jordan_comm (slot12 a) idem1, jordan_idem1_slot12,
    jordan_smul_right, jordan_idem1_slot12]
  module
theorem peirceInner_slot12_idem2 (a : Octonion) : peirceInner (slot12 a) idem1 idem2 = -slot12 a := by
  rw [peirceInner_apply, jordan_idem1_idem2, jordan_zero_right, jordan_comm (slot12 a) idem2,
    jordan_idem2_slot12, jordan_smul_right, jordan_idem1_slot12]
  module
theorem peirceInner_slot12_idem0 (a : Octonion) : peirceInner (slot12 a) idem1 idem0 = 0 := by
  rw [peirceInner_apply, jordan_idem1_idem0, jordan_zero_right, jordan_comm (slot12 a) idem0,
    jordan_idem0_slot12, jordan_zero_right]
  module

/-! ## Diagonal variation and the inner section -/

/-- The diagonal variation `D ↦ ((D e₀).o01, (D e₀).o02, (D e₁).o12)`. -/
def diagonalVariation : Module.End ℝ Albert →ₗ[ℝ] Octonion × Octonion × Octonion where
  toFun D := ((D idem0).o01, (D idem0).o02, (D idem1).o12)
  map_add' := by intro D E; rfl
  map_smul' := by intro r D; rfl

theorem diagonalVariation_apply (D : Module.End ℝ Albert) :
    diagonalVariation D = ((D idem0).o01, (D idem0).o02, (D idem1).o12) := rfl

/-- The inner section `(a, b, c) ↦ δ_{01,a} + δ_{02,b} + δ_{12,c}`. -/
def innerSection : (Octonion × Octonion × Octonion) →ₗ[ℝ] Module.End ℝ Albert where
  toFun v := peirceInner (slot01 v.1) idem0 + peirceInner (slot02 v.2.1) idem0 + peirceInner (slot12 v.2.2) idem1
  map_add' := by
    intro v w
    simp only [Prod.fst_add, Prod.snd_add, slot01_add, slot02_add, slot12_add, peirceInner_add_left]
    abel
  map_smul' := by
    intro r v
    simp only [Prod.smul_fst, Prod.smul_snd, slot01_smul, slot02_smul, slot12_smul,
      peirceInner_smul_left, RingHom.id_apply, smul_add]

theorem innerSection_apply (v : Octonion × Octonion × Octonion) :
    innerSection v =
      peirceInner (slot01 v.1) idem0 + peirceInner (slot02 v.2.1) idem0 + peirceInner (slot12 v.2.2) idem1 := rfl

theorem innerSection_mem (v : Octonion × Octonion × Octonion) : innerSection v ∈ jordanDerivations := by
  rw [innerSection_apply]
  exact add_mem (add_mem (peirceInner_mem _ _) (peirceInner_mem _ _)) (peirceInner_mem _ _)

theorem diagonalVariation_innerSection (v : Octonion × Octonion × Octonion) :
    diagonalVariation (innerSection v) = v := by
  obtain ⟨a, b, c⟩ := v
  rw [diagonalVariation_apply, innerSection_apply]
  simp only [LinearMap.add_apply, peirceInner_slot01_idem0, peirceInner_slot02_idem0,
    peirceInner_slot12_idem0, peirceInner_slot01_idem1, peirceInner_slot02_idem1,
    peirceInner_slot12_idem1, Albert.add_o01, Albert.add_o02, Albert.add_o12, Albert.zero_o01,
    Albert.zero_o02, Albert.zero_o12, neg_o12]
  simp [slot01, slot02, slot12]

/-! ## Idempotent rigidity

Adapted from `leibniz_idem0_eq_zero`, `leibniz_idem1_eq_zero`, `leibniz_idem2_eq_zero` of
`RealOrbitSlice/Native/DerivationDimension/Rigidity.lean` (earlier first-party work):
`D e_i = 2 e_i ∘ D e_i` and `e_i ∘ e_j = 0` force `D e_i = 0` from the three diagonal-variation
directions. -/

theorem oct_eq_zero_of_half {x : Octonion} (h : 0 = (2 : ℝ)⁻¹ • x) : x = 0 := by
  have h2 := congrArg (fun z : Octonion => (2 : ℝ) • z) h
  simp only [smul_zero, smul_smul] at h2
  norm_num at h2
  exact h2.symm

section Leibniz

variable {δ : Albert →ₗ[ℝ] Albert} (hδ : IsJordanDerivation δ)
include hδ

theorem leibniz_idem0_eq_zero (h01 : (δ idem0).o01 = 0) (h02 : (δ idem0).o02 = 0) :
    δ idem0 = 0 := by
  have h := hδ idem0 idem0
  rw [jordan_idem0_idem0, jordan_comm (δ idem0) idem0, jordan_idem0_left] at h
  have hd0 := congrArg Albert.d0 h
  have hd1 := congrArg Albert.d1 h
  have hd2 := congrArg Albert.d2 h
  have h12 := congrArg Albert.o12 h
  simp at hd0 hd1 hd2 h12
  apply Albert.extExplicit <;> simp [hd0, hd1, hd2, h12, h01, h02]

theorem leibniz_idem1_eq_zero (h0 : δ idem0 = 0) (h12 : (δ idem1).o12 = 0) :
    δ idem1 = 0 := by
  have h := hδ idem1 idem1
  rw [jordan_idem1_idem1, jordan_comm (δ idem1) idem1, jordan_idem1_left] at h
  have hd0 := congrArg Albert.d0 h
  have hd1 := congrArg Albert.d1 h
  have hd2 := congrArg Albert.d2 h
  have h02 := congrArg Albert.o02 h
  have k := hδ idem0 idem1
  rw [jordan_idem0_idem1, map_zero, h0, jordan_zero_left, zero_add, jordan_idem0_left] at k
  have h01 := congrArg Albert.o01 k
  simp at hd0 hd1 hd2 h02 h01
  have h01' := oct_eq_zero_of_half h01
  apply Albert.extExplicit <;> simp [hd0, hd1, hd2, h12, h01', h02]

theorem leibniz_idem2_eq_zero (h0 : δ idem0 = 0) (h1 : δ idem1 = 0) : δ idem2 = 0 := by
  have h := hδ idem2 idem2
  rw [jordan_idem2_idem2, jordan_comm (δ idem2) idem2, jordan_idem2_left] at h
  have hd0 := congrArg Albert.d0 h
  have hd1 := congrArg Albert.d1 h
  have hd2 := congrArg Albert.d2 h
  have h01 := congrArg Albert.o01 h
  have k := hδ idem0 idem2
  rw [jordan_idem0_idem2, map_zero, h0, jordan_zero_left, zero_add, jordan_idem0_left] at k
  have h02 := congrArg Albert.o02 k
  have l := hδ idem1 idem2
  rw [jordan_idem1_idem2, map_zero, h1, jordan_zero_left, zero_add, jordan_idem1_left] at l
  have h12 := congrArg Albert.o12 l
  simp at hd0 hd1 hd2 h01 h02 h12
  have h02' := oct_eq_zero_of_half h02
  have h12' := oct_eq_zero_of_half h12
  apply Albert.extExplicit <;> simp [hd0, hd1, hd2, h12', h01, h02']

end Leibniz

/-- A derivation fixes the ordered diagonal iff its diagonal variation vanishes. -/
theorem mem_diagonalFixer_iff_diagonalVariation {D : Module.End ℝ Albert} (hD : D ∈ jordanDerivations) :
    D ∈ diagonalFixer ↔ diagonalVariation D = 0 := by
  have hD' : IsJordanDerivation D := mem_jordanDerivations.mp hD
  constructor
  · intro h
    obtain ⟨_, h0, h1, _⟩ := mem_diagonalFixer.mp h
    rw [diagonalVariation_apply, h0, h1]
    rfl
  · intro h
    rw [diagonalVariation_apply] at h
    have h01 : (D idem0).o01 = 0 := congrArg Prod.fst h
    have h02 : (D idem0).o02 = 0 := congrArg (fun p => p.2.1) h
    have h12 : (D idem1).o12 = 0 := congrArg (fun p => p.2.2) h
    have e0 := leibniz_idem0_eq_zero hD' h01 h02
    have e1 := leibniz_idem1_eq_zero hD' e0 h12
    exact mem_diagonalFixer.mpr ⟨hD', e0, e1, leibniz_idem2_eq_zero hD' e0 e1⟩

theorem diagonalVariation_sub_innerSection_mem (D : jordanDerivations) :
    (D : Module.End ℝ Albert) - innerSection (diagonalVariation D) ∈ diagonalFixer := by
  have hmem : (D : Module.End ℝ Albert) - innerSection (diagonalVariation D) ∈ jordanDerivations :=
    sub_mem D.2 (innerSection_mem _)
  rw [mem_diagonalFixer_iff_diagonalVariation hmem, map_sub, diagonalVariation_innerSection, sub_self]

theorem innerSection_add_mem (v : Octonion × Octonion × Octonion) (F : diagonalFixer) :
    innerSection v + (F : Module.End ℝ Albert) ∈ jordanDerivations :=
  add_mem (innerSection_mem v) (diagonalFixer_le F.2)

theorem diagonalVariation_fixer (F : diagonalFixer) : diagonalVariation (F : Module.End ℝ Albert) = 0 :=
  (mem_diagonalFixer_iff_diagonalVariation (diagonalFixer_le F.2)).mp F.2

theorem coe_add_jordanDerivations (D E : jordanDerivations) :
    ((D + E : jordanDerivations) : Module.End ℝ Albert) = D + E := rfl

theorem coe_smul_jordanDerivations (r : ℝ) (D : jordanDerivations) :
    ((r • D : jordanDerivations) : Module.End ℝ Albert) = r • (D : Module.End ℝ Albert) := rfl

theorem coe_add_diagonalFixer (F G : diagonalFixer) :
    ((F + G : diagonalFixer) : Module.End ℝ Albert) = F + G := rfl

theorem coe_smul_diagonalFixer (r : ℝ) (F : diagonalFixer) :
    ((r • F : diagonalFixer) : Module.End ℝ Albert) = r • (F : Module.End ℝ Albert) := rfl

/-- The fixer component `D ↦ D - innerSection (diagonalVariation D)`. -/
def fixerPart (D : jordanDerivations) : diagonalFixer :=
  ⟨D - innerSection (diagonalVariation D), diagonalVariation_sub_innerSection_mem D⟩

theorem coe_fixerPart (D : jordanDerivations) :
    (fixerPart D : Module.End ℝ Albert) = D - innerSection (diagonalVariation D) := by
  rw [fixerPart]

/-- The reassembly `(v, F) ↦ innerSection v + F`. -/
def reassemble (p : (Octonion × Octonion × Octonion) × diagonalFixer) : jordanDerivations :=
  ⟨innerSection p.1 + p.2, innerSection_add_mem p.1 p.2⟩

theorem coe_reassemble (p : (Octonion × Octonion × Octonion) × diagonalFixer) :
    (reassemble p : Module.End ℝ Albert) = innerSection p.1 + p.2 := by
  rw [reassemble]

theorem fixerPart_add (D E : jordanDerivations) : fixerPart (D + E) = fixerPart D + fixerPart E := by
  apply Subtype.ext
  rw [coe_add_diagonalFixer, coe_fixerPart, coe_fixerPart, coe_fixerPart, coe_add_jordanDerivations,
    map_add, map_add]
  abel

theorem fixerPart_smul (r : ℝ) (D : jordanDerivations) : fixerPart (r • D) = r • fixerPart D := by
  apply Subtype.ext
  rw [coe_smul_diagonalFixer, coe_fixerPart, coe_fixerPart, coe_smul_jordanDerivations, map_smul,
    map_smul, smul_sub]

theorem reassemble_fixerPart (D : jordanDerivations) :
    reassemble (diagonalVariation D, fixerPart D) = D := by
  apply Subtype.ext
  rw [coe_reassemble, coe_fixerPart]
  abel

theorem diagonalVariation_reassemble (p : (Octonion × Octonion × Octonion) × diagonalFixer) :
    diagonalVariation (reassemble p : Module.End ℝ Albert) = p.1 := by
  rw [coe_reassemble, map_add, diagonalVariation_innerSection, diagonalVariation_fixer, add_zero]

theorem fixerPart_reassemble (p : (Octonion × Octonion × Octonion) × diagonalFixer) :
    fixerPart (reassemble p) = p.2 := by
  apply Subtype.ext
  rw [coe_fixerPart, diagonalVariation_reassemble, coe_reassemble]
  abel

/-- The real linear splitting of all native derivations into three octonion directions and the
ordered diagonal fixer. -/
def derivationDecomposition : jordanDerivations ≃ₗ[ℝ] (Octonion × Octonion × Octonion) × diagonalFixer :=
  { toFun D := (diagonalVariation D, fixerPart D)
    map_add' D E := by
      show (diagonalVariation ((D + E : jordanDerivations) : Module.End ℝ Albert), fixerPart (D + E)) =
        (diagonalVariation (D : Module.End ℝ Albert), fixerPart D) +
          (diagonalVariation (E : Module.End ℝ Albert), fixerPart E)
      rw [fixerPart_add, coe_add_jordanDerivations, map_add]
      exact (Prod.mk_add_mk _ _ _ _).symm
    map_smul' r D := by
      show (diagonalVariation ((r • D : jordanDerivations) : Module.End ℝ Albert), fixerPart (r • D)) =
        RingHom.id ℝ r • (diagonalVariation (D : Module.End ℝ Albert), fixerPart D)
      rw [fixerPart_smul, coe_smul_jordanDerivations, map_smul, RingHom.id_apply]
      exact (Prod.smul_mk _ _ _).symm
    invFun := reassemble
    left_inv := reassemble_fixerPart
    right_inv p := Prod.ext (diagonalVariation_reassemble p) (fixerPart_reassemble p) }

theorem derivationDecomposition_apply (D : jordanDerivations) :
    derivationDecomposition D = (diagonalVariation D, fixerPart D) := by
  unfold derivationDecomposition
  rw [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]

theorem derivationDecomposition_apply_fst (D : jordanDerivations) :
    (derivationDecomposition D).1 = diagonalVariation D := by
  rw [derivationDecomposition_apply]

theorem derivationDecomposition_apply_snd (D : jordanDerivations) :
    ((derivationDecomposition D).2 : Module.End ℝ Albert) = D - innerSection (diagonalVariation D) := by
  rw [derivationDecomposition_apply, coe_fixerPart]

theorem derivationDecomposition_symm_apply (v : Octonion × Octonion × Octonion) (F : diagonalFixer) :
    ((derivationDecomposition.symm (v, F) : jordanDerivations) : Module.End ℝ Albert) =
      innerSection v + F := by
  unfold derivationDecomposition
  rw [LinearEquiv.coe_symm_mk, coe_reassemble]

end CKM.NativeDerivationTriality

#print axioms CKM.NativeDerivationTriality.peirceInner_mem
#print axioms CKM.NativeDerivationTriality.peirceInner_slot01_idem0
#print axioms CKM.NativeDerivationTriality.peirceInner_slot01_idem1
#print axioms CKM.NativeDerivationTriality.peirceInner_slot01_idem2
#print axioms CKM.NativeDerivationTriality.peirceInner_slot02_idem0
#print axioms CKM.NativeDerivationTriality.peirceInner_slot02_idem2
#print axioms CKM.NativeDerivationTriality.peirceInner_slot02_idem1
#print axioms CKM.NativeDerivationTriality.peirceInner_slot12_idem1
#print axioms CKM.NativeDerivationTriality.peirceInner_slot12_idem2
#print axioms CKM.NativeDerivationTriality.peirceInner_slot12_idem0
#print axioms CKM.NativeDerivationTriality.diagonalVariation
#print axioms CKM.NativeDerivationTriality.innerSection
#print axioms CKM.NativeDerivationTriality.innerSection_mem
#print axioms CKM.NativeDerivationTriality.diagonalVariation_innerSection
#print axioms CKM.NativeDerivationTriality.mem_diagonalFixer_iff_diagonalVariation
#print axioms CKM.NativeDerivationTriality.derivationDecomposition
#print axioms CKM.NativeDerivationTriality.derivationDecomposition_apply_fst
#print axioms CKM.NativeDerivationTriality.derivationDecomposition_apply_snd
#print axioms CKM.NativeDerivationTriality.derivationDecomposition_symm_apply
