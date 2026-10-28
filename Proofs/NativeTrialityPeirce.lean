module

public import NativeTrialityOctonion
public import NativeTrialityReuseInnerDerivation

/-!
# Native diagonal idempotents, Peirce slots and the derivation Lie algebras

The diagonal idempotents `idem0, idem1, idem2` and the three off-diagonal octonion slots
`slot01, slot02, slot12` of the actual native Albert algebra `Glennie.Albert`, in its native field
order `(d0, d1, d2, o01, o02, o12)`, with their native Jordan products (from the native coordinate
formulas `Glennie.jordan_d0 … jordan_o12`).

* `jordanDerivations` — all real-linear Leibniz maps for the native product `Glennie.jordan`, a Lie
  subalgebra of `Module.End ℝ Albert` (commutator bracket);
* `diagonalFixer` — the derivations killing each of the three ordered diagonal idempotents.
-/

@[expose] public section

noncomputable section

namespace CKM.NativeDerivationTriality

open Glennie Reuse

/-! ## Idempotents and slots -/

/-- The native diagonal idempotents. -/
def idem0 : Albert := ⟨1, 0, 0, 0, 0, 0⟩
def idem1 : Albert := ⟨0, 1, 0, 0, 0, 0⟩
def idem2 : Albert := ⟨0, 0, 1, 0, 0, 0⟩

/-- The three off-diagonal octonion slots (upper entries `o01`, `o02`, `o12`). -/
def slot01 (a : Octonion) : Albert := ⟨0, 0, 0, a, 0, 0⟩
def slot02 (a : Octonion) : Albert := ⟨0, 0, 0, 0, a, 0⟩
def slot12 (a : Octonion) : Albert := ⟨0, 0, 0, 0, 0, a⟩

/-- The diagonal part `diag d₀ d₁ d₂`. -/
def diagonal (d₀ d₁ d₂ : ℝ) : Albert := ⟨d₀, d₁, d₂, 0, 0, 0⟩

/-! ## Octonion zero laws (local helpers)

Adapted from `RealOrbitSlice/Native/DerivationDimension/Peirce.lean` (package
real-orbit-slice-2026-10-24, first-party source); made private and only
locally `simp` here, to avoid clashing with any other file of this block. -/

private theorem octMul_zero_left (x : Octonion) : octMul 0 x = 0 := by
  simp [octMul]

private theorem octMul_zero_right (x : Octonion) : octMul x 0 = 0 := by
  simp [octMul]

private theorem octConj_zero : octConj 0 = 0 := by
  simp [octConj]

private theorem octDot_zero_left (x : Octonion) : octDot 0 x = 0 := by
  simp [octDot, octRe, octMul]

private theorem octDot_zero_right (x : Octonion) : octDot x 0 = 0 := by
  simp [octDot, octRe, octMul, octConj]

private theorem octNormSq_zero : octNormSq 0 = 0 := (octNormSq_eq_zero 0).mpr rfl

attribute [local simp] octMul_zero_left octMul_zero_right octConj_zero octDot_zero_left
  octDot_zero_right octNormSq_zero

theorem albert_decomposition (x : Albert) :
    x = x.d0 • idem0 + x.d1 • idem1 + x.d2 • idem2 + slot01 x.o01 + slot02 x.o02 + slot12 x.o12 := by
  -- Adapted from `RealOrbitSlice/Native/DerivationDimension/Peirce.lean` (`albert_decomposition`).
  apply Albert.extExplicit <;> simp [idem0, idem1, idem2, slot01, slot02, slot12]

theorem idem0_add_idem1_add_idem2 : idem0 + idem1 + idem2 = (1 : Albert) := by
  apply Albert.extExplicit <;> simp [idem0, idem1, idem2]

/-! ## Native products with idempotents and slots -/

theorem jordan_idem0_left (x : Albert) :
    jordan idem0 x = ⟨x.d0, 0, 0, (1/2 : ℝ) • x.o01, (1/2 : ℝ) • x.o02, 0⟩ := by
  -- Adapted from `RealOrbitSlice/Native/DerivationDimension/Peirce.lean` (`jordan_idem0_left`).
  apply Albert.extExplicit
  · rw [jordan_d0]; simp [idem0]
  · rw [jordan_d1]; simp [idem0]
  · rw [jordan_d2]; simp [idem0]
  · rw [jordan_o01]; simp [idem0]
  · rw [jordan_o02]; simp [idem0]
  · rw [jordan_o12]; simp [idem0]

theorem jordan_idem1_left (x : Albert) :
    jordan idem1 x = ⟨0, x.d1, 0, (1/2 : ℝ) • x.o01, 0, (1/2 : ℝ) • x.o12⟩ := by
  -- Adapted from `RealOrbitSlice/Native/DerivationDimension/Peirce.lean` (`jordan_idem1_left`).
  apply Albert.extExplicit
  · rw [jordan_d0]; simp [idem1]
  · rw [jordan_d1]; simp [idem1]
  · rw [jordan_d2]; simp [idem1]
  · rw [jordan_o01]; simp [idem1]
  · rw [jordan_o02]; simp [idem1]
  · rw [jordan_o12]; simp [idem1]

theorem jordan_idem2_left (x : Albert) :
    jordan idem2 x = ⟨0, 0, x.d2, 0, (1/2 : ℝ) • x.o02, (1/2 : ℝ) • x.o12⟩ := by
  -- Adapted from `RealOrbitSlice/Native/DerivationDimension/Peirce.lean` (`jordan_idem2_left`).
  apply Albert.extExplicit
  · rw [jordan_d0]; simp [idem2]
  · rw [jordan_d1]; simp [idem2]
  · rw [jordan_d2]; simp [idem2]
  · rw [jordan_o01]; simp [idem2]
  · rw [jordan_o02]; simp [idem2]
  · rw [jordan_o12]; simp [idem2]

theorem jordan_slot01_slot01 (a b : Octonion) :
    jordan (slot01 a) (slot01 b) = diagonal (octDot a b) (octDot a b) 0 := by
  -- Specialisation of `jordan_slot01_left` in `RealOrbitSlice/Native/DerivationDimension/Peirce.lean`.
  apply Albert.extExplicit
  · rw [jordan_d0]; simp [slot01, diagonal]
  · rw [jordan_d1]; simp [slot01, diagonal]
  · rw [jordan_d2]; simp [slot01, diagonal]
  · rw [jordan_o01]; simp [slot01, diagonal]
  · rw [jordan_o02]; simp [slot01, diagonal]
  · rw [jordan_o12]; simp [slot01, diagonal]

theorem jordan_slot02_slot02 (a b : Octonion) :
    jordan (slot02 a) (slot02 b) = diagonal (octDot a b) 0 (octDot a b) := by
  -- Specialisation of `jordan_slot02_left` in `RealOrbitSlice/Native/DerivationDimension/Peirce.lean`.
  apply Albert.extExplicit
  · rw [jordan_d0]; simp [slot02, diagonal]
  · rw [jordan_d1]; simp [slot02, diagonal]
  · rw [jordan_d2]; simp [slot02, diagonal]
  · rw [jordan_o01]; simp [slot02, diagonal]
  · rw [jordan_o02]; simp [slot02, diagonal]
  · rw [jordan_o12]; simp [slot02, diagonal]

theorem jordan_slot12_slot12 (a b : Octonion) :
    jordan (slot12 a) (slot12 b) = diagonal 0 (octDot a b) (octDot a b) := by
  -- Specialisation of `jordan_slot12_left` in `RealOrbitSlice/Native/DerivationDimension/Peirce.lean`.
  apply Albert.extExplicit
  · rw [jordan_d0]; simp [slot12, diagonal]
  · rw [jordan_d1]; simp [slot12, diagonal]
  · rw [jordan_d2]; simp [slot12, diagonal]
  · rw [jordan_o01]; simp [slot12, diagonal]
  · rw [jordan_o02]; simp [slot12, diagonal]
  · rw [jordan_o12]; simp [slot12, diagonal]

/-- `E₀₁ ∘ E₁₂ ⊆ E₀₂`: `slot01 a ∘ slot12 b = slot02 (½ a b)`. -/
theorem jordan_slot01_slot12 (a b : Octonion) :
    jordan (slot01 a) (slot12 b) = slot02 ((1/2 : ℝ) • octMul a b) := by
  -- Specialisation of `jordan_slot01_left` in `RealOrbitSlice/Native/DerivationDimension/Peirce.lean`.
  apply Albert.extExplicit
  · rw [jordan_d0]; simp [slot01, slot12, slot02]
  · rw [jordan_d1]; simp [slot01, slot12, slot02]
  · rw [jordan_d2]; simp [slot01, slot12, slot02]
  · rw [jordan_o01]; simp [slot01, slot12, slot02]
  · rw [jordan_o02]; simp [slot01, slot12, slot02]
  · rw [jordan_o12]; simp [slot01, slot12, slot02]

/-- `E₀₂ ∘ E₁₂ ⊆ E₀₁`: `slot02 a ∘ slot12 b = slot01 (½ a b̄)`. -/
theorem jordan_slot02_slot12 (a b : Octonion) :
    jordan (slot02 a) (slot12 b) = slot01 ((1/2 : ℝ) • octMul a (octConj b)) := by
  -- Specialisation of `jordan_slot02_left` in `RealOrbitSlice/Native/DerivationDimension/Peirce.lean`.
  apply Albert.extExplicit
  · rw [jordan_d0]; simp [slot02, slot12, slot01]
  · rw [jordan_d1]; simp [slot02, slot12, slot01]
  · rw [jordan_d2]; simp [slot02, slot12, slot01]
  · rw [jordan_o01]; simp [slot02, slot12, slot01]
  · rw [jordan_o02]; simp [slot02, slot12, slot01]
  · rw [jordan_o12]; simp [slot02, slot12, slot01]

/-- `E₀₁ ∘ E₀₂ ⊆ E₁₂`: `slot01 a ∘ slot02 b = slot12 (½ ā b)`. -/
theorem jordan_slot01_slot02 (a b : Octonion) :
    jordan (slot01 a) (slot02 b) = slot12 ((1/2 : ℝ) • octMul (octConj a) b) := by
  -- Specialisation of `jordan_slot01_left` in `RealOrbitSlice/Native/DerivationDimension/Peirce.lean`.
  apply Albert.extExplicit
  · rw [jordan_d0]; simp [slot01, slot02, slot12]
  · rw [jordan_d1]; simp [slot01, slot02, slot12]
  · rw [jordan_d2]; simp [slot01, slot02, slot12]
  · rw [jordan_o01]; simp [slot01, slot02, slot12]
  · rw [jordan_o02]; simp [slot01, slot02, slot12]
  · rw [jordan_o12]; simp [slot01, slot02, slot12]

/-! ## The derivation Lie algebras -/

/-- The real Jordan derivations of the native product, as a submodule of endomorphisms. -/
def derivationSubmodule : Submodule ℝ (Module.End ℝ Albert) where
  carrier := {D | IsJordanDerivation D}
  zero_mem' := by
    intro x y
    simp only [LinearMap.zero_apply, jordan_zero_left, jordan_zero_right, add_zero]
  add_mem' := by
    intro D E hD hE x y
    have hD' : IsJordanDerivation D := hD
    have hE' : IsJordanDerivation E := hE
    simp only [LinearMap.add_apply, hD' x y, hE' x y, jordan_add_left, jordan_add_right]
    abel
  smul_mem' := by
    intro r D hD x y
    have hD' : IsJordanDerivation D := hD
    simp only [LinearMap.smul_apply, hD' x y, jordan_smul_left, jordan_smul_right, smul_add]

/-- A derivation kills the three ordered diagonal idempotents. -/
def FixesDiagonal (D : Module.End ℝ Albert) : Prop := D idem0 = 0 ∧ D idem1 = 0 ∧ D idem2 = 0

/-- The ordered diagonal-fixing derivations, as a submodule of endomorphisms. -/
def diagonalFixerSubmodule : Submodule ℝ (Module.End ℝ Albert) where
  carrier := {D | IsJordanDerivation D ∧ FixesDiagonal D}
  zero_mem' := ⟨derivationSubmodule.zero_mem, rfl, rfl, rfl⟩
  add_mem' := by
    rintro D E ⟨hD, hD0, hD1, hD2⟩ ⟨hE, hE0, hE1, hE2⟩
    exact ⟨derivationSubmodule.add_mem hD hE, by simp [hD0, hE0], by simp [hD1, hE1], by simp [hD2, hE2]⟩
  smul_mem' := by
    rintro r D ⟨hD, hD0, hD1, hD2⟩
    exact ⟨derivationSubmodule.smul_mem r hD, by simp [hD0], by simp [hD1], by simp [hD2]⟩

/-- Commutators of derivations are derivations. -/
theorem commutator_mem_derivationSubmodule {D E : Module.End ℝ Albert} (hD : D ∈ derivationSubmodule)
    (hE : E ∈ derivationSubmodule) : D * E - E * D ∈ derivationSubmodule := by
  have hD' : IsJordanDerivation D := hD
  have hE' : IsJordanDerivation E := hE
  show IsJordanDerivation (D * E - E * D)
  intro x y
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hD' x y, hE' x y, map_add, hD' (E x) y,
    hD' x (E y), hE' (D x) y, hE' x (D y), jordan_sub_left, jordan_sub_right]
  abel

theorem commutator_mem_diagonalFixerSubmodule {D E : Module.End ℝ Albert}
    (hD : D ∈ diagonalFixerSubmodule) (hE : E ∈ diagonalFixerSubmodule) :
    D * E - E * D ∈ diagonalFixerSubmodule := by
  obtain ⟨hD, hD0, hD1, hD2⟩ := hD
  obtain ⟨hE, hE0, hE1, hE2⟩ := hE
  refine ⟨commutator_mem_derivationSubmodule hD hE, ?_, ?_, ?_⟩ <;>
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hD0, hD1, hD2, hE0, hE1, hE2, map_zero,
      sub_self]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- All real Jordan derivations of the native Albert algebra, with the commutator bracket. -/
def jordanDerivations : LieSubalgebra ℝ (Module.End ℝ Albert) :=
  { derivationSubmodule with lie_mem' := fun hD hE => commutator_mem_derivationSubmodule hD hE }

/-- The ordered diagonal-fixing derivations, with the commutator bracket. -/
def diagonalFixer : LieSubalgebra ℝ (Module.End ℝ Albert) :=
  { diagonalFixerSubmodule with lie_mem' := fun hD hE => commutator_mem_diagonalFixerSubmodule hD hE }

theorem mem_jordanDerivations {D : Module.End ℝ Albert} :
    D ∈ jordanDerivations ↔ IsJordanDerivation D := Iff.rfl

theorem mem_diagonalFixer {D : Module.End ℝ Albert} :
    D ∈ diagonalFixer ↔ IsJordanDerivation D ∧ FixesDiagonal D := Iff.rfl

theorem diagonalFixer_le : diagonalFixer ≤ jordanDerivations := fun _ hD => hD.1

end CKM.NativeDerivationTriality

#print axioms CKM.NativeDerivationTriality.albert_decomposition
#print axioms CKM.NativeDerivationTriality.idem0_add_idem1_add_idem2
#print axioms CKM.NativeDerivationTriality.jordan_idem0_left
#print axioms CKM.NativeDerivationTriality.jordan_idem1_left
#print axioms CKM.NativeDerivationTriality.jordan_idem2_left
#print axioms CKM.NativeDerivationTriality.jordan_slot01_slot01
#print axioms CKM.NativeDerivationTriality.jordan_slot02_slot02
#print axioms CKM.NativeDerivationTriality.jordan_slot12_slot12
#print axioms CKM.NativeDerivationTriality.jordan_slot01_slot12
#print axioms CKM.NativeDerivationTriality.jordan_slot02_slot12
#print axioms CKM.NativeDerivationTriality.jordan_slot01_slot02
#print axioms CKM.NativeDerivationTriality.commutator_mem_derivationSubmodule
#print axioms CKM.NativeDerivationTriality.commutator_mem_diagonalFixerSubmodule
#print axioms CKM.NativeDerivationTriality.jordanDerivations
#print axioms CKM.NativeDerivationTriality.diagonalFixer
#print axioms CKM.NativeDerivationTriality.mem_jordanDerivations
#print axioms CKM.NativeDerivationTriality.mem_diagonalFixer
#print axioms CKM.NativeDerivationTriality.diagonalFixer_le
