module

public import GSAutChart
public import NativeTracePreservation
public import A3Interfaces
public import NativeTrialityMain

@[expose] public section

/-!
# Native coordinates: the endomorphism algebra, the product and the derivations

The existing native carrier `Glennie.Albert` has no topology. As in the pinned compact library
(`Glennie.Compact.Flows`), analysis is done in the existing 27 upper coordinates
`NativePolynomial.upperCoordinates` (the literal coordinates of the 1053-variable packing):

* `Coord = Fin 27 → ℝ`, `CEnd = Coord →L[ℝ] Coord` (operator norm; a finite-dimensional real
  Banach algebra);
* `coordEnd : Module.End ℝ Albert ≃ₐ[ℝ] CEnd`, `g ↦ upperCoordinates ∘ g ∘ fromUpperCoordinates`;
* `prodC`: the original equations' coordinate product `coordinateProduct (1/2)`, which is the native
  Jordan product in coordinates (`prodC_eq_native`, from the accepted
  `coordinateProduct_real_eq_native_coordinates`);
* `derC = derOf prodC`: the actual native Jordan derivations in coordinates, equal to the image of
  the triality block's `jordanDerivations` (`derC_eq_map`), of dimension 52.
-/

noncomputable section

namespace CKM.NativeGroupSlice

open Glennie NativePolynomial CKM.NativeDerivationTriality

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The 27 upper coordinates of the native algebra. -/
abbrev Coord := Fin 27 → ℝ

/-- Continuous linear endomorphisms of the coordinate space (operator norm). -/
abbrev CEnd := Coord →L[ℝ] Coord

/-- The conjugation equivalence underlying `coordEnd`, applied to a vector. -/
private theorem coord_conjEquiv_apply (g : Module.End ℝ Albert) (v : Coord) :
    (upperCoordinateEquiv.conj.trans LinearMap.toContinuousLinearMap) g v =
      upperCoordinates (g (fromUpperCoordinates v)) :=
  rfl

/-- Native endomorphisms read in the 27 upper coordinates. -/
def coordEnd : Module.End ℝ Albert ≃ₐ[ℝ] CEnd :=
  AlgEquiv.ofLinearEquiv (upperCoordinateEquiv.conj.trans LinearMap.toContinuousLinearMap)
    (by
      ext v
      rw [coord_conjEquiv_apply]
      simp)
    (by
      intro f g
      ext v
      rw [mul_apply_eq_comp, coord_conjEquiv_apply, coord_conjEquiv_apply,
        coord_conjEquiv_apply, fromUpperCoordinates_upperCoordinates, Module.End.mul_apply])

theorem coordEnd_apply (g : Module.End ℝ Albert) (v : Coord) :
    coordEnd g v = upperCoordinates (g (fromUpperCoordinates v)) :=
  rfl

theorem coordEnd_symm_apply (A : CEnd) (x : Albert) :
    coordEnd.symm A x = fromUpperCoordinates (A (upperCoordinates x)) := by
  conv_rhs => rw [← coordEnd.apply_symm_apply A]
  rw [coordEnd_apply, fromUpperCoordinates_upperCoordinates,
    fromUpperCoordinates_upperCoordinates]

/-- The original equations' coordinate product `coordinateProduct (1/2)`, as a continuous
bilinear map. -/
def prodC : Coord →L[ℝ] Coord →L[ℝ] Coord :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp (CoordinateMaps.coordinateProduct (1 / 2 : ℝ)))

theorem prodC_apply (a b : Coord) : prodC a b = CoordinateMaps.coordinateProduct (1 / 2 : ℝ) a b :=
  rfl

/-- `prodC` is the native Jordan product in coordinates. -/
theorem prodC_eq_native (a b : Coord) :
    prodC a b = upperCoordinates (jordan (fromUpperCoordinates a) (fromUpperCoordinates b)) := by
  rw [prodC_apply]
  exact CoordinateMaps.coordinateProduct_real_eq_native_coordinates (1 / 2 : ℝ) (by norm_num) a b

theorem prodC_upperCoordinates (x y : Albert) :
    prodC (upperCoordinates x) (upperCoordinates y) = upperCoordinates (jordan x y) := by
  rw [prodC_eq_native, fromUpperCoordinates_upperCoordinates, fromUpperCoordinates_upperCoordinates]

/-- The actual native Jordan derivations, in coordinates. -/
abbrev derC : Submodule ℝ CEnd := derOf prodC

theorem mem_derC_iff (A : CEnd) : A ∈ derC ↔ coordEnd.symm A ∈ jordanDerivations := by
  obtain ⟨D, rfl⟩ := coordEnd.surjective A
  rw [AlgEquiv.symm_apply_apply, mem_jordanDerivations, mem_derOf]
  constructor
  · intro h x y
    have hxy := h (upperCoordinates x) (upperCoordinates y)
    rw [prodC_upperCoordinates, coordEnd_apply, coordEnd_apply, coordEnd_apply,
      fromUpperCoordinates_upperCoordinates, fromUpperCoordinates_upperCoordinates,
      fromUpperCoordinates_upperCoordinates, prodC_upperCoordinates, prodC_upperCoordinates,
      ← upperCoordinates_add] at hxy
    simpa only [fromUpperCoordinates_upperCoordinates] using
      congrArg fromUpperCoordinates hxy
  · intro h a b
    rw [prodC_eq_native, coordEnd_apply, coordEnd_apply, coordEnd_apply,
      fromUpperCoordinates_upperCoordinates, h, prodC_eq_native, prodC_eq_native,
      fromUpperCoordinates_upperCoordinates, fromUpperCoordinates_upperCoordinates,
      upperCoordinates_add]

theorem derC_eq_map : derC = jordanDerivations.toSubmodule.map coordEnd.toLinearMap := by
  ext A
  rw [Submodule.mem_map]
  constructor
  · intro h
    exact ⟨coordEnd.symm A, (mem_derC_iff A).1 h, by
      rw [AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply]⟩
  · rintro ⟨D, hD, rfl⟩
    rw [mem_derC_iff, AlgEquiv.toLinearMap_apply, AlgEquiv.symm_apply_apply]
    exact hD

/-- The identity chart has dimension 52. -/
theorem finrank_derC : Module.finrank ℝ derC = 52 := by
  rw [derC_eq_map, ← (Submodule.equivMapOfInjective coordEnd.toLinearMap coordEnd.injective
    jordanDerivations.toSubmodule).finrank_eq]
  exact finrank_jordanDerivations

end CKM.NativeGroupSlice

#print axioms CKM.NativeGroupSlice.coordEnd
#print axioms CKM.NativeGroupSlice.coordEnd_apply
#print axioms CKM.NativeGroupSlice.coordEnd_symm_apply
#print axioms CKM.NativeGroupSlice.prodC_apply
#print axioms CKM.NativeGroupSlice.prodC_eq_native
#print axioms CKM.NativeGroupSlice.prodC_upperCoordinates
#print axioms CKM.NativeGroupSlice.mem_derC_iff
#print axioms CKM.NativeGroupSlice.derC_eq_map
#print axioms CKM.NativeGroupSlice.finrank_derC
