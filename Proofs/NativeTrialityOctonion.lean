module

public import NativeTrialityReuseOctonionLaws
public import Mathlib.Algebra.Lie.SkewAdjoint
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Trace

/-!
# Native octonion operators for the derivation/triality block

The actual native compact octonions `Glennie.Octonion` (two quaternions, doubling parameter `-1`) with
their native product `Glennie.octMul`, conjugation `Glennie.octConj` and positive pairing
`Glennie.octDot`. This file packages them as real-linear objects:

* `octDotForm` — the native pairing as a real bilinear form; `skewEnd` — its skew-adjoint Lie algebra
  (commutator bracket), the skew endomorphisms of the native eight-dimensional octonion space;
* `octConjLinear`, `leftMul u`, `rightMul u` — conjugation and left/right multiplication operators;
* `octBasis` — the real coordinate basis `1, i, j, k, ℓ, iℓ, jℓ, kℓ`; `imagUnit i = octBasis (i+1)`;

and states the octonion identities used later: symmetry and positivity of the pairing, norm
adjunction, skewness of `L_u`, `R_u` for imaginary `u`, the polarized alternative (Clifford) relations,
the linearized middle Moufang identity behind the seed triple, and `K L_u K = -R_u`.
-/

@[expose] public section

noncomputable section

namespace CKM.NativeDerivationTriality

open Glennie

-- The commutator Lie structure on endomorphisms, enabled locally as Mathlib itself does at this pin.
attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## Linear packaging -/

/-- The native positive pairing `octDot x y = Re (x * conj y)` as a real bilinear form. -/
def octDotForm : LinearMap.BilinForm ℝ Octonion :=
  LinearMap.mk₂ ℝ octDot
    (fun x y z => octDot_add_left x y z)
    (fun r x y => by rw [octDot_smul_left, smul_eq_mul])
    (fun x y z => by rw [octDot_comm, octDot_add_left, octDot_comm y, octDot_comm z])
    (fun r x y => by rw [octDot_comm, octDot_smul_left, octDot_comm, smul_eq_mul])

@[simp] theorem octDotForm_apply (x y : Octonion) : octDotForm x y = octDot x y := rfl

/-- The skew endomorphisms of the native octonion space, `octDot (T x) y = - octDot x (T y)`,
as a Lie subalgebra of `Module.End ℝ Octonion` with the commutator bracket. -/
abbrev skewEnd : LieSubalgebra ℝ (Module.End ℝ Octonion) := skewAdjointLieSubalgebra octDotForm

/-- Native octonion conjugation as a real-linear map. -/
def octConjLinear : Octonion →ₗ[ℝ] Octonion where
  toFun := octConj
  map_add' := octConj_add
  map_smul' := octConj_smul

/-- Left multiplication `L_u x = u * x` by a native octonion. -/
def leftMul (u : Octonion) : Module.End ℝ Octonion where
  toFun x := octMul u x
  map_add' x y := octMul_add_right u x y
  map_smul' r x := octMul_smul_right r u x

/-- Right multiplication `R_u x = x * u` by a native octonion. -/
def rightMul (u : Octonion) : Module.End ℝ Octonion where
  toFun x := octMul x u
  map_add' x y := octMul_add_left x y u
  map_smul' r x := octMul_smul_left r x u

@[simp] theorem octConjLinear_apply (x : Octonion) : octConjLinear x = octConj x := rfl
@[simp] theorem leftMul_apply (u x : Octonion) : leftMul u x = octMul u x := rfl
@[simp] theorem rightMul_apply (u x : Octonion) : rightMul u x = octMul x u := rfl

/-- The octonion with prescribed real coordinates `(q₁.re, q₁.i, q₁.j, q₁.k, q₂.re, q₂.i, q₂.j, q₂.k)`. -/
def octOfCoord (v : Fin 8 → ℝ) : Octonion :=
  (⟨v 0, v 1, v 2, v 3⟩, ⟨v 4, v 5, v 6, v 7⟩)

/-- The standard real coordinate basis of the native octonions; `octBasis 0 = 1`. -/
def octBasis (j : Fin 8) : Octonion := octOfCoord (Pi.single j 1)

/-- The seven standard imaginary units `octBasis 1, …, octBasis 7`. -/
def imagUnit (i : Fin 7) : Octonion := octBasis i.succ

/-! ## Helper facts (component expansion through the two quaternion halves) -/

namespace OctonionAux

/-- The `j`-th real coordinate of a native octonion, in the order of `octOfCoord`.
Adapted from `RealOrbitSlice/Native/DerivationDimension/Peirce.lean` (`octCoord`). -/
def octCoord (i : Fin 8) (x : Octonion) : ℝ :=
  ![x.1.re, x.1.imI, x.1.imJ, x.1.imK, x.2.re, x.2.imI, x.2.imJ, x.2.imK] i

/-- Pairing with a basis vector reads off a coordinate.
Adapted from `RealOrbitSlice/Native/DerivationDimension/Peirce.lean` (`octDot_octBasis_left`). -/
theorem octDot_octBasis_left (j : Fin 8) (x : Octonion) :
    octDot (octBasis j) x = octCoord j x := by
  rw [octDot_coordinates]
  fin_cases j <;> simp [octBasis, octOfCoord, octCoord]

theorem octCoord_octBasis (i j : Fin 8) : octCoord i (octBasis j) = if i = j then 1 else 0 := by
  fin_cases i <;> simp [octBasis, octOfCoord, octCoord, Pi.single_apply]

theorem octConj_of_re_zero {u : Octonion} (hu : octRe u = 0) : octConj u = -u := by
  obtain ⟨⟨a, b, c, d⟩, q⟩ := u
  simp only [octRe] at hu
  subst hu
  apply Prod.ext <;> apply Quaternion.ext <;> simp [octConj]

theorem octMul_neg_right (x y : Octonion) : octMul x (-y) = -octMul x y := by
  rw [← neg_one_smul ℝ y, octMul_smul_right, neg_one_smul]

/-- Polarized left alternative law: `u (v x) + v (u x) = (u v + v u) x`. -/
theorem octMul_left_polarized (u v x : Octonion) :
    octMul u (octMul v x) + octMul v (octMul u x) = octMul (octMul u v + octMul v u) x := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [octMul] <;> ring

/-- Polarized right alternative law: `(x v) u + (x u) v = x (v u + u v)`. -/
theorem octMul_right_polarized (u v x : Octonion) :
    octMul (octMul x v) u + octMul (octMul x u) v = octMul x (octMul v u + octMul u v) := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [octMul] <;> ring

/-- For imaginary `u, v`: `u v + v u = -2 ⟨u, v⟩`. -/
theorem octMul_anticomm_of_imag {u v : Octonion} (hu : octRe u = 0) (hv : octRe v = 0) :
    octMul u v + octMul v u = octScalar (-2 * octDot u v) := by
  obtain ⟨⟨a, b, c, d⟩, q⟩ := u
  obtain ⟨⟨a', b', c', d'⟩, q'⟩ := v
  simp only [octRe] at hu hv
  subst hu hv
  rw [octDot_coordinates]
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [octMul, octScalar] <;> ring

theorem octDot_imagUnit (i j : Fin 7) :
    octDot (imagUnit i) (imagUnit j) = if i = j then 1 else 0 := by
  rw [imagUnit, imagUnit, octDot_octBasis_left, octCoord_octBasis]
  simp only [Fin.succ_inj]

end OctonionAux

open OctonionAux

/-! ## Statements -/

theorem finrank_octonion : Module.finrank ℝ Octonion = 8 := by
  rw [Module.finrank_prod, Quaternion.finrank_eq_four]

theorem octDot_octBasis (i j : Fin 8) : octDot (octBasis i) (octBasis j) = if i = j then 1 else 0 := by
  rw [octDot_octBasis_left, octCoord_octBasis]

theorem octDot_self_pos {x : Octonion} (hx : x ≠ 0) : 0 < octDot x x := by
  rw [octDot_self]
  exact lt_of_le_of_ne (octNormSq_nonneg x) (fun h => hx ((octNormSq_eq_zero x).mp h.symm))

/-- Norm adjunction for left multiplication: `⟨x y, z⟩ = ⟨y, x̄ z⟩`. -/
theorem octDot_mul_left_adjoint (x y z : Octonion) :
    octDot (octMul x y) z = octDot y (octMul (octConj x) z) := by
  rw [octDot_coordinates, octDot_coordinates]
  simp [octMul, octConj]
  ring

/-- Norm adjunction for right multiplication: `⟨x y, z⟩ = ⟨x, z ȳ⟩`. -/
theorem octDot_mul_right_adjoint (x y z : Octonion) :
    octDot (octMul x y) z = octDot x (octMul z (octConj y)) := by
  rw [octDot_coordinates, octDot_coordinates]
  simp [octMul, octConj]
  ring

theorem octDot_conj_conj (x y : Octonion) : octDot (octConj x) (octConj y) = octDot x y := by
  rw [octDot_coordinates, octDot_coordinates]
  simp [octConj]

theorem leftMul_mem_skewEnd {u : Octonion} (hu : octRe u = 0) : leftMul u ∈ skewEnd := by
  show leftMul u ∈ octDotForm.skewAdjointSubmodule
  rw [LinearMap.mem_skewAdjointSubmodule]
  intro x y
  simp only [octDotForm_apply, leftMul_apply, Pi.neg_apply]
  rw [octDot_mul_left_adjoint, octConj_of_re_zero hu, ← neg_one_smul ℝ u, octMul_smul_left,
    neg_one_smul]

theorem rightMul_mem_skewEnd {u : Octonion} (hu : octRe u = 0) : rightMul u ∈ skewEnd := by
  show rightMul u ∈ octDotForm.skewAdjointSubmodule
  rw [LinearMap.mem_skewAdjointSubmodule]
  intro x y
  simp only [octDotForm_apply, rightMul_apply, Pi.neg_apply]
  rw [octDot_mul_right_adjoint, octConj_of_re_zero hu, octMul_neg_right]

theorem octRe_imagUnit (i : Fin 7) : octRe (imagUnit i) = 0 := by
  have h := octCoord_octBasis 0 i.succ
  rw [ite_eq_right_iff.mpr (fun h' => absurd h'.symm (Fin.succ_ne_zero i))] at h
  exact h

/-- Polarized left alternativity for the imaginary units: `L_i L_j + L_j L_i = -2 δ_ij`. -/
theorem leftMul_imagUnit_anticomm (i j : Fin 7) :
    leftMul (imagUnit i) * leftMul (imagUnit j) + leftMul (imagUnit j) * leftMul (imagUnit i) =
      (if i = j then (-2 : ℝ) else 0) • (1 : Module.End ℝ Octonion) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.add_apply, Module.End.mul_apply, leftMul_apply, LinearMap.smul_apply,
    Module.End.one_apply]
  rw [octMul_left_polarized, octMul_anticomm_of_imag (octRe_imagUnit i) (octRe_imagUnit j),
    octMul_scalar_left, octDot_imagUnit]
  split_ifs <;> simp

/-- Polarized right alternativity for the imaginary units: `R_i R_j + R_j R_i = -2 δ_ij`. -/
theorem rightMul_imagUnit_anticomm (i j : Fin 7) :
    rightMul (imagUnit i) * rightMul (imagUnit j) + rightMul (imagUnit j) * rightMul (imagUnit i) =
      (if i = j then (-2 : ℝ) else 0) • (1 : Module.End ℝ Octonion) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.add_apply, Module.End.mul_apply, rightMul_apply, LinearMap.smul_apply,
    Module.End.one_apply]
  rw [octMul_right_polarized, octMul_anticomm_of_imag (octRe_imagUnit j) (octRe_imagUnit i),
    octMul_scalar_right, octDot_imagUnit]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

/-- The linearized middle Moufang identity: `(u x) y + x (y u) = u (x y) + (x y) u`. -/
theorem seed_identity (u x y : Octonion) :
    octMul (octMul u x) y + octMul x (octMul y u) = octMul u (octMul x y) + octMul (octMul x y) u := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [octMul] <;> ring

/-- Conjugating left multiplication by an imaginary octonion: `K L_u K = -R_u`. -/
theorem conj_leftMul_conj {u : Octonion} (hu : octRe u = 0) :
    octConjLinear * leftMul u * octConjLinear = -rightMul u := by
  apply LinearMap.ext
  intro x
  simp only [Module.End.mul_apply, octConjLinear_apply, leftMul_apply, LinearMap.neg_apply,
    rightMul_apply]
  rw [octConj_mul, octConj_conj, octConj_of_re_zero hu, octMul_neg_right]

end CKM.NativeDerivationTriality

#print axioms CKM.NativeDerivationTriality.finrank_octonion
#print axioms CKM.NativeDerivationTriality.octDot_octBasis
#print axioms CKM.NativeDerivationTriality.octDot_self_pos
#print axioms CKM.NativeDerivationTriality.octDot_mul_left_adjoint
#print axioms CKM.NativeDerivationTriality.octDot_mul_right_adjoint
#print axioms CKM.NativeDerivationTriality.octDot_conj_conj
#print axioms CKM.NativeDerivationTriality.leftMul_mem_skewEnd
#print axioms CKM.NativeDerivationTriality.rightMul_mem_skewEnd
#print axioms CKM.NativeDerivationTriality.octRe_imagUnit
#print axioms CKM.NativeDerivationTriality.leftMul_imagUnit_anticomm
#print axioms CKM.NativeDerivationTriality.rightMul_imagUnit_anticomm
#print axioms CKM.NativeDerivationTriality.seed_identity
#print axioms CKM.NativeDerivationTriality.conj_leftMul_conj
