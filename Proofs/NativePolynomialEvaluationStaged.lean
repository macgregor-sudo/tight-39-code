/-
Staged actual-native polynomial evaluation module. Imports the one emitted
NativeIncludedQuartetReadouts base; no native declaration is recopied here.
The attributed law extraction and first-party polynomial body below are exact,
with only their module/import commands removed. No second Glennie.Native or
SectorModel object is imported. THIRD_PARTY_NOTICES.md#native-albert-code records source
permission, authorship, retained notices and the real-only application limit.
-/
module

public import NativeIncludedQuartetReadouts
public import Mathlib.Tactic.Module
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

/-
Attributed extraction of exact native bilinearity, unit and linear-map packaging.
Repository: https://github.com/macgregor-sudo/compact-albert-recognition
Commit: 40d3b344180d9ddb78aaa2876873377c1e631515.
Original files: Glennie/Native/AlgebraLaws.lean, octDot_add_left,
octDot_smul_left, jordan_add_left/right, jordan_smul_left/right,
jordan_unit_left/right; Glennie/Native/CubicIdentity.lean,
jordanLinear, traceLinear and their application lemmas.
SPDX: Apache-2.0; original LICENSE and complete THIRD-PARTY-NOTICES.md
are retained in LICENSES/Native-Albert-Apache-2.0.txt and LICENSES/Native-Albert-THIRD-PARTY-NOTICES.md. No individual file author or
copyright header appears in these units. Pinned README credits AI-generated
development under Robert MacGregor's direction; its NOTICE names him as
maintainer. No holder or copyright year is inferred.
Modifications: declaration bodies copied unchanged; imports reduced to their
actual Native and Module dependencies, and surrounding file/section/options
omitted. No cubic identity, norm, alternativity or new carrier is included.
Canonical ledger: THIRD_PARTY_NOTICES.md#native-albert-code.
Thanks to the compact-albert-recognition contributors and maintainer, and to
the Lean and mathlib contributors, for this reusable native algebra.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/


noncomputable section
namespace Glennie

theorem octDot_add_left (x y z : Octonion) :
    octDot (x+y) z = octDot x z+octDot y z := by
  simp [octDot_coordinates]
  ring

theorem octDot_smul_left (r : ℝ) (x y : Octonion) :
    octDot (r • x) y = r*octDot x y := by
  simp [octDot_coordinates, smul_eq_mul]
  ring

theorem jordan_add_left (x y z : Albert) : jordan (x+y) z = jordan x z + jordan y z := by
  apply Albert.ext
  all_goals simp only [Albert.add_d0, Albert.add_d1, Albert.add_d2,
    Albert.add_o01, Albert.add_o02, Albert.add_o12,
    jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
    octDot_add_left, octConj_add, octMul_add_left, octMul_add_right]
  case d0 => ring
  case d1 => ring
  case d2 => ring
  all_goals module

theorem jordan_add_right (x y z : Albert) : jordan x (y+z) = jordan x y + jordan x z := by
  rw [jordan_comm, jordan_add_left, jordan_comm y x, jordan_comm z x]

theorem jordan_smul_left (r : ℝ) (x y : Albert) :
    jordan (r • x) y = r • jordan x y := by
  apply Albert.ext
  all_goals simp only [Albert.smul_d0, Albert.smul_d1, Albert.smul_d2,
    Albert.smul_o01, Albert.smul_o02, Albert.smul_o12,
    jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
    octDot_smul_left, octConj_smul, octMul_smul_left, octMul_smul_right]
  case d0 => ring
  case d1 => ring
  case d2 => ring
  all_goals module

theorem jordan_smul_right (r : ℝ) (x y : Albert) :
    jordan x (r • y) = r • jordan x y := by
  rw [jordan_comm, jordan_smul_left, jordan_comm]

@[simp] theorem jordan_unit_left (x : Albert) : jordan 1 x = x := by
  apply Albert.ext
  all_goals norm_num [jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02,
    jordan_o12, unit, octDot_coordinates, octMul, octConj, Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, smul_eq_mul,
    Prod.mk_zero_zero, smul_smul]

@[simp] theorem jordan_unit_right (x : Albert) : jordan x 1 = x := by
  rw [jordan_comm, jordan_unit_left]

def jordanLinear : Albert →ₗ[ℝ] Albert →ₗ[ℝ] Albert where
  toFun x :=
    { toFun := jordan x
      map_add' := fun y z => jordan_add_right x y z
      map_smul' := fun r y => jordan_smul_right r x y }
  map_add' x y := LinearMap.ext fun z => jordan_add_left x y z
  map_smul' r x := LinearMap.ext fun y => jordan_smul_left r x y

def traceLinear : Albert →ₗ[ℝ] ℝ where
  toFun := trace
  map_add' := trace_add
  map_smul' := trace_smul

@[simp] theorem jordanLinear_apply (x y : Albert) : jordanLinear x y = jordan x y := rfl
@[simp] theorem traceLinear_apply (x : Albert) : traceLinear x = trace x := rfl

end Glennie
/-
First-party finite-coordinate and polynomial adapters. The actual native
carrier and product are imported; neither is redefined by transport.
Imported native source: compact-albert-recognition,
https://github.com/macgregor-sudo/compact-albert-recognition,
commit 40d3b344180d9ddb78aaa2876873377c1e631515, Glennie/Native.lean.
The exact bilinear-law extraction and its adaptation/provenance are recorded
in the attributed extraction above (formerly NativeJordanBilinearLaws.lean) and THIRD_PARTY_NOTICES.md#native-albert-code.
Apache-2.0 notices are retained in LICENSES/Native-Albert-Apache-2.0.txt and LICENSES/Native-Albert-THIRD-PARTY-NOTICES.md.
Mathlib imports are at 065356127b1dc0016f66b7283ce0ce2c4055aa55.
No upstream proof body is copied into this adapter. Thank you to the
compact-albert-recognition, Lean and mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/


/-!
# Polynomial evaluation against the actual native Jordan product

Coordinates are the three real diagonals followed by the upper octonions
(01,02,12), each in (1,i,j,k,ell,iell,n,kell) order, n=j ell. The cyclic
chart is different: (Y01,Y02,Y12)=(x3,star(x2),x1). No cyclic/Fano transport
is asserted or silently inserted below.

The finite polynomial tensor formula is coefficient-parametric, so a later
integer-numerator/half realization can reuse it unchanged. The actual real
structure constants here come from the imported native basis products.
Evaluation-to-native multiplication is proved, not assumed. Real constants
alone provide no reduction map to a finite field. Rational/integral table
realization, literal F/G row families and generated-ideal equality remain
separate application obligations.
-/

noncomputable section

namespace NativePolynomial

open scoped BigOperators
open MvPolynomial

/-- Literal frozen upper-coordinate order of the existing native carrier. -/
def upperCoordinates (x : Glennie.Albert) : Fin 27 → ℝ :=
  ![x.d0, x.d1, x.d2,
    x.o01.1.re, x.o01.1.imI, x.o01.1.imJ, x.o01.1.imK,
    x.o01.2.re, x.o01.2.imI, x.o01.2.imJ, x.o01.2.imK,
    x.o02.1.re, x.o02.1.imI, x.o02.1.imJ, x.o02.1.imK,
    x.o02.2.re, x.o02.2.imI, x.o02.2.imJ, x.o02.2.imK,
    x.o12.1.re, x.o12.1.imI, x.o12.1.imJ, x.o12.1.imK,
    x.o12.2.re, x.o12.2.imI, x.o12.2.imJ, x.o12.2.imK]

/-- Reconstruct exactly the existing Albert and quaternion records. -/
def fromUpperCoordinates (v : Fin 27 → ℝ) : Glennie.Albert :=
  ⟨v 0, v 1, v 2,
    (⟨v 3, v 4, v 5, v 6⟩, ⟨v 7, v 8, v 9, v 10⟩),
    (⟨v 11, v 12, v 13, v 14⟩, ⟨v 15, v 16, v 17, v 18⟩),
    (⟨v 19, v 20, v 21, v 22⟩, ⟨v 23, v 24, v 25, v 26⟩)⟩

@[simp] theorem fromUpperCoordinates_upperCoordinates (x : Glennie.Albert) :
    fromUpperCoordinates (upperCoordinates x) = x := by
  apply Glennie.Albert.extExplicit
  · rfl
  · rfl
  · rfl
  all_goals apply Prod.ext <;> apply Quaternion.ext <;> rfl

@[simp] theorem upperCoordinates_fromUpperCoordinates (v : Fin 27 → ℝ) :
    upperCoordinates (fromUpperCoordinates v) = v := by
  funext i
  fin_cases i <;> rfl

theorem upperCoordinates_add (x y : Glennie.Albert) :
    upperCoordinates (x + y) = upperCoordinates x + upperCoordinates y := by
  funext i
  fin_cases i <;> simp [upperCoordinates]

theorem upperCoordinates_smul (r : ℝ) (x : Glennie.Albert) :
    upperCoordinates (r • x) = r • upperCoordinates x := by
  funext i
  fin_cases i <;> simp [upperCoordinates]

/-- A coordinate view, with no multiplication defined by transport. -/
def upperCoordinateEquiv : Glennie.Albert ≃ₗ[ℝ] (Fin 27 → ℝ) where
  toFun := upperCoordinates
  invFun := fromUpperCoordinates
  left_inv := fromUpperCoordinates_upperCoordinates
  right_inv := upperCoordinates_fromUpperCoordinates
  map_add' := upperCoordinates_add
  map_smul' := upperCoordinates_smul

/-- Actual coordinate basis element in the existing native algebra. -/
def nativeCoordinateBasis (i : Fin 27) : Glennie.Albert :=
  fromUpperCoordinates (fun j => if i = j then 1 else 0)

theorem fromUpperCoordinates_eq_sum (v : Fin 27 → ℝ) :
    fromUpperCoordinates v = ∑ i, v i • nativeCoordinateBasis i := by
  change upperCoordinateEquiv.symm.toLinearMap v = _
  exact LinearMap.pi_apply_eq_sum_univ upperCoordinateEquiv.symm.toLinearMap v

/-- The constants are defined from the actual native products, not input data. -/
def nativeStructureConstant (i j k : Fin 27) : ℝ :=
  upperCoordinates (Glennie.jordan (nativeCoordinateBasis i) (nativeCoordinateBasis j)) k

theorem jordan_fromUpperCoordinates (x y : Fin 27 → ℝ) :
    Glennie.jordan (fromUpperCoordinates x) (fromUpperCoordinates y) =
      ∑ i, ∑ j, (x i * y j) •
        Glennie.jordan (nativeCoordinateBasis i) (nativeCoordinateBasis j) := by
  change Glennie.jordanLinear (fromUpperCoordinates x) (fromUpperCoordinates y) = _
  rw [fromUpperCoordinates_eq_sum x, fromUpperCoordinates_eq_sum y]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.smul_sum, smul_smul, Glennie.jordanLinear_apply]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem upperCoordinates_jordan (x y : Fin 27 → ℝ) (k : Fin 27) :
    upperCoordinates (Glennie.jordan (fromUpperCoordinates x) (fromUpperCoordinates y)) k =
      ∑ i, ∑ j, x i * y j * nativeStructureConstant i j k := by
  change upperCoordinateEquiv
    (Glennie.jordan (fromUpperCoordinates x) (fromUpperCoordinates y)) k = _
  rw [jordan_fromUpperCoordinates]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

section PolynomialTensor

variable {σ R S : Type*} [CommSemiring R] [CommSemiring S]

/-- The single finite polynomial tensor formula shared by scalar stages. -/
def tensorPolynomial (c : Fin 27 → Fin 27 → Fin 27 → R)
    (x y : Fin 27 → MvPolynomial σ R) (k : Fin 27) : MvPolynomial σ R :=
  ∑ i, ∑ j, x i * y j * C (c i j k)

/-- Actual coefficient specialization commutes with the same finite formula. -/
theorem map_tensorPolynomial (f : R →+* S)
    (c : Fin 27 → Fin 27 → Fin 27 → R)
    (x y : Fin 27 → MvPolynomial σ R) (k : Fin 27) :
    MvPolynomial.map f (tensorPolynomial c x y k) =
      tensorPolynomial (fun i j k => f (c i j k))
        (fun i => MvPolynomial.map f (x i)) (fun j => MvPolynomial.map f (y j)) k := by
  simp [tensorPolynomial]

/-- Evaluation is a finite coefficient computation, with no semantic premise. -/
theorem eval₂_tensorPolynomial (f : R →+* S) (a : σ → S)
    (c : Fin 27 → Fin 27 → Fin 27 → R)
    (x y : Fin 27 → MvPolynomial σ R) (k : Fin 27) :
    MvPolynomial.eval₂ f a (tensorPolynomial c x y k) =
      ∑ i, ∑ j, MvPolynomial.eval₂ f a (x i) * MvPolynomial.eval₂ f a (y j) * f (c i j k) := by
  simp [tensorPolynomial, eval₂_mul]

end PolynomialTensor

variable {σ : Type*}

/-- Evaluate coordinate polynomials and recover the original native element. -/
def evaluateNative (a : σ → ℝ) (x : Fin 27 → MvPolynomial σ ℝ) : Glennie.Albert :=
  fromUpperCoordinates (fun k => MvPolynomial.eval₂ (RingHom.id ℝ) a (x k))

/-- The actual real polynomial product decodes to the original native Jordan
product at every evaluation. No correspondence or multiplication law is assumed. -/
theorem evaluateNative_tensorPolynomial (a : σ → ℝ)
    (x y : Fin 27 → MvPolynomial σ ℝ) :
    evaluateNative a (tensorPolynomial nativeStructureConstant x y) =
      Glennie.jordan (evaluateNative a x) (evaluateNative a y) := by
  have hCoordinates :
      (fun k => MvPolynomial.eval₂ (RingHom.id ℝ) a
        (tensorPolynomial nativeStructureConstant x y k)) =
      upperCoordinates (Glennie.jordan (evaluateNative a x) (evaluateNative a y)) := by
    funext k
    rw [eval₂_tensorPolynomial]
    simpa only [evaluateNative, RingHom.id_apply] using
      (upperCoordinates_jordan
        (fun i => MvPolynomial.eval₂ (RingHom.id ℝ) a (x i))
        (fun j => MvPolynomial.eval₂ (RingHom.id ℝ) a (y j)) k).symm
  change fromUpperCoordinates _ = _
  rw [hCoordinates, fromUpperCoordinates_upperCoordinates]

/-- The original trace uses the three diagonal coordinates. -/
def tracePolynomial (x : Fin 27 → MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  x 0 + x 1 + x 2

theorem eval₂_tracePolynomial (a : σ → ℝ) (x : Fin 27 → MvPolynomial σ ℝ) :
    MvPolynomial.eval₂ (RingHom.id ℝ) a (tracePolynomial x) =
      Glennie.trace (evaluateNative a x) := by
  simp [tracePolynomial, evaluateNative, fromUpperCoordinates, Glennie.trace]

end NativePolynomial


#check @Glennie.jordanLinear
#check @Glennie.jordan_unit_left
#check @NativePolynomial.upperCoordinates
#check @NativePolynomial.fromUpperCoordinates
#check @NativePolynomial.fromUpperCoordinates_upperCoordinates
#check @NativePolynomial.upperCoordinates_fromUpperCoordinates
#check @NativePolynomial.upperCoordinateEquiv
#check @NativePolynomial.fromUpperCoordinates_eq_sum
#check @NativePolynomial.nativeStructureConstant
#check @NativePolynomial.jordan_fromUpperCoordinates
#check @NativePolynomial.upperCoordinates_jordan
#check @NativePolynomial.tensorPolynomial
#check @NativePolynomial.map_tensorPolynomial
#check @NativePolynomial.eval₂_tensorPolynomial
#check @NativePolynomial.evaluateNative_tensorPolynomial
#check @NativePolynomial.eval₂_tracePolynomial

#print axioms Glennie.jordanLinear
#print axioms Glennie.jordan_unit_left
#print axioms NativePolynomial.fromUpperCoordinates_upperCoordinates
#print axioms NativePolynomial.upperCoordinates_fromUpperCoordinates
#print axioms NativePolynomial.upperCoordinateEquiv
#print axioms NativePolynomial.fromUpperCoordinates_eq_sum
#print axioms NativePolynomial.jordan_fromUpperCoordinates
#print axioms NativePolynomial.upperCoordinates_jordan
#print axioms NativePolynomial.map_tensorPolynomial
#print axioms NativePolynomial.eval₂_tensorPolynomial
#print axioms NativePolynomial.evaluateNative_tensorPolynomial
#print axioms NativePolynomial.eval₂_tracePolynomial
