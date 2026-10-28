module

public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.FinCases

/-!
# Ring-generic shape of the accepted 39-point CKM configuration

Every formula here is over an arbitrary commutative ring `R`, takes the
scalar inputs as a small record `Consts R` (one third, the three cube-root
characters, the four rational phases, each split into real/imaginary parts),
and mirrors the native definitions `nativePoint`, `nativeFamilyPoint`,
`nativeOuterProductThird`, `Glennie.octMul` and `upperCoordinates` literally
(same branch structure, same index arithmetic, same coordinate order).

Instantiated at `R = ℝ` it equals the native point's coordinates
(PointStructure.lean); instantiated at an exact computable ring it computes
the point's literal table, and ring homs commute with it (`shape_map`).

First-party composition, no borrowed text.
-/

@[expose] public section

namespace FourSheets.PointShape

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Quaternion product in coordinates (re, imI, imJ, imK). -/
def qmul (x y : Fin 4 → R) : Fin 4 → R :=
  ![x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3,
    x 0 * y 1 + x 1 * y 0 + x 2 * y 3 - x 3 * y 2,
    x 0 * y 2 - x 1 * y 3 + x 2 * y 0 + x 3 * y 1,
    x 0 * y 3 + x 1 * y 2 - x 2 * y 1 + x 3 * y 0]

def qstar (x : Fin 4 → R) : Fin 4 → R := ![x 0, -x 1, -x 2, -x 3]

def lo (x : Fin 8 → R) : Fin 4 → R := ![x 0, x 1, x 2, x 3]
def hi (x : Fin 8 → R) : Fin 4 → R := ![x 4, x 5, x 6, x 7]
def join (p q : Fin 4 → R) : Fin 8 → R := ![p 0, p 1, p 2, p 3, q 0, q 1, q 2, q 3]

/-- Cayley–Dickson product, literally `Glennie.octMul`:
`(x₁y₁ − ȳ₂x₂, y₂x₁ + x₂ȳ₁)`. -/
def omul (x y : Fin 8 → R) : Fin 8 → R :=
  join (qmul (lo x) (lo y) - qmul (qstar (hi y)) (hi x))
    (qmul (hi y) (lo x) + qmul (hi x) (qstar (lo y)))

/-- `Glennie.octConj`: `(x̄₁, −x₂)`. -/
def oconj (x : Fin 8 → R) : Fin 8 → R := join (qstar (lo x)) (-(hi x))

def onormSq (x : Fin 8 → R) : R :=
  x 0 * x 0 + x 1 * x 1 + x 2 * x 2 + x 3 * x 3 +
    (x 4 * x 4 + x 5 * x 5 + x 6 * x 6 + x 7 * x 7)

/-- Upper coordinates of `nativeOuterProductThird x y`
= ⟨1/3, |x|²/3, |y|²/3, x̄/3, ȳ/3, x ȳ/3⟩, with `third` for 1/3. -/
def outerVec (third : R) (x y : Fin 8 → R) : Fin 27 → R :=
  let cx := oconj x
  let cy := oconj y
  let m := omul x cy
  ![third, third * onormSq x, third * onormSq y,
    third * cx 0, third * cx 1, third * cx 2, third * cx 3,
    third * cx 4, third * cx 5, third * cx 6, third * cx 7,
    third * cy 0, third * cy 1, third * cy 2, third * cy 3,
    third * cy 4, third * cy 5, third * cy 6, third * cy 7,
    third * m 0, third * m 1, third * m 2, third * m 3,
    third * m 4, third * m 5, third * m 6, third * m 7]

/-- Upper coordinates of `literalNativeCoordinatePoint t`. -/
def coordVec (t : Fin 3) : Fin 27 → R := fun k => if k.val = t.val then 1 else 0

/-- Coordinates of `complexOctonion z` from `(z.re, z.im)`. -/
def zvec (re im : R) : Fin 8 → R := ![re, im, 0, 0, 0, 0, 0, 0]

/-- Coordinates of `nativeOctonionBasis b`. -/
def basisVec (b : Fin 8) : Fin 8 → R := fun j => if j = b then 1 else 0

/-- Scalar inputs: 1/3, characters ω^r (re, im) and the four phases (re, im). -/
structure Consts (R : Type*) where
  third : R
  cre : ZMod 3 → R
  cim : ZMod 3 → R
  pre : Fin 4 → R
  pim : Fin 4 → R

def Consts.map (f : R →+* S) (c : Consts R) : Consts S :=
  ⟨f c.third, fun r => f (c.cre r), fun r => f (c.cim r),
    fun p => f (c.pre p), fun p => f (c.pim p)⟩

/-- Coordinates of `complexOctonion (character r)`. -/
def charVec (c : Consts R) (r : ZMod 3) : Fin 8 → R := zvec (c.cre r) (c.cim r)

/-- Coordinates of `complexOctonion (exactPhases p * character r)`
(`Complex.mul_re`, `Complex.mul_im` order). -/
def phasedVec (c : Consts R) (p : Fin 4) (r : ZMod 3) : Fin 8 → R :=
  zvec (c.pre p * c.cre r - c.pim p * c.cim r) (c.pre p * c.cim r + c.pim p * c.cre r)

/-- Mirror of `nativeFamilyPoint q s t` (same branches). -/
def familyShape (c : Consts R) (q : Fin 4) (s t : ZMod 3) : Fin 27 → R :=
  if q = 0 then outerVec c.third (charVec c t) (charVec c (s - t))
  else if q = 1 then
    outerVec c.third (omul (charVec c t) (basisVec 2)) (omul (charVec c (s + t)) (basisVec 4))
  else if q = 2 then
    outerVec c.third (omul (phasedVec c 0 t) (basisVec 4))
      (omul (phasedVec c 1 (s + t)) (basisVec 6))
  else
    outerVec c.third (omul (phasedVec c 2 t) (basisVec 6))
      (omul (phasedVec c 3 (s + t)) (basisVec 2))

/-- Mirror of `nativePoint i` (same index arithmetic). -/
def shape (c : Consts R) (i : Fin 39) : Fin 27 → R :=
  if hi : i.val < 3 then coordVec ⟨i.val, hi⟩
  else
    let q : Fin 4 := ⟨(i.val - 3) / 9, by have hi39 := i.isLt; omega⟩
    let s : ZMod 3 := (((i.val - 3) % 9) / 3 : ℕ)
    let t : ZMod 3 := ((i.val - 3) % 3 : ℕ)
    familyShape c q s t

/-! ## Ring homs commute with the shape -/

theorem map_qmul (f : R →+* S) (x y : Fin 4 → R) :
    (fun i => f (qmul x y i)) = qmul (fun i => f (x i)) (fun i => f (y i)) := by
  funext i; fin_cases i <;> simp [qmul]

theorem map_qstar (f : R →+* S) (x : Fin 4 → R) :
    (fun i => f (qstar x i)) = qstar (fun i => f (x i)) := by
  funext i; fin_cases i <;> simp [qstar]

theorem map_lo (f : R →+* S) (x : Fin 8 → R) :
    (fun i => f (lo x i)) = lo (fun i => f (x i)) := by
  funext i; fin_cases i <;> simp [lo]

theorem map_hi (f : R →+* S) (x : Fin 8 → R) :
    (fun i => f (hi x i)) = hi (fun i => f (x i)) := by
  funext i; fin_cases i <;> simp [hi]

theorem map_join (f : R →+* S) (p q : Fin 4 → R) :
    (fun i => f (join p q i)) = join (fun i => f (p i)) (fun i => f (q i)) := by
  funext i; fin_cases i <;> simp [join]

theorem map_omul (f : R →+* S) (x y : Fin 8 → R) :
    (fun i => f (omul x y i)) = omul (fun i => f (x i)) (fun i => f (y i)) := by
  have hs (a b : Fin 4 → R) : (fun i => f ((a - b) i)) = (fun i => f (a i)) - (fun i => f (b i)) := by
    funext i; simp
  have ha (a b : Fin 4 → R) : (fun i => f ((a + b) i)) = (fun i => f (a i)) + (fun i => f (b i)) := by
    funext i; simp
  simp only [omul, map_join, hs, ha, map_qmul, map_qstar, map_lo, map_hi]

theorem map_oconj (f : R →+* S) (x : Fin 8 → R) :
    (fun i => f (oconj x i)) = oconj (fun i => f (x i)) := by
  have hn (a : Fin 4 → R) : (fun i => f ((-a) i)) = -(fun i => f (a i)) := by
    funext i; simp
  simp only [oconj, map_join, hn, map_qstar, map_lo, map_hi]

theorem map_onormSq (f : R →+* S) (x : Fin 8 → R) :
    f (onormSq x) = onormSq (fun i => f (x i)) := by
  simp [onormSq]

theorem map_outerVec (f : R →+* S) (third : R) (x y : Fin 8 → R) :
    (fun k => f (outerVec third x y k)) =
      outerVec (f third) (fun i => f (x i)) (fun i => f (y i)) := by
  have hm : (fun i => f (omul x (oconj y) i)) =
      omul (fun i => f (x i)) (oconj (fun i => f (y i))) := by
    rw [map_omul, map_oconj]
  have hcx := map_oconj f x
  have hcy := map_oconj f y
  funext k
  have e1 := congrFun hm
  have e2 := congrFun hcx
  have e3 := congrFun hcy
  fin_cases k <;> simp [outerVec, map_onormSq, ← e1, ← e2, ← e3]

theorem map_coordVec (f : R →+* S) (t : Fin 3) :
    (fun k => f (coordVec t k)) = coordVec t := by
  funext k; unfold coordVec; split_ifs <;> simp

theorem map_zvec (f : R →+* S) (a b : R) :
    (fun i => f (zvec a b i)) = zvec (f a) (f b) := by
  funext i; fin_cases i <;> simp [zvec]

theorem map_basisVec (f : R →+* S) (b : Fin 8) :
    (fun i => f (basisVec b i)) = basisVec b := by
  funext i; unfold basisVec; split_ifs <;> simp

theorem map_charVec (f : R →+* S) (c : Consts R) (r : ZMod 3) :
    (fun i => f (charVec c r i)) = charVec (c.map f) r := by
  simp only [charVec, map_zvec, Consts.map]

theorem map_phasedVec (f : R →+* S) (c : Consts R) (p : Fin 4) (r : ZMod 3) :
    (fun i => f (phasedVec c p r i)) = phasedVec (c.map f) p r := by
  simp only [phasedVec, map_zvec, Consts.map, map_sub, map_add, map_mul]

theorem map_omul_basis (f : R →+* S) (x : Fin 8 → R) (b : Fin 8) :
    (fun i => f (omul x (basisVec b) i)) = omul (fun i => f (x i)) (basisVec b) := by
  rw [map_omul, map_basisVec]

theorem map_familyShape (f : R →+* S) (c : Consts R) (q : Fin 4) (s t : ZMod 3) :
    (fun k => f (familyShape c q s t k)) = familyShape (c.map f) q s t := by
  unfold familyShape
  split_ifs <;>
    simp only [map_outerVec, map_omul_basis, map_charVec, map_phasedVec] <;> rfl

/-- Ring homs commute with the whole 39-point shape. -/
theorem shape_map (f : R →+* S) (c : Consts R) (i : Fin 39) (k : Fin 27) :
    f (shape c i k) = shape (c.map f) i k := by
  unfold shape
  split_ifs
  · exact congrFun (map_coordVec f _) k
  · exact congrFun (map_familyShape f c _ _ _) k

end FourSheets.PointShape

#print axioms FourSheets.PointShape.shape_map
