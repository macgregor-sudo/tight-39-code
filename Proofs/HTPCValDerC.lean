module

public import HTPCValDer

@[expose] public section

/-!
# Kernel-evaluable twin of the Kronecker derivation integer (first-party)

`kronC l` uses only list folds, `Int.add`, `Int.mul` and `Nat.pow` (GMP-accelerated in the
kernel), sparse matrix rows and the original `productTable`; `kronC_eq` proves `kronC l = kron l`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace Option2.NativeStress.HTPhaseComplete

open scoped BigOperators
open QuarticCertificate.RowBridge

def lsum (l : List ℤ) : ℤ := l.foldr Int.add 0

theorem lsum_eq (l : List ℤ) : lsum l = l.sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [lsum, List.foldr_cons, List.sum_cons] at ih ⊢; rw [← ih]; rfl

theorem lsum_finRange (f : Fin 27 → ℤ) : lsum ((List.finRange 27).map f) = ∑ k, f k := by
  rw [lsum_eq, Fin.sum_univ_def]

/-- Sparse row action `(D v)_k`. -/
def mvC (l : List IEnt) (v : Fin 27 → ℤ) (k : Fin 27) : ℤ :=
  lsum (l.map fun e => if e.1 = k then Int.mul e.2.2 (v e.2.1) else 0)

def tbC (k : Fin 27) (y z : Fin 27 → ℤ) : ℤ :=
  lsum ((productTable k).map fun e => Int.mul e.2.2 (Int.add (Int.mul (y e.1) (z e.2.1)) (Int.mul (z e.1) (y e.2.1))))

def defectC (l : List IEnt) (y z : Fin 27 → ℤ) (k : Fin 27) : ℤ :=
  Int.sub (Int.sub (lsum (l.map fun e => if e.1 = k then Int.mul e.2.2 (tbC e.2.1 y z) else 0))
    (tbC k (mvC l y) z)) (tbC k y (mvC l z))

def ySC (m : Fin 27) : ℤ := Int.ofNat (Nat.pow 2 (32 * m.val))
def zSC (n : Fin 27) : ℤ := Int.ofNat (Nat.pow 2 (32 * (27 * n.val)))
def wSC (k : Fin 27) : ℤ := Int.ofNat (Nat.pow 2 (32 * (729 * k.val)))

def kronC (l : List IEnt) : ℤ := lsum ((List.finRange 27).map fun k => Int.mul (wSC k) (defectC l ySC zSC k))

theorem sparse_sum (l : List IEnt) (k : Fin 27) (f : Fin 27 → ℤ) :
    ∑ c, (iAt l k c : ℤ) * f c = (l.map fun e => if e.1 = k then e.2.2 * f e.2.1 else 0).sum := by
  induction l with
  | nil => simp [iAt]
  | cons e l ih =>
    have : ∀ c, iAt (e :: l) k c = (if e.1 = k ∧ e.2.1 = c then e.2.2 else 0) + iAt l k c := by
      intro c; simp [iAt]
    simp only [this, add_mul, Finset.sum_add_distrib, List.map_cons, List.sum_cons]
    rw [ih]
    congr 1
    by_cases h : e.1 = k
    · simp [h, ite_and, Finset.sum_ite_eq]
    · simp [h]

theorem mvC_eq (l : List IEnt) (v : Fin 27 → ℤ) : mvC l v = mv (iMat (R := ℤ) l) v := by
  funext k
  simp only [mvC, lsum_eq, mv, iMat, Int.cast_id, sparse_sum]
  congr 1

theorem tbC_eq (k : Fin 27) (y z : Fin 27 → ℤ) : tbC k y z = tb k y z := by
  simp only [tbC, lsum_eq, tb]; rfl

theorem defectC_eq (l : List IEnt) (y z : Fin 27 → ℤ) (k : Fin 27) :
    defectC l y z k = defect (iMat (R := ℤ) l) y z k := by
  simp only [defectC, defect, lsum_eq, tbC_eq, mvC_eq, iMat, Int.cast_id, sparse_sum]
  rfl

theorem ySC_eq (m : Fin 27) : ySC m = yS m := by
  simp only [ySC, yS, kX, Nat.pow_eq, Int.ofNat_eq_coe, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
theorem zSC_eq (n : Fin 27) : zSC n = zS n := by
  simp only [zSC, zS, kX, Nat.pow_eq, Int.ofNat_eq_coe, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
theorem wSC_eq (k : Fin 27) : wSC k = wS k := by
  simp only [wSC, wS, kX, Nat.pow_eq, Int.ofNat_eq_coe, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]

theorem kronC_eq (l : List IEnt) : kronC l = kron l := by
  have hy : ySC = yS := funext ySC_eq
  have hz : zSC = zS := funext zSC_eq
  simp only [kronC, kron, lsum_finRange, defectC_eq, hy, hz, wSC_eq]
  rfl

/-- **Derivation from the kernel-evaluated integer.** -/
theorem isDer_of_kronC {R : Type*} [CommRing R] (l : List IEnt) (hb : derBound l < kX) (h : kronC l = 0) :
    IsDer (iMat (R := R) l) := isDer_of_kron l hb (by rw [← kronC_eq]; exact h)

/-! ## Faster kernel form: the two matrix–vector products are materialised once as list arguments -/

def vecOf (d : List ℤ) (a : Fin 27) : ℤ := d.getD a.val 0

theorem vecOf_map (f : Fin 27 → ℤ) : vecOf ((List.finRange 27).map f) = f := by
  funext a; simp [vecOf, List.getD_eq_getElem?_getD, List.getElem?_map]

def defV (l : List IEnt) (dy dz : List ℤ) (k : Fin 27) : ℤ :=
  Int.sub (Int.sub (lsum (l.map fun e => if e.1 = k then Int.mul e.2.2 (tbC e.2.1 ySC zSC) else 0))
    (tbC k (vecOf dy) zSC)) (tbC k ySC (vecOf dz))

def kronCore (l : List IEnt) (dy dz : List ℤ) : ℤ :=
  lsum ((List.finRange 27).map fun k => Int.mul (wSC k) (defV l dy dz k))

def kronF (l : List IEnt) : ℤ :=
  kronCore l ((List.finRange 27).map (mvC l ySC)) ((List.finRange 27).map (mvC l zSC))

theorem kronF_eq (l : List IEnt) : kronF l = kronC l := by
  simp only [kronF, kronCore, defV, vecOf_map, kronC, defectC]

/-- **Derivation from the (fast) kernel-evaluated integer.** -/
theorem isDer_of_kronF {R : Type*} [CommRing R] (l : List IEnt) (hb : derBound l < kX) (h : kronF l = 0) :
    IsDer (iMat (R := R) l) := isDer_of_kronC l hb (by rw [← kronF_eq]; exact h)

end Option2.NativeStress.HTPhaseComplete
