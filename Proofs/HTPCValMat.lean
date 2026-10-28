module

public import HTPCValGen
public import DirKTransfer

@[expose] public section

/-!
# Complex derivation extensions `A_j`, the anchor operators `N_j = A_j − K_j`, and their support
(first-party)

* `aMat j = ½ · (2 A_j)` with `2 A_j = aZ j ∈ ℤ[i]` read from the certificate's derivation extensions
  exactly as `kMat j = ½ · kZ j` (`kMat_eq_kZ`) is read from its partial generators.
* `dirDer y = ∑_j y_j A_j` is a trace-skew, unit-killing, trace-free derivation over every ring
  (`dirDer_props`), from the 24 integer generator checks `gen_ok_*`.
* `nZ j = aZ j − kZ j = 2 N_j`: kernel checks `nCheck j` give the support statement `nZ_support`
  (`N_j[c,n] ≠ 0 → c, n ∈ J_{s(j)}`) and `nZ_unit` (`N_j e = 0`), with `J_s` = diagonal plus the three
  planes of window `s` (`jMem`).
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace Option2.NativeStress.HTPhaseComplete

open scoped BigOperators

/-! ## Closure of the four operator properties under linear combinations -/

section Closure
variable {R : Type*} [CommRing R]

def matLin (a b : R) (D E : Fin 27 → Fin 27 → R) : Fin 27 → Fin 27 → R := fun k c => a * D k c + b * E k c

theorem mv_matLin (a b : R) (D E : Fin 27 → Fin 27 → R) (y : Fin 27 → R) :
    mv (matLin a b D E) y = a • mv D y + b • mv E y := by
  funext k; simp only [mv, matLin, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro n _; ring

theorem isDer_matLin (a b : R) {D E : Fin 27 → Fin 27 → R} (hD : IsDer D) (hE : IsDer E) :
    IsDer (matLin a b D E) := by
  intro k y z
  rw [mv_matLin, mv_matLin, tb_add_left, tb_smul_left, tb_smul_left, tb_comm k y (a • mv D z + b • mv E z),
    tb_add_left, tb_smul_left, tb_smul_left, tb_comm k (mv D z) y, tb_comm k (mv E z) y]
  have h1 := hD k y z; have h2 := hE k y z
  simp only [matLin, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  rw [h1, h2]; ring

theorem isSkew_matLin (a b : R) {D E : Fin 27 → Fin 27 → R} (hD : IsSkew D) (hE : IsSkew E) :
    IsSkew (matLin a b D E) := by
  intro m n; simp only [matLin]; linear_combination a * hD m n + b * hE m n

theorem killsUnit_matLin (a b : R) {D E : Fin 27 → Fin 27 → R} (hD : KillsUnit D) (hE : KillsUnit E) :
    KillsUnit (matLin a b D E) := by
  intro m; simp only [matLin]; linear_combination a * hD m + b * hE m

theorem traceFree_matLin (a b : R) {D E : Fin 27 → Fin 27 → R} (hD : TraceFree D) (hE : TraceFree E) :
    TraceFree (matLin a b D E) := by
  intro n; simp only [matLin]; linear_combination a * hD n + b * hE n

/-- All four properties at once. -/
def GoodOp (D : Fin 27 → Fin 27 → R) : Prop := IsDer D ∧ IsSkew D ∧ KillsUnit D ∧ TraceFree D

theorem goodOp_matLin (a b : R) {D E : Fin 27 → Fin 27 → R} (hD : GoodOp D) (hE : GoodOp E) :
    GoodOp (matLin a b D E) :=
  ⟨isDer_matLin a b hD.1 hE.1, isSkew_matLin a b hD.2.1 hE.2.1, killsUnit_matLin a b hD.2.2.1 hE.2.2.1,
    traceFree_matLin a b hD.2.2.2 hE.2.2.2⟩

theorem goodOp_zero : GoodOp (fun _ _ => (0 : R)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k y z
    have : mv (fun _ _ => (0 : R)) = fun _ => 0 := by funext v k; simp [mv]
    simp only [this, zero_mul, Finset.sum_const_zero]
    have h0 : (fun _ : Fin 27 => (0 : R)) = 0 := rfl
    rw [tb_zero_left, tb_comm k y 0, tb_zero_left]; ring
  · intro m n; ring
  · intro m; ring
  · intro n; ring

theorem goodOp_sum (s : Finset (Fin 24)) (y : Fin 24 → R) (A : Fin 24 → Fin 27 → Fin 27 → R)
    (hA : ∀ j, GoodOp (A j)) : GoodOp (fun k c => ∑ j ∈ s, y j * A j k c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (goodOp_zero (R := R))
  | insert a s ha ih =>
    have e : (fun k c => ∑ j ∈ insert a s, y j * A j k c) = matLin (y a) 1 (A a) (fun k c => ∑ j ∈ s, y j * A j k c) := by
      funext k c; simp [matLin, Finset.sum_insert ha]
    rw [e]; exact goodOp_matLin _ _ (hA a) ih

end Closure

/-! ## The complex derivation extensions -/

def aPairOf (j : Fin 24) : Option (ℕ × ℕ × ℕ × List IEnt × List IEnt) :=
  aPairs.find? (fun pr => pr.2.1 == j.val || pr.2.2.1 == j.val)

/-- `2 A_j` in the Gaussian integers (same convention as `kZ`). -/
def aZ (j : Fin 24) (k c : Fin 27) : GaussianInt :=
  match aPairOf j with
  | none => 0
  | some pr =>
    if pr.2.1 = j.val then ⟨iAt pr.2.2.2.1 k c, -iAt pr.2.2.2.2 k c⟩
    else ⟨-iAt pr.2.2.2.1 k c, -iAt pr.2.2.2.2 k c⟩

def aMat (j : Fin 24) (k c : Fin 27) : Q12 := kHalf * gToQ12 (aZ j k c)

theorem aPairOf_mem {j : Fin 24} {pr : ℕ × ℕ × ℕ × List IEnt × List IEnt} (h : aPairOf j = some pr) :
    pr ∈ aPairs := List.mem_of_find?_eq_some h

/-- Every `A_j` is a good operator over any ring receiving `Q12`. -/
theorem aMat_good {R : Type*} [CommRing R] (ι : Q12 →+* R) (j : Fin 24) :
    GoodOp (fun k c => ι (aMat j k c)) := by
  unfold aMat aZ
  cases h : aPairOf j with
  | none =>
    simp only [map_zero, mul_zero]; exact goodOp_zero
  | some pr =>
    obtain ⟨h1, h2⟩ := aPairs_ok pr (aPairOf_mem h)
    have g1 := gen_props (R := R) _ h1
    have g2 := gen_props (R := R) _ h2
    dsimp only
    split_ifs with hj
    · have e : (fun k c => ι (kHalf * gToQ12 ⟨iAt pr.2.2.2.1 k c, -iAt pr.2.2.2.2 k c⟩)) =
          matLin (ι kHalf) (-(ι kHalf * ι Q12.I)) (iMat pr.2.2.2.1) (iMat pr.2.2.2.2) := by
        funext k c; simp only [matLin, iMat, gToQ12_apply, map_mul, map_add, map_intCast]; push_cast; ring
      rw [e]; exact goodOp_matLin _ _ g1 g2
    · have e : (fun k c => ι (kHalf * gToQ12 ⟨-iAt pr.2.2.2.1 k c, -iAt pr.2.2.2.2 k c⟩)) =
          matLin (-ι kHalf) (-(ι kHalf * ι Q12.I)) (iMat pr.2.2.2.1) (iMat pr.2.2.2.2) := by
        funext k c; simp only [matLin, iMat, gToQ12_apply, map_mul, map_add, map_intCast]; push_cast; ring
      rw [e]; exact goodOp_matLin _ _ g1 g2

/-- The direction derivation `∑_j y_j A_j`. -/
def dirDer {R : Type*} [CommRing R] (ι : Q12 →+* R) (y : Fin 24 → R) : Fin 27 → Fin 27 → R :=
  fun k c => ∑ j, y j * ι (aMat j k c)

theorem dirDer_props {R : Type*} [CommRing R] (ι : Q12 →+* R) (y : Fin 24 → R) : GoodOp (dirDer ι y) :=
  goodOp_sum Finset.univ y _ (aMat_good ι)

/-! ## The anchor operators and their support -/

def nZ (j : Fin 24) (k c : Fin 27) : GaussianInt := aZ j k c - kZ j k c

/-- Window of plane `p` (coordinates `3+2p, 4+2p`): W0 {0,4,8}, W1 {1,6,11}, W2 {2,7,9}, W3 {3,5,10}. -/
def winOf (p : ℕ) : ℕ := [0, 1, 2, 3, 0, 3, 1, 2, 0, 2, 3, 1].getD p 4

/-- Membership in `J_s` = diagonal ⊕ the three planes of window `s`. -/
def jMem (s : ℕ) (c : Fin 27) : Bool := decide (c.val < 3) || winOf ((c.val - 3) / 2) == s

def sheetOf (j : Fin 24) : ℕ := match aPairOf j with | none => 4 | some pr => pr.1


/-- Kernel check for one `j`: aligned certificate pairs, support of the differences inside `J_s × J_s`
on every listed position, and vanishing on the unit. -/
def nCheck (j : Fin 24) : Bool :=
  match aPairOf j, kPairOf j with
  | some pr, some kp =>
    let s := pr.1
    let dR : Fin 27 → Fin 27 → ℤ := fun c n => iAt pr.2.2.2.1 c n - litZ kp.2.2.2.1 c n
    let dI : Fin 27 → Fin 27 → ℤ := fun c n => iAt pr.2.2.2.2 c n - litZ kp.2.2.2.2 c n
    let ok : Fin 27 → Fin 27 → Bool := fun c n => (jMem s c && jMem s n) || (dR c n == 0 && dI c n == 0)
    decide (pr.1 = kp.1) && decide (pr.2.1 = kp.2.1) && decide (pr.2.2.1 = kp.2.2.1) &&
    (pr.2.2.2.1 ++ pr.2.2.2.2).all (fun e => ok e.1 e.2.1) &&
    (kp.2.2.2.1 ++ kp.2.2.2.2).all (fun e => if h : e.1 < 27 ∧ e.2.1 < 27 then ok ⟨e.1, h.1⟩ ⟨e.2.1, h.2⟩ else true) &&
    (List.finRange 27).all (fun c => dR c 0 + dR c 1 + dR c 2 == 0 && dI c 0 + dI c 1 + dI c 2 == 0)
  | _, _ => false

theorem nCheck_0 : nCheck 0 = true := by decide +kernel
theorem nCheck_1 : nCheck 1 = true := by decide +kernel
theorem nCheck_2 : nCheck 2 = true := by decide +kernel
theorem nCheck_3 : nCheck 3 = true := by decide +kernel
theorem nCheck_4 : nCheck 4 = true := by decide +kernel
theorem nCheck_5 : nCheck 5 = true := by decide +kernel
theorem nCheck_6 : nCheck 6 = true := by decide +kernel
theorem nCheck_7 : nCheck 7 = true := by decide +kernel
theorem nCheck_8 : nCheck 8 = true := by decide +kernel
theorem nCheck_9 : nCheck 9 = true := by decide +kernel
theorem nCheck_10 : nCheck 10 = true := by decide +kernel
theorem nCheck_11 : nCheck 11 = true := by decide +kernel
theorem nCheck_12 : nCheck 12 = true := by decide +kernel
theorem nCheck_13 : nCheck 13 = true := by decide +kernel
theorem nCheck_14 : nCheck 14 = true := by decide +kernel
theorem nCheck_15 : nCheck 15 = true := by decide +kernel
theorem nCheck_16 : nCheck 16 = true := by decide +kernel
theorem nCheck_17 : nCheck 17 = true := by decide +kernel
theorem nCheck_18 : nCheck 18 = true := by decide +kernel
theorem nCheck_19 : nCheck 19 = true := by decide +kernel
theorem nCheck_20 : nCheck 20 = true := by decide +kernel
theorem nCheck_21 : nCheck 21 = true := by decide +kernel
theorem nCheck_22 : nCheck 22 = true := by decide +kernel
theorem nCheck_23 : nCheck 23 = true := by decide +kernel

theorem nCheck_all : ∀ j : Fin 24, nCheck j = true := by
  intro j; fin_cases j
  · exact nCheck_0
  · exact nCheck_1
  · exact nCheck_2
  · exact nCheck_3
  · exact nCheck_4
  · exact nCheck_5
  · exact nCheck_6
  · exact nCheck_7
  · exact nCheck_8
  · exact nCheck_9
  · exact nCheck_10
  · exact nCheck_11
  · exact nCheck_12
  · exact nCheck_13
  · exact nCheck_14
  · exact nCheck_15
  · exact nCheck_16
  · exact nCheck_17
  · exact nCheck_18
  · exact nCheck_19
  · exact nCheck_20
  · exact nCheck_21
  · exact nCheck_22
  · exact nCheck_23

end Option2.NativeStress.HTPhaseComplete
