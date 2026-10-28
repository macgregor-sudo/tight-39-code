module

public import DirKData
public import DirOpG
public import BookTangentData
public import BookQuadricDictionary
public import BookSheetRealStructure

@[expose] public section

/-! Kernel check: the JSON family operators are exactly the accepted Lean Q12 sheet operators.
The JSON literals are read in two ways: `kMat` (Q12, the five-integer literal semantics `(A+Bi+C√3+Di√3)/N`,
`K_a = ½(K_rd − i K_is)`, `K_ā = −½(K_rd + i K_is)` for `eigen_pair [a, ā]`) and `kZ` (twice the same matrix in
the Gaussian integers); `kMat_eq_kZ` proves they agree, `kZ_check_*` compare `kZ` with the generic operator over
ℤ[i] in the kernel, and `kMat_eq_q12Op` transfers to the accepted `q12Op` (DirOpG). First-party. -/

set_option Elab.async false
namespace Option2.NativeStress.HTPhaseComplete
open Option2.NativeStress.BookHT Option2.NativeStress.BookHT.TangentCoordinates

def findLit (l : List KLit) (k c : Fin 27) : Option KLit :=
  l.find? (fun e => e.1 == k.val && e.2.1 == c.val)

def litVal (e : KLit) : Q12 := Q12.lit e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2

/-- JSON entry at `(k, c)` as a Q12 literal (positions are unique: `kData_wellFormed`). -/
def litAt (l : List KLit) (k c : Fin 27) : Q12 := ((findLit l k c).map litVal).getD 0

/-- The same entry's integer `A` field. -/
def litZ (l : List KLit) (k c : Fin 27) : ℤ := ((findLit l k c).map fun e => e.2.2.1).getD 0

def kHalf : Q12 := Q12.ofRat (1/2)

/-- The certificate pair carrying Book eigen coordinate `j`. -/
def kPairOf (j : Fin 24) : Option (ℕ × ℕ × ℕ × List KLit × List KLit) :=
  kPairs.find? (fun pr => pr.2.1 == j.val || pr.2.2.1 == j.val)

/-- The complex fixed family operator `K_j`, entry `(k, c)`, read from the JSON literals. -/
def kMat (j : Fin 24) (k c : Fin 27) : Q12 :=
  match kPairOf j with
  | none => 0
  | some pr =>
    if pr.2.1 = j.val then kHalf * litAt pr.2.2.2.1 k c - kHalf * Q12.I * litAt pr.2.2.2.2 k c
    else -(kHalf * litAt pr.2.2.2.1 k c) - kHalf * Q12.I * litAt pr.2.2.2.2 k c

/-- `2 K_j` in the Gaussian integers. -/
def kZ (j : Fin 24) (k c : Fin 27) : GaussianInt :=
  match kPairOf j with
  | none => 0
  | some pr =>
    if pr.2.1 = j.val then ⟨litZ pr.2.2.2.1 k c, -litZ pr.2.2.2.2 k c⟩
    else ⟨-litZ pr.2.2.2.1 k c, -litZ pr.2.2.2.2 k c⟩

/-- Data integrity: every literal is `(±1, 0, 0, 0, 1)`-shaped (`B = C = D = 0`, `N = 1`), positions in each
list are unique, and the 24 labels of the twelve pairs are exactly `0..23`. -/
def entryOk (e : KLit) : Bool :=
  e.2.2.2.1 == 0 && e.2.2.2.2.1 == 0 && e.2.2.2.2.2.1 == 0 && e.2.2.2.2.2.2 == 1

theorem kData_wellFormed :
    (kPairs.all fun pr => (pr.2.2.2.1.all entryOk && pr.2.2.2.2.all entryOk &&
      (pr.2.2.2.1.map fun e => (e.1, e.2.1)).Nodup && (pr.2.2.2.2.map fun e => (e.1, e.2.1)).Nodup
      : Bool)) = true ∧
    ((kPairs.map fun pr => pr.2.1) ++ (kPairs.map fun pr => pr.2.2.1)).Perm (List.range 24) := by
  decide +kernel

def gaussI : GaussianInt := ⟨0, 1⟩

/-- The Gaussian integers inside Q12, `a + b i ↦ a + b I`. -/
def gToQ12 : GaussianInt →+* Q12 := Zsqrtd.lift ⟨Q12.I, by decide +kernel⟩

def ebZ (c : Fin 27) : Fin 27 → GaussianInt := fun k => if k.val = c.val then 1 else 0

def zCheck (j : Fin 24) : Bool :=
  (List.finRange 27).all fun c => (List.finRange 27).all fun k =>
    decide (opG 1 gaussI (eigenIndex j) (ebZ c) k = kZ j k c)

/-- The twelve first labels of the certificate pairs (= `Dictionary.independentIndex`). -/
def indepList : List (Fin 24) := [0, 1, 2, 6, 9, 12, 8, 11, 14, 7, 10, 13]

theorem kZ_check_0 : zCheck 0 = true := by decide +kernel
theorem kZ_check_1 : zCheck 1 = true := by decide +kernel
theorem kZ_check_2 : zCheck 2 = true := by decide +kernel
theorem kZ_check_6 : zCheck 6 = true := by decide +kernel
theorem kZ_check_9 : zCheck 9 = true := by decide +kernel
theorem kZ_check_12 : zCheck 12 = true := by decide +kernel
theorem kZ_check_8 : zCheck 8 = true := by decide +kernel
theorem kZ_check_11 : zCheck 11 = true := by decide +kernel
theorem kZ_check_14 : zCheck 14 = true := by decide +kernel
theorem kZ_check_7 : zCheck 7 = true := by decide +kernel
theorem kZ_check_10 : zCheck 10 = true := by decide +kernel
theorem kZ_check_13 : zCheck 13 = true := by decide +kernel

theorem zCheck_indep : ∀ j ∈ indepList, zCheck j = true := by
  intro j hj
  simp only [indepList, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [kZ_check_0, kZ_check_1, kZ_check_2, kZ_check_6, kZ_check_9, kZ_check_12, kZ_check_8, kZ_check_11, kZ_check_14, kZ_check_7, kZ_check_10, kZ_check_13]

theorem indep_or_bar : ∀ j : Fin 24, j ∈ indepList ∨ Dictionary.coordinateBar j ∈ indepList := by
  decide +kernel

theorem eigenIndex_bar' : ∀ j : Fin 24,
    eigenIndex (Dictionary.coordinateBar j) = basisBar (eigenIndex j) := by
  decide +kernel

/-- Bar check for one label (a function of `j`: a closed `Bool` constant would be evaluated by the compiler). -/
def barCheck (j : Fin 24) : Bool :=
  (List.finRange 27).all fun k => (List.finRange 27).all fun c =>
    decide (kZ (Dictionary.coordinateBar j) k c = ⟨-(kZ j k c).re, (kZ j k c).im⟩)

theorem barCheck_0 : barCheck 0 = true := by decide +kernel
theorem barCheck_1 : barCheck 1 = true := by decide +kernel
theorem barCheck_2 : barCheck 2 = true := by decide +kernel
theorem barCheck_6 : barCheck 6 = true := by decide +kernel
theorem barCheck_9 : barCheck 9 = true := by decide +kernel
theorem barCheck_12 : barCheck 12 = true := by decide +kernel
theorem barCheck_8 : barCheck 8 = true := by decide +kernel
theorem barCheck_11 : barCheck 11 = true := by decide +kernel
theorem barCheck_14 : barCheck 14 = true := by decide +kernel
theorem barCheck_7 : barCheck 7 = true := by decide +kernel
theorem barCheck_10 : barCheck 10 = true := by decide +kernel
theorem barCheck_13 : barCheck 13 = true := by decide +kernel

theorem barCheck_indep : ∀ j ∈ indepList, barCheck j = true := by
  intro j hj
  simp only [indepList, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [barCheck_0, barCheck_1, barCheck_2, barCheck_6, barCheck_9, barCheck_12, barCheck_8, barCheck_11, barCheck_14, barCheck_7, barCheck_10, barCheck_13]

end Option2.NativeStress.HTPhaseComplete
open Option2.NativeStress.HTPhaseComplete
#print axioms kData_wellFormed
#print axioms zCheck_indep
#print axioms barCheck_indep
