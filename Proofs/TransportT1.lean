module

public import AutS
public import TransportData

@[expose] public section

/-! Transport T1 (with coordinate permutation `T1_perm` and signs `T1_sign`) is a structure automorphism: kernel `decide` per output. -/

namespace TitsS.Transport

def T1p : Fin 27 → Fin 27 := permOfList T1_perm
def T1pinv : Fin 27 → Fin 27 := permOfList T1_inv_perm
def T1s : Fin 27 → ℤ := sgnOfList T1_sign

theorem T1_structureAut : IsStructureAut T1p T1pinv T1s := by decide

theorem T1_numOK_0 : numOK T1p T1s 0 := by decide
theorem T1_numOK_1 : numOK T1p T1s 1 := by decide
theorem T1_numOK_2 : numOK T1p T1s 2 := by decide
theorem T1_numOK_3 : numOK T1p T1s 3 := by decide
theorem T1_numOK_4 : numOK T1p T1s 4 := by decide
theorem T1_numOK_5 : numOK T1p T1s 5 := by decide
theorem T1_numOK_6 : numOK T1p T1s 6 := by decide
theorem T1_numOK_7 : numOK T1p T1s 7 := by decide
theorem T1_numOK_8 : numOK T1p T1s 8 := by decide
theorem T1_numOK_9 : numOK T1p T1s 9 := by decide
theorem T1_numOK_10 : numOK T1p T1s 10 := by decide
theorem T1_numOK_11 : numOK T1p T1s 11 := by decide
theorem T1_numOK_12 : numOK T1p T1s 12 := by decide
theorem T1_numOK_13 : numOK T1p T1s 13 := by decide
theorem T1_numOK_14 : numOK T1p T1s 14 := by decide
theorem T1_numOK_15 : numOK T1p T1s 15 := by decide
theorem T1_numOK_16 : numOK T1p T1s 16 := by decide
theorem T1_numOK_17 : numOK T1p T1s 17 := by decide
theorem T1_numOK_18 : numOK T1p T1s 18 := by decide
theorem T1_numOK_19 : numOK T1p T1s 19 := by decide
theorem T1_numOK_20 : numOK T1p T1s 20 := by decide
theorem T1_numOK_21 : numOK T1p T1s 21 := by decide
theorem T1_numOK_22 : numOK T1p T1s 22 := by decide
theorem T1_numOK_23 : numOK T1p T1s 23 := by decide
theorem T1_numOK_24 : numOK T1p T1s 24 := by decide
theorem T1_numOK_25 : numOK T1p T1s 25 := by decide
theorem T1_numOK_26 : numOK T1p T1s 26 := by decide

theorem T1_numOK : ∀ k, numOK T1p T1s k := by
  intro k
  fin_cases k
  exacts [T1_numOK_0, T1_numOK_1, T1_numOK_2, T1_numOK_3, T1_numOK_4, T1_numOK_5, T1_numOK_6, T1_numOK_7, T1_numOK_8, T1_numOK_9, T1_numOK_10, T1_numOK_11, T1_numOK_12, T1_numOK_13, T1_numOK_14, T1_numOK_15, T1_numOK_16, T1_numOK_17, T1_numOK_18, T1_numOK_19, T1_numOK_20, T1_numOK_21, T1_numOK_22, T1_numOK_23, T1_numOK_24, T1_numOK_25, T1_numOK_26]

theorem T1_isAut {S : Type*} [CommRing S] (h : S) :
    IsAut h (sgnPerm T1p T1s : (Fin 27 → S) → (Fin 27 → S)) :=
  sgnPerm_isAut h T1_structureAut T1_numOK

/-! The inverse transport (data lists `T1_inv_perm`, `T1_inv_sign`). -/

def T1si : Fin 27 → ℤ := sgnOfList T1_inv_sign

theorem T1_inv_structureAut : IsStructureAut T1pinv T1p T1si := by decide

theorem T1_inv_numOK_0 : numOK T1pinv T1si 0 := by decide
theorem T1_inv_numOK_1 : numOK T1pinv T1si 1 := by decide
theorem T1_inv_numOK_2 : numOK T1pinv T1si 2 := by decide
theorem T1_inv_numOK_3 : numOK T1pinv T1si 3 := by decide
theorem T1_inv_numOK_4 : numOK T1pinv T1si 4 := by decide
theorem T1_inv_numOK_5 : numOK T1pinv T1si 5 := by decide
theorem T1_inv_numOK_6 : numOK T1pinv T1si 6 := by decide
theorem T1_inv_numOK_7 : numOK T1pinv T1si 7 := by decide
theorem T1_inv_numOK_8 : numOK T1pinv T1si 8 := by decide
theorem T1_inv_numOK_9 : numOK T1pinv T1si 9 := by decide
theorem T1_inv_numOK_10 : numOK T1pinv T1si 10 := by decide
theorem T1_inv_numOK_11 : numOK T1pinv T1si 11 := by decide
theorem T1_inv_numOK_12 : numOK T1pinv T1si 12 := by decide
theorem T1_inv_numOK_13 : numOK T1pinv T1si 13 := by decide
theorem T1_inv_numOK_14 : numOK T1pinv T1si 14 := by decide
theorem T1_inv_numOK_15 : numOK T1pinv T1si 15 := by decide
theorem T1_inv_numOK_16 : numOK T1pinv T1si 16 := by decide
theorem T1_inv_numOK_17 : numOK T1pinv T1si 17 := by decide
theorem T1_inv_numOK_18 : numOK T1pinv T1si 18 := by decide
theorem T1_inv_numOK_19 : numOK T1pinv T1si 19 := by decide
theorem T1_inv_numOK_20 : numOK T1pinv T1si 20 := by decide
theorem T1_inv_numOK_21 : numOK T1pinv T1si 21 := by decide
theorem T1_inv_numOK_22 : numOK T1pinv T1si 22 := by decide
theorem T1_inv_numOK_23 : numOK T1pinv T1si 23 := by decide
theorem T1_inv_numOK_24 : numOK T1pinv T1si 24 := by decide
theorem T1_inv_numOK_25 : numOK T1pinv T1si 25 := by decide
theorem T1_inv_numOK_26 : numOK T1pinv T1si 26 := by decide

theorem T1_inv_numOK : ∀ k, numOK T1pinv T1si k := by
  intro k
  fin_cases k
  exacts [T1_inv_numOK_0, T1_inv_numOK_1, T1_inv_numOK_2, T1_inv_numOK_3, T1_inv_numOK_4, T1_inv_numOK_5, T1_inv_numOK_6, T1_inv_numOK_7, T1_inv_numOK_8, T1_inv_numOK_9, T1_inv_numOK_10, T1_inv_numOK_11, T1_inv_numOK_12, T1_inv_numOK_13, T1_inv_numOK_14, T1_inv_numOK_15, T1_inv_numOK_16, T1_inv_numOK_17, T1_inv_numOK_18, T1_inv_numOK_19, T1_inv_numOK_20, T1_inv_numOK_21, T1_inv_numOK_22, T1_inv_numOK_23, T1_inv_numOK_24, T1_inv_numOK_25, T1_inv_numOK_26]

theorem T1_inv_isAut {S : Type*} [CommRing S] (h : S) :
    IsAut h (sgnPerm T1pinv T1si : (Fin 27 → S) → (Fin 27 → S)) :=
  sgnPerm_isAut h T1_inv_structureAut T1_inv_numOK

theorem T1_inv_rel : ∀ k, T1s k * T1si (T1p k) = 1 ∧ T1pinv (T1p k) = k := by decide

theorem T1_comp_inv {S : Type*} [CommRing S] (x : Fin 27 → S) :
    sgnPerm T1p T1s (sgnPerm T1pinv T1si x) = x := by
  funext k
  simp only [sgnPerm]
  rw [(T1_inv_rel k).2, ← mul_assoc, ← Int.cast_mul, (T1_inv_rel k).1, Int.cast_one, one_mul]

end TitsS.Transport

#print axioms TitsS.Transport.T1_isAut
#print axioms TitsS.Transport.T1_inv_isAut
#print axioms TitsS.Transport.T1_comp_inv
