module

public import AutS
public import TransportData

@[expose] public section

/-! Transport T3 (with coordinate permutation `T3_perm` and signs `T3_sign`) is a structure automorphism: kernel `decide` per output. -/

namespace TitsS.Transport

def T3p : Fin 27 → Fin 27 := permOfList T3_perm
def T3pinv : Fin 27 → Fin 27 := permOfList T3_inv_perm
def T3s : Fin 27 → ℤ := sgnOfList T3_sign

theorem T3_structureAut : IsStructureAut T3p T3pinv T3s := by decide

theorem T3_numOK_0 : numOK T3p T3s 0 := by decide
theorem T3_numOK_1 : numOK T3p T3s 1 := by decide
theorem T3_numOK_2 : numOK T3p T3s 2 := by decide
theorem T3_numOK_3 : numOK T3p T3s 3 := by decide
theorem T3_numOK_4 : numOK T3p T3s 4 := by decide
theorem T3_numOK_5 : numOK T3p T3s 5 := by decide
theorem T3_numOK_6 : numOK T3p T3s 6 := by decide
theorem T3_numOK_7 : numOK T3p T3s 7 := by decide
theorem T3_numOK_8 : numOK T3p T3s 8 := by decide
theorem T3_numOK_9 : numOK T3p T3s 9 := by decide
theorem T3_numOK_10 : numOK T3p T3s 10 := by decide
theorem T3_numOK_11 : numOK T3p T3s 11 := by decide
theorem T3_numOK_12 : numOK T3p T3s 12 := by decide
theorem T3_numOK_13 : numOK T3p T3s 13 := by decide
theorem T3_numOK_14 : numOK T3p T3s 14 := by decide
theorem T3_numOK_15 : numOK T3p T3s 15 := by decide
theorem T3_numOK_16 : numOK T3p T3s 16 := by decide
theorem T3_numOK_17 : numOK T3p T3s 17 := by decide
theorem T3_numOK_18 : numOK T3p T3s 18 := by decide
theorem T3_numOK_19 : numOK T3p T3s 19 := by decide
theorem T3_numOK_20 : numOK T3p T3s 20 := by decide
theorem T3_numOK_21 : numOK T3p T3s 21 := by decide
theorem T3_numOK_22 : numOK T3p T3s 22 := by decide
theorem T3_numOK_23 : numOK T3p T3s 23 := by decide
theorem T3_numOK_24 : numOK T3p T3s 24 := by decide
theorem T3_numOK_25 : numOK T3p T3s 25 := by decide
theorem T3_numOK_26 : numOK T3p T3s 26 := by decide

theorem T3_numOK : ∀ k, numOK T3p T3s k := by
  intro k
  fin_cases k
  exacts [T3_numOK_0, T3_numOK_1, T3_numOK_2, T3_numOK_3, T3_numOK_4, T3_numOK_5, T3_numOK_6, T3_numOK_7, T3_numOK_8, T3_numOK_9, T3_numOK_10, T3_numOK_11, T3_numOK_12, T3_numOK_13, T3_numOK_14, T3_numOK_15, T3_numOK_16, T3_numOK_17, T3_numOK_18, T3_numOK_19, T3_numOK_20, T3_numOK_21, T3_numOK_22, T3_numOK_23, T3_numOK_24, T3_numOK_25, T3_numOK_26]

theorem T3_isAut {S : Type*} [CommRing S] (h : S) :
    IsAut h (sgnPerm T3p T3s : (Fin 27 → S) → (Fin 27 → S)) :=
  sgnPerm_isAut h T3_structureAut T3_numOK

/-! The inverse transport (data lists `T3_inv_perm`, `T3_inv_sign`). -/

def T3si : Fin 27 → ℤ := sgnOfList T3_inv_sign

theorem T3_inv_structureAut : IsStructureAut T3pinv T3p T3si := by decide

theorem T3_inv_numOK_0 : numOK T3pinv T3si 0 := by decide
theorem T3_inv_numOK_1 : numOK T3pinv T3si 1 := by decide
theorem T3_inv_numOK_2 : numOK T3pinv T3si 2 := by decide
theorem T3_inv_numOK_3 : numOK T3pinv T3si 3 := by decide
theorem T3_inv_numOK_4 : numOK T3pinv T3si 4 := by decide
theorem T3_inv_numOK_5 : numOK T3pinv T3si 5 := by decide
theorem T3_inv_numOK_6 : numOK T3pinv T3si 6 := by decide
theorem T3_inv_numOK_7 : numOK T3pinv T3si 7 := by decide
theorem T3_inv_numOK_8 : numOK T3pinv T3si 8 := by decide
theorem T3_inv_numOK_9 : numOK T3pinv T3si 9 := by decide
theorem T3_inv_numOK_10 : numOK T3pinv T3si 10 := by decide
theorem T3_inv_numOK_11 : numOK T3pinv T3si 11 := by decide
theorem T3_inv_numOK_12 : numOK T3pinv T3si 12 := by decide
theorem T3_inv_numOK_13 : numOK T3pinv T3si 13 := by decide
theorem T3_inv_numOK_14 : numOK T3pinv T3si 14 := by decide
theorem T3_inv_numOK_15 : numOK T3pinv T3si 15 := by decide
theorem T3_inv_numOK_16 : numOK T3pinv T3si 16 := by decide
theorem T3_inv_numOK_17 : numOK T3pinv T3si 17 := by decide
theorem T3_inv_numOK_18 : numOK T3pinv T3si 18 := by decide
theorem T3_inv_numOK_19 : numOK T3pinv T3si 19 := by decide
theorem T3_inv_numOK_20 : numOK T3pinv T3si 20 := by decide
theorem T3_inv_numOK_21 : numOK T3pinv T3si 21 := by decide
theorem T3_inv_numOK_22 : numOK T3pinv T3si 22 := by decide
theorem T3_inv_numOK_23 : numOK T3pinv T3si 23 := by decide
theorem T3_inv_numOK_24 : numOK T3pinv T3si 24 := by decide
theorem T3_inv_numOK_25 : numOK T3pinv T3si 25 := by decide
theorem T3_inv_numOK_26 : numOK T3pinv T3si 26 := by decide

theorem T3_inv_numOK : ∀ k, numOK T3pinv T3si k := by
  intro k
  fin_cases k
  exacts [T3_inv_numOK_0, T3_inv_numOK_1, T3_inv_numOK_2, T3_inv_numOK_3, T3_inv_numOK_4, T3_inv_numOK_5, T3_inv_numOK_6, T3_inv_numOK_7, T3_inv_numOK_8, T3_inv_numOK_9, T3_inv_numOK_10, T3_inv_numOK_11, T3_inv_numOK_12, T3_inv_numOK_13, T3_inv_numOK_14, T3_inv_numOK_15, T3_inv_numOK_16, T3_inv_numOK_17, T3_inv_numOK_18, T3_inv_numOK_19, T3_inv_numOK_20, T3_inv_numOK_21, T3_inv_numOK_22, T3_inv_numOK_23, T3_inv_numOK_24, T3_inv_numOK_25, T3_inv_numOK_26]

theorem T3_inv_isAut {S : Type*} [CommRing S] (h : S) :
    IsAut h (sgnPerm T3pinv T3si : (Fin 27 → S) → (Fin 27 → S)) :=
  sgnPerm_isAut h T3_inv_structureAut T3_inv_numOK

theorem T3_inv_rel : ∀ k, T3s k * T3si (T3p k) = 1 ∧ T3pinv (T3p k) = k := by decide

theorem T3_comp_inv {S : Type*} [CommRing S] (x : Fin 27 → S) :
    sgnPerm T3p T3s (sgnPerm T3pinv T3si x) = x := by
  funext k
  simp only [sgnPerm]
  rw [(T3_inv_rel k).2, ← mul_assoc, ← Int.cast_mul, (T3_inv_rel k).1, Int.cast_one, one_mul]

end TitsS.Transport

#print axioms TitsS.Transport.T3_isAut
#print axioms TitsS.Transport.T3_inv_isAut
#print axioms TitsS.Transport.T3_comp_inv
