module

public import AutS
public import TransportData

@[expose] public section

/-! Transport T2 (with coordinate permutation `T2_perm` and signs `T2_sign`) is a structure automorphism: kernel `decide` per output. -/

namespace TitsS.Transport

def T2p : Fin 27 → Fin 27 := permOfList T2_perm
def T2pinv : Fin 27 → Fin 27 := permOfList T2_inv_perm
def T2s : Fin 27 → ℤ := sgnOfList T2_sign

theorem T2_structureAut : IsStructureAut T2p T2pinv T2s := by decide

theorem T2_numOK_0 : numOK T2p T2s 0 := by decide
theorem T2_numOK_1 : numOK T2p T2s 1 := by decide
theorem T2_numOK_2 : numOK T2p T2s 2 := by decide
theorem T2_numOK_3 : numOK T2p T2s 3 := by decide
theorem T2_numOK_4 : numOK T2p T2s 4 := by decide
theorem T2_numOK_5 : numOK T2p T2s 5 := by decide
theorem T2_numOK_6 : numOK T2p T2s 6 := by decide
theorem T2_numOK_7 : numOK T2p T2s 7 := by decide
theorem T2_numOK_8 : numOK T2p T2s 8 := by decide
theorem T2_numOK_9 : numOK T2p T2s 9 := by decide
theorem T2_numOK_10 : numOK T2p T2s 10 := by decide
theorem T2_numOK_11 : numOK T2p T2s 11 := by decide
theorem T2_numOK_12 : numOK T2p T2s 12 := by decide
theorem T2_numOK_13 : numOK T2p T2s 13 := by decide
theorem T2_numOK_14 : numOK T2p T2s 14 := by decide
theorem T2_numOK_15 : numOK T2p T2s 15 := by decide
theorem T2_numOK_16 : numOK T2p T2s 16 := by decide
theorem T2_numOK_17 : numOK T2p T2s 17 := by decide
theorem T2_numOK_18 : numOK T2p T2s 18 := by decide
theorem T2_numOK_19 : numOK T2p T2s 19 := by decide
theorem T2_numOK_20 : numOK T2p T2s 20 := by decide
theorem T2_numOK_21 : numOK T2p T2s 21 := by decide
theorem T2_numOK_22 : numOK T2p T2s 22 := by decide
theorem T2_numOK_23 : numOK T2p T2s 23 := by decide
theorem T2_numOK_24 : numOK T2p T2s 24 := by decide
theorem T2_numOK_25 : numOK T2p T2s 25 := by decide
theorem T2_numOK_26 : numOK T2p T2s 26 := by decide

theorem T2_numOK : ∀ k, numOK T2p T2s k := by
  intro k
  fin_cases k
  exacts [T2_numOK_0, T2_numOK_1, T2_numOK_2, T2_numOK_3, T2_numOK_4, T2_numOK_5, T2_numOK_6, T2_numOK_7, T2_numOK_8, T2_numOK_9, T2_numOK_10, T2_numOK_11, T2_numOK_12, T2_numOK_13, T2_numOK_14, T2_numOK_15, T2_numOK_16, T2_numOK_17, T2_numOK_18, T2_numOK_19, T2_numOK_20, T2_numOK_21, T2_numOK_22, T2_numOK_23, T2_numOK_24, T2_numOK_25, T2_numOK_26]

theorem T2_isAut {S : Type*} [CommRing S] (h : S) :
    IsAut h (sgnPerm T2p T2s : (Fin 27 → S) → (Fin 27 → S)) :=
  sgnPerm_isAut h T2_structureAut T2_numOK

/-! The inverse transport (data lists `T2_inv_perm`, `T2_inv_sign`). -/

def T2si : Fin 27 → ℤ := sgnOfList T2_inv_sign

theorem T2_inv_structureAut : IsStructureAut T2pinv T2p T2si := by decide

theorem T2_inv_numOK_0 : numOK T2pinv T2si 0 := by decide
theorem T2_inv_numOK_1 : numOK T2pinv T2si 1 := by decide
theorem T2_inv_numOK_2 : numOK T2pinv T2si 2 := by decide
theorem T2_inv_numOK_3 : numOK T2pinv T2si 3 := by decide
theorem T2_inv_numOK_4 : numOK T2pinv T2si 4 := by decide
theorem T2_inv_numOK_5 : numOK T2pinv T2si 5 := by decide
theorem T2_inv_numOK_6 : numOK T2pinv T2si 6 := by decide
theorem T2_inv_numOK_7 : numOK T2pinv T2si 7 := by decide
theorem T2_inv_numOK_8 : numOK T2pinv T2si 8 := by decide
theorem T2_inv_numOK_9 : numOK T2pinv T2si 9 := by decide
theorem T2_inv_numOK_10 : numOK T2pinv T2si 10 := by decide
theorem T2_inv_numOK_11 : numOK T2pinv T2si 11 := by decide
theorem T2_inv_numOK_12 : numOK T2pinv T2si 12 := by decide
theorem T2_inv_numOK_13 : numOK T2pinv T2si 13 := by decide
theorem T2_inv_numOK_14 : numOK T2pinv T2si 14 := by decide
theorem T2_inv_numOK_15 : numOK T2pinv T2si 15 := by decide
theorem T2_inv_numOK_16 : numOK T2pinv T2si 16 := by decide
theorem T2_inv_numOK_17 : numOK T2pinv T2si 17 := by decide
theorem T2_inv_numOK_18 : numOK T2pinv T2si 18 := by decide
theorem T2_inv_numOK_19 : numOK T2pinv T2si 19 := by decide
theorem T2_inv_numOK_20 : numOK T2pinv T2si 20 := by decide
theorem T2_inv_numOK_21 : numOK T2pinv T2si 21 := by decide
theorem T2_inv_numOK_22 : numOK T2pinv T2si 22 := by decide
theorem T2_inv_numOK_23 : numOK T2pinv T2si 23 := by decide
theorem T2_inv_numOK_24 : numOK T2pinv T2si 24 := by decide
theorem T2_inv_numOK_25 : numOK T2pinv T2si 25 := by decide
theorem T2_inv_numOK_26 : numOK T2pinv T2si 26 := by decide

theorem T2_inv_numOK : ∀ k, numOK T2pinv T2si k := by
  intro k
  fin_cases k
  exacts [T2_inv_numOK_0, T2_inv_numOK_1, T2_inv_numOK_2, T2_inv_numOK_3, T2_inv_numOK_4, T2_inv_numOK_5, T2_inv_numOK_6, T2_inv_numOK_7, T2_inv_numOK_8, T2_inv_numOK_9, T2_inv_numOK_10, T2_inv_numOK_11, T2_inv_numOK_12, T2_inv_numOK_13, T2_inv_numOK_14, T2_inv_numOK_15, T2_inv_numOK_16, T2_inv_numOK_17, T2_inv_numOK_18, T2_inv_numOK_19, T2_inv_numOK_20, T2_inv_numOK_21, T2_inv_numOK_22, T2_inv_numOK_23, T2_inv_numOK_24, T2_inv_numOK_25, T2_inv_numOK_26]

theorem T2_inv_isAut {S : Type*} [CommRing S] (h : S) :
    IsAut h (sgnPerm T2pinv T2si : (Fin 27 → S) → (Fin 27 → S)) :=
  sgnPerm_isAut h T2_inv_structureAut T2_inv_numOK

theorem T2_inv_rel : ∀ k, T2s k * T2si (T2p k) = 1 ∧ T2pinv (T2p k) = k := by decide

theorem T2_comp_inv {S : Type*} [CommRing S] (x : Fin 27 → S) :
    sgnPerm T2p T2s (sgnPerm T2pinv T2si x) = x := by
  funext k
  simp only [sgnPerm]
  rw [(T2_inv_rel k).2, ← mul_assoc, ← Int.cast_mul, (T2_inv_rel k).1, Int.cast_one, one_mul]

end TitsS.Transport

#print axioms TitsS.Transport.T2_isAut
#print axioms TitsS.Transport.T2_inv_isAut
#print axioms TitsS.Transport.T2_comp_inv
