module

public import TitsProduct

@[expose] public section

/-!
# Points of the configuration in Tits form (brief C3)

Non-anchor points `pt ι h t U Ut = Λ (t•1, t•U, t•Ut)` for a complexified
special-unitary pair `UPair U Ut` (`U * Utᵀ = 1`, `adj U = Utᵀ`), anchors
`anc ι h a = Λ (a, 0, 0)`.  Idempotency, trace, within-frame products, central
sums and pairings, all over a generic ring with `2h = 1`, `3t = 1`.
-/

namespace TitsS

open NativePolynomial.CoordinateMaps Matrix

variable {S : Type*} [CommRing S] (ι : Q12 →+* S)

/-! ### Polarized adjugate helpers -/

theorem crossT_smul_smul (X : M3 S) (c d : S) :
    crossT (c • X) (d • X) = (2 * c * d) • (adjugate X)ᵀ := by
  have : c • X + d • X = (c + d) • X := by rw [add_smul]
  rw [crossT, this, adjugate_smul, adjugate_smul, adjugate_smul, Fintype.card_fin]
  simp only [Nat.add_one_sub_one, transpose_sub, transpose_smul]
  module

theorem crossT_self (X : M3 S) : crossT X X = (2 : S) • (adjugate X)ᵀ := by
  have := crossT_smul_smul X 1 1
  simpa using this

theorem crossT_zero : crossT (0 : M3 S) 0 = 0 := by
  simp [crossT, adjugate_zero]

/-! ### Complexified special-unitary pairs -/

/-- `U * Utᵀ = 1` and `adj U = Utᵀ`: the complexification of "U is special unitary
with `Ut = conj U`". -/
def UPair (U Ut : M3 S) : Prop := U * Utᵀ = 1 ∧ adjugate U = Utᵀ

namespace UPair

variable {U Ut : M3 S} (hU : UPair U Ut)
include hU

theorem det_eq_one : det U = 1 := by
  have h1 : U * adjugate U = det U • (1 : M3 S) := mul_adjugate U
  rw [hU.2, hU.1] at h1
  have := congrFun (congrFun h1 0) 0
  simpa using this.symm

theorem mulT_left : Utᵀ * U = 1 := by
  rw [← hU.2, adjugate_mul, hU.det_eq_one, one_smul]

theorem adjugate_Ut : adjugate Ut = Uᵀ := by
  have h3 : adjugate (Utᵀ) = U := by
    rw [← hU.2, adjugate_adjugate U (by simp), hU.det_eq_one]
    simp
  have h4 : (adjugate Ut)ᵀ = U := by rw [adjugate_transpose, h3]
  rw [← h4, transpose_transpose]

theorem adjugate_Ut_transpose : (adjugate Ut)ᵀ = U := by
  rw [hU.adjugate_Ut, transpose_transpose]

theorem adjugate_U_transpose : (adjugate U)ᵀ = Ut := by
  rw [hU.2, transpose_transpose]

theorem symm : UPair Ut U := by
  refine ⟨?_, hU.adjugate_Ut⟩
  have h2 := congrArg Matrix.transpose hU.1
  rwa [transpose_mul, transpose_transpose, transpose_one] at h2

theorem mul {V Vt : M3 S} (hV : UPair V Vt) : UPair (U * V) (Ut * Vt) := by
  constructor
  · rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc V, hV.1, Matrix.one_mul, hU.1]
  · rw [adjugate_mul_distrib, hU.2, hV.2, transpose_mul]

theorem smul {c c' : S} (hc : c * c' = 1) (hc3 : c ^ 3 = 1) : UPair (c • U) (c' • Ut) := by
  constructor
  · rw [transpose_smul, smul_mul, Matrix.mul_smul, smul_smul, hU.1, hc, one_smul]
  · rw [adjugate_smul, hU.2, transpose_smul, Fintype.card_fin, Nat.add_one_sub_one]
    congr 1
    linear_combination (-c ^ 2) * hc + c' * hc3

omit hU in
theorem one : UPair (1 : M3 S) 1 := by
  constructor
  · simp
  · simp [adjugate_one]

end UPair

/-! ### Tits triples of points and anchors -/

/-- Tits triple of a non-anchor point. -/
def ptTits (t : S) (U Ut : M3 S) : Tits S := (t • (1 : M3 S), t • U, t • Ut)

/-- Native coordinates of a non-anchor point. -/
def pt (h t : S) (U Ut : M3 S) : Fin 27 → S := titsToNative ι h (ptTits t U Ut)

/-- Tits triple of an anchor. -/
def ancTits (a : M3 S) : Tits S := (a, 0, 0)

/-- Native coordinates of an anchor. -/
def anc (h : S) (a : M3 S) : Fin 27 → S := titsToNative ι h (ancTits a)

section TitsLevel

variable (h t : S) (h2 : (2 : S) * h = 1) (t3 : (3 : S) * t = 1)
variable {U Ut : M3 S} (hU : UPair U Ut)
include h2 t3 hU

theorem ptTits_sq : titsProduct h (ptTits t U Ut) (ptTits t U Ut) = ptTits t U Ut := by
  have key : t = 6 * h * t * t := by linear_combination (-(3 * t * t)) * h2 + (-t) * t3
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [titsProduct, ptTits, transpose_smul, smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.one_mul, hU.1, trace_smul, trace_one, Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul]
    rw [show (t • (1 : M3 S)) = (6 * h * t * t) • 1 by rw [← key]]
    module
  · simp only [titsProduct, ptTits, crossT_smul_smul, hU.adjugate_Ut_transpose, transpose_smul,
      smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.sub_mul, trace_smul, trace_one,
      Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul]
    conv_rhs => rw [key]
    module
  · simp only [titsProduct, ptTits, crossT_smul_smul, hU.adjugate_U_transpose, transpose_smul,
      transpose_one, smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.sub_mul,
      trace_smul, trace_one, Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul]
    conv_rhs => rw [key]
    module

omit h2 t3 in
/-- Two scaled copies of a special-unitary pair in the same frame have product zero when the
phases `c, d` (with partners `c', d'`) satisfy the three cyclotomic relations. -/
theorem ptTits_mul_zero {c c' d d' : S}
    (hA : c * d' + c' * d = -1) (hC : c + d + c' * d' = 0) (hCt : c' + d' + c * d = 0) :
    titsProduct h (ptTits t (c • U) (c' • Ut)) (ptTits t (d • U) (d' • Ut)) = 0 := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [titsProduct, ptTits, transpose_smul, smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.one_mul, hU.1, trace_smul, trace_one, Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul]
    trans (h * t * t * (2 + 2 * (c * d' + c' * d))) • (1 : M3 S)
    · module
    · rw [hA]; norm_num
  · simp only [titsProduct, ptTits, smul_smul, crossT_smul_smul, hU.adjugate_Ut_transpose,
      transpose_smul, smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.sub_mul, trace_smul,
      trace_one, Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul]
    trans (h * t * t * (2 * (c + d + c' * d'))) • U
    · module
    · rw [hC]; simp
  · simp only [titsProduct, ptTits, smul_smul, crossT_smul_smul, hU.adjugate_U_transpose,
      transpose_smul, transpose_one, smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.sub_mul,
      trace_smul, trace_one, Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul]
    trans (h * t * t * (2 * (c' + d' + c * d))) • Ut
    · module
    · rw [hCt]; simp

end TitsLevel

theorem ptTits_sum_three (t : S) (t3 : (3 : S) * t = 1) (U Ut : M3 S)
    {c0 c1 c2 c0' c1' c2' : S} (hc : c0 + c1 + c2 = 0) (hc' : c0' + c1' + c2' = 0) :
    ptTits t (c0 • U) (c0' • Ut) + ptTits t (c1 • U) (c1' • Ut) + ptTits t (c2 • U) (c2' • Ut) =
      ((1 : M3 S), 0, 0) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [ptTits, Prod.fst_add]
    trans (3 * t) • (1 : M3 S)
    · module
    · rw [t3, one_smul]
  · simp only [ptTits, Prod.snd_add, Prod.fst_add]
    trans (t * (c0 + c1 + c2)) • U
    · module
    · rw [hc, mul_zero, zero_smul]
  · simp only [ptTits, Prod.snd_add]
    trans (t * (c0' + c1' + c2')) • Ut
    · module
    · rw [hc', mul_zero, zero_smul]

/-! ### Native-coordinate statements -/

section Native

variable (h t : S)

theorem pt_idem (h2 : (2 : S) * h = 1) (t3 : (3 : S) * t = 1) {U Ut : M3 S} (hU : UPair U Ut) :
    coordinateProduct h (pt ι h t U Ut) (pt ι h t U Ut) = pt ι h t U Ut := by
  rw [pt, product_titsToNative ι h h2, ptTits_sq h t h2 t3 hU]

theorem pt_trace (h2 : (2 : S) * h = 1) (t3 : (3 : S) * t = 1) (U Ut : M3 S) : coordinateTrace (pt ι h t U Ut) = 1 := by
  rw [pt, trace_titsToNative ι h h2]
  simp only [ptTits, trace_smul, trace_one, Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul]
  linear_combination t3

theorem pt_mul_zero (h2 : (2 : S) * h = 1) {U Ut : M3 S} (hU : UPair U Ut) {c c' d d' : S}
    (hA : c * d' + c' * d = -1) (hC : c + d + c' * d' = 0) (hCt : c' + d' + c * d = 0) :
    coordinateProduct h (pt ι h t (c • U) (c' • Ut)) (pt ι h t (d • U) (d' • Ut)) = 0 := by
  rw [pt, pt, product_titsToNative ι h h2, ptTits_mul_zero h t hU hA hC hCt, titsToNative_zero]

theorem pt_sum_three (h2 : (2 : S) * h = 1) (t3 : (3 : S) * t = 1) (U Ut : M3 S) {c0 c1 c2 c0' c1' c2' : S}
    (hc : c0 + c1 + c2 = 0) (hc' : c0' + c1' + c2' = 0) :
    pt ι h t (c0 • U) (c0' • Ut) + pt ι h t (c1 • U) (c1' • Ut) + pt ι h t (c2 • U) (c2' • Ut) =
      coordinateUnit := by
  simp only [pt, ← titsToNative_add]
  rw [ptTits_sum_three t t3 U Ut hc hc', titsToNative_unit ι h h2]

theorem pt_pairing (h2 : (2 : S) * h = 1) (t3 : (3 : S) * t = 1) (U Ut V Vt : M3 S) :
    coordinatePairing (pt ι h t U Ut) (pt ι h t V Vt) =
      t + t * t * (trace (U * Vtᵀ) + trace (V * Utᵀ)) := by
  rw [pt, pt, pairing_titsToNative ι h h2]
  simp only [ptTits, transpose_smul, smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul,
    trace_smul, trace_one, Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul]
  linear_combination t * t3

theorem pt_pairing_of_trace_zero (h2 : (2 : S) * h = 1) (t3 : (3 : S) * t = 1) (U Ut V Vt : M3 S)
    (h1 : trace (U * Vtᵀ) = 0) (h1' : trace (V * Utᵀ) = 0) :
    coordinatePairing (pt ι h t U Ut) (pt ι h t V Vt) = t := by
  rw [pt_pairing ι h t h2 t3, h1, h1']
  ring

theorem ancTits_product (a b : M3 S) :
    titsProduct h (ancTits a) (ancTits b) = ancTits (h • (a * b + b * a)) := by
  simp [titsProduct, ancTits, crossT_zero]

theorem anc_product (h2 : (2 : S) * h = 1) (a b : M3 S) :
    coordinateProduct h (anc ι h a) (anc ι h b) = anc ι h (h • (a * b + b * a)) := by
  rw [anc, anc, product_titsToNative ι h h2, ancTits_product]
  rfl

theorem anc_idem (h2 : (2 : S) * h = 1) {a : M3 S} (ha : a * a = a) :
    coordinateProduct h (anc ι h a) (anc ι h a) = anc ι h a := by
  rw [anc_product ι h h2, ha, ← two_smul S a, smul_smul, mul_comm, h2, one_smul]

theorem anc_zero : anc ι h 0 = 0 := by
  show titsToNative ι h 0 = 0
  exact titsToNative_zero ι h

theorem anc_mul_zero (h2 : (2 : S) * h = 1) {a b : M3 S} (hab : a * b + b * a = 0) :
    coordinateProduct h (anc ι h a) (anc ι h b) = 0 := by
  rw [anc_product ι h h2, hab, smul_zero, anc_zero]

theorem anc_trace (h2 : (2 : S) * h = 1) (a : M3 S) : coordinateTrace (anc ι h a) = trace a := by
  rw [anc, trace_titsToNative ι h h2]
  rfl

theorem anc_add (a b : M3 S) : anc ι h a + anc ι h b = anc ι h (a + b) := by
  rw [anc, anc, anc, ← titsToNative_add]
  congr 1
  simp [ancTits]

theorem anc_one (h2 : (2 : S) * h = 1) : anc ι h 1 = coordinateUnit := titsToNative_unit ι h h2

theorem anc_pairing_anc (h2 : (2 : S) * h = 1) (a b : M3 S) :
    coordinatePairing (anc ι h a) (anc ι h b) = trace (a * b) := by
  rw [anc, anc, pairing_titsToNative ι h h2]
  simp [ancTits]

theorem anc_pairing_pt (h2 : (2 : S) * h = 1) (a U Ut : M3 S) :
    coordinatePairing (anc ι h a) (pt ι h t U Ut) = t * trace a := by
  rw [anc, pt, pairing_titsToNative ι h h2]
  simp [ancTits, ptTits, trace_smul]

theorem pt_pairing_anc (h2 : (2 : S) * h = 1) (a U Ut : M3 S) :
    coordinatePairing (pt ι h t U Ut) (anc ι h a) = t * trace a := by
  rw [pt, anc, pairing_titsToNative ι h h2]
  simp [ancTits, ptTits, trace_smul]

end Native

end TitsS

#print axioms TitsS.pt_idem
#print axioms TitsS.pt_mul_zero
#print axioms TitsS.pt_sum_three
#print axioms TitsS.pt_pairing
#print axioms TitsS.anc_idem
#print axioms TitsS.anc_pairing_pt
#print axioms TitsS.UPair.mul
#print axioms TitsS.UPair.smul
