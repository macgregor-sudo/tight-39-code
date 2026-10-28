module

public import TitsProdA
public import TitsProdB
public import TitsProdBt

@[expose] public section

/-!
# The Tits product identity, assembled

`titsOfNative ι (x ∘ y) = titsProduct h (titsOfNative ι x) (titsOfNative ι y)` for the
native product `x ∘ y = coordinateProduct h x y` (any `h`), and its transported form
`titsToNative ι h p ∘ titsToNative ι h q = titsToNative ι h (titsProduct h p q)` (needs
`2 * h = 1`).  Trace, unit and pairing in Tits coordinates.
-/

namespace TitsS

open NativePolynomial.CoordinateMaps Matrix

variable {S : Type*} [CommRing S] (ι : Q12 →+* S)

theorem titsOfNative_product (h : S) (x y : Fin 27 → S) :
    titsOfNative ι (coordinateProduct h x y) =
      titsProduct h (titsOfNative ι x) (titsOfNative ι y) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  all_goals ext i j
  all_goals fin_cases i <;> fin_cases j
  · exact prod_a00 ι h x y
  · exact prod_a01 ι h x y
  · exact prod_a02 ι h x y
  · exact prod_a10 ι h x y
  · exact prod_a11 ι h x y
  · exact prod_a12 ι h x y
  · exact prod_a20 ι h x y
  · exact prod_a21 ι h x y
  · exact prod_a22 ι h x y
  · exact prod_B00 ι h x y
  · exact prod_B01 ι h x y
  · exact prod_B02 ι h x y
  · exact prod_B10 ι h x y
  · exact prod_B11 ι h x y
  · exact prod_B12 ι h x y
  · exact prod_B20 ι h x y
  · exact prod_B21 ι h x y
  · exact prod_B22 ι h x y
  · exact prod_Bt00 ι h x y
  · exact prod_Bt01 ι h x y
  · exact prod_Bt02 ι h x y
  · exact prod_Bt10 ι h x y
  · exact prod_Bt11 ι h x y
  · exact prod_Bt12 ι h x y
  · exact prod_Bt20 ι h x y
  · exact prod_Bt21 ι h x y
  · exact prod_Bt22 ι h x y

/-- The native product of two Tits points is the Tits product (`2h = 1`). -/
theorem product_titsToNative (h : S) (h2 : (2 : S) * h = 1) (p q : Tits S) :
    coordinateProduct h (titsToNative ι h p) (titsToNative ι h q) =
      titsToNative ι h (titsProduct h p q) := by
  apply titsOfNative_injective ι h h2
  rw [titsOfNative_product, ofNative_toNative ι h h2, ofNative_toNative ι h h2, ofNative_toNative ι h h2]

theorem trace_titsToNative (h : S) (h2 : (2 : S) * h = 1) (p : Tits S) :
    coordinateTrace (titsToNative ι h p) = Matrix.trace p.1 := by
  rw [← trace_titsOfNative ι, ofNative_toNative ι h h2]

theorem pairing_titsToNative (h : S) (h2 : (2 : S) * h = 1) (p q : Tits S) :
    coordinatePairing (titsToNative ι h p) (titsToNative ι h q) =
      Matrix.trace (p.1 * q.1) + Matrix.trace (p.2.1 * q.2.2ᵀ) +
        Matrix.trace (q.2.1 * p.2.2ᵀ) := by
  rw [pairing_titsOfNative ι, ofNative_toNative ι h h2, ofNative_toNative ι h h2]

theorem titsToNative_add (h : S) (p q : Tits S) :
    titsToNative ι h (p + q) = titsToNative ι h p + titsToNative ι h q := by
  funext k
  fin_cases k <;> simp only [titsToNative, Pi.add_apply, Prod.fst_add, Prod.snd_add,
    Matrix.add_apply, Matrix.cons_val, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring

theorem titsToNative_zero (h : S) : titsToNative ι h 0 = 0 := by
  funext k
  fin_cases k <;> simp [titsToNative]

theorem titsToNative_smul (h c : S) (p : Tits S) :
    titsToNative ι h (c • p) = c • titsToNative ι h p := by
  funext k
  fin_cases k <;> simp only [titsToNative, Pi.smul_apply, Prod.smul_fst, Prod.smul_snd,
    Matrix.smul_apply, smul_eq_mul, Matrix.cons_val, Fin.isValue, Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk] <;> ring

end TitsS

#print axioms TitsS.titsOfNative_product
#print axioms TitsS.product_titsToNative
#print axioms TitsS.toNative_ofNative
#print axioms TitsS.ofNative_toNative
#print axioms TitsS.pairing_titsToNative
#print axioms TitsS.trace_titsToNative
#print axioms TitsS.titsToNative_unit
