module

public import BookSignedHilbert
public import BookQuadricDictionary

@[expose] public section

noncomputable section
namespace Option2.NativeStress.BookHilbertCharZero
open MvPolynomial Module
open Option2.NativeStress.BookHT
open scoped BigOperators

/-- Dictionary coordinate → the exact MONO grevlex coordinate. -/
def grevlexIndex : Fin 24 → Fin 24 :=
  ![15,7,0,12,14,3,4,19,17,20,13,16,21,10,18,23,6,8,9,5,11,22,2,1]

theorem grevlexIndex_bijective : Function.Bijective grevlexIndex := by decide +kernel

def grevlexEquiv : Fin 24 ≃ Fin 24 := Equiv.ofBijective grevlexIndex grevlexIndex_bijective

/-- Exact signed integer lift of the supplied Book dictionary. -/
def bookIntegerQuadric (s : Fin 48) : MvPolynomial (Fin 24) ℤ :=
  ∑ a : Fin 3, C (Dictionary.terms s a).2.2 * X (Dictionary.terms s a).1 * X (Dictionary.terms s a).2.1

theorem monomial_pair (a b : Fin 24) (c : ℤ) :
    monomial (Finsupp.single a 1 + Finsupp.single b 1) c = C c * X a * X b := by
  simp only [X, C_mul_monomial, monomial_mul_monomial, mul_one]

/-- Equality of the actual48 ordered polynomials, including every sign and
variable permutation. This is a ring equality, not equality after reduction. -/
theorem integer_dictionary_binding (s : Fin 48) :
    rename grevlexIndex (bookIntegerQuadric s) = integerTrinomial s := by
  fin_cases s <;>
    simp [bookIntegerQuadric, Dictionary.terms, integerTrinomial, MonoKV.tri, MonoKV.tri.triTable,
      signedCoefficient, MonoSound.vfin, grevlexIndex, Fin.sum_univ_succ,
      monomial_pair] <;> ring

#print axioms Option2.NativeStress.BookHilbertCharZero.integer_dictionary_binding
end Option2.NativeStress.BookHilbertCharZero
