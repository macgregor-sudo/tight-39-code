module

public import BookConjugationTits
public import TransportT1
public import TransportT2
public import TransportT3
public import Mathlib.Data.Matrix.Basis

@[expose] public section

/-!
Sparse root conjugation at the literal Book base, with the existing accepted
signed transports. This compatibility companion follows the legacy format of
the imported Tits/transport owners. No new transport table is supplied.
-/

set_option Elab.async false

namespace Option2.NativeStress.BookHT.TangentCoordinates

open Option2.BookNativeBase

def q12RootHidden (a b : Fin 3) (B : Matrix (Fin 3) (Fin 3) Q12) :
    Matrix (Fin 3) (Fin 3) Q12 := fun i j =>
  (if i = a then B b j else 0) - (if j = b then B i a else 0)

theorem q12RootHidden_eq (a b : Fin 3) (B : Matrix (Fin 3) (Fin 3) Q12) :
    q12RootHidden a b B = Matrix.single a b 1 * B - B * Matrix.single a b 1 := by
  apply Matrix.ext
  intro i j
  by_cases hi : i = a <;> by_cases hj : j = b
  · subst i; subst j; simp [q12RootHidden]
  · subst i; simp [q12RootHidden, hj]
  · subst j; simp [q12RootHidden, hi]
  · simp [q12RootHidden, hi, hj]

def q12RootPartner (a b : Fin 3) (Bt : Matrix (Fin 3) (Fin 3) Q12) :
    Matrix (Fin 3) (Fin 3) Q12 := -q12RootHidden b a Bt

theorem q12RootPartner_eq (a b : Fin 3) (Bt : Matrix (Fin 3) (Fin 3) Q12) :
    q12RootPartner a b Bt = -(Matrix.single a b (1 : Q12)).transpose * Bt +
      Bt * (Matrix.single a b (1 : Q12)).transpose := by
  rw [q12RootPartner, q12RootHidden_eq, Matrix.transpose_single, neg_sub,
    Matrix.neg_mul, sub_eq_add_neg, add_comm]

def q12RootCoordinates (a b : Fin 3) (x : Fin 27 → Q12) : Fin 27 → Q12 :=
  q12HiddenCoordinates (q12RootHidden a b (q12Hidden x))
    (q12RootPartner a b (q12Partner x))

theorem q12RootCoordinates_eq (a b : Fin 3) (x : Fin 27 → Q12) :
    q12RootCoordinates a b x = q12Conjugation (Matrix.single a b 1) x := by
  rw [q12RootCoordinates, q12RootHidden_eq, q12RootPartner_eq]
  rfl

def q12SheetTransport (s : Fin 4) : (Fin 27 → Q12) → Fin 27 → Q12 :=
  ![id, TitsS.sgnPerm TitsS.Transport.T1p TitsS.Transport.T1s,
    TitsS.sgnPerm TitsS.Transport.T2p TitsS.Transport.T2s,
    TitsS.sgnPerm TitsS.Transport.T3p TitsS.Transport.T3s] s

def q12SheetInverse (s : Fin 4) : (Fin 27 → Q12) → Fin 27 → Q12 :=
  ![id, TitsS.sgnPerm TitsS.Transport.T1pinv TitsS.Transport.T1si,
    TitsS.sgnPerm TitsS.Transport.T2pinv TitsS.Transport.T2si,
    TitsS.sgnPerm TitsS.Transport.T3pinv TitsS.Transport.T3si] s

def rootPair : Fin 6 → Fin 3 × Fin 3 := ![(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)]

noncomputable def q12SheetColumn (b : Fin 24) (p : Fin 39) : Fin 27 → Q12 :=
  let s := d6Sheet b
  let ab := rootPair ⟨b.val % 6, Nat.mod_lt _ (by decide)⟩
  if p.val / 3 = 0 ∨ (1 + 3 * s.val ≤ p.val / 3 ∧ p.val / 3 ≤ 3 + 3 * s.val) then 0 else
    q12SheetTransport s
      (q12RootCoordinates ab.1 ab.2 (q12SheetInverse s (bookPointQ12 p)))

end Option2.NativeStress.BookHT.TangentCoordinates

#check Option2.NativeStress.BookHT.TangentCoordinates.q12RootCoordinates_eq
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.q12RootCoordinates_eq
