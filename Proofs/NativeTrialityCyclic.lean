module

public import NativeTrialityRestriction

/-!
# The cyclic Peirce-slot convention

With `K` octonion conjugation, the cyclic slot coordinates of `x` are
`(x₁, x₂, x₃) = (o12, K o02, o01)` (MASTER §6.6). A related triple `(A, B, C)` acts on them, through its
extension, by `(B, K C K, A)`. Consequently the cyclic seed of `T_u = (L_u, R_u, L_u + R_u)` is
`(R_u, -L_u - R_u, L_u)`, and the first cyclic Peirce space `E₂₃` (entry `o12`) carries the **second**
projection of the related triple.
-/

@[expose] public section

noncomputable section

namespace CKM.NativeDerivationTriality

open Glennie Reuse

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Cyclic slot coordinates `(x₁, x₂, x₃) = (o12, K o02, o01)`. -/
def cyclicSlots (x : Albert) : Octonion × Octonion × Octonion := (x.o12, octConj x.o02, x.o01)

/-- The cyclic action `(B, K C K, A)` of a triple `(A, B, C)`. -/
def cyclicAction (t : EndTriple) : EndTriple := (t.2.1, octConjLinear * t.2.2 * octConjLinear, t.1)

theorem cyclicSlots_extendTriple (t : EndTriple) (x : Albert) :
    cyclicSlots (extendTriple t x) =
      ((cyclicAction t).1 (cyclicSlots x).1, (cyclicAction t).2.1 (cyclicSlots x).2.1,
        (cyclicAction t).2.2 (cyclicSlots x).2.2) := by
  simp only [cyclicSlots, cyclicAction, extendTriple_apply, Module.End.mul_apply, octConjLinear_apply,
    octConj_conj]

/-- Conjugating right multiplication by an imaginary octonion: `K R_u K = -L_u`. -/
theorem cyc_conj_rightMul_conj {u : Octonion} (hu : octRe u = 0) :
    octConjLinear * rightMul u * octConjLinear = -leftMul u := by
  apply LinearMap.ext
  intro x
  have h0 := congrArg (fun T : Module.End ℝ Octonion => T (octConj x)) (conj_leftMul_conj hu)
  simp only [Module.End.mul_apply, octConjLinear_apply, octConj_conj, LinearMap.neg_apply,
    leftMul_apply, rightMul_apply] at h0
  have h1 : octMul (octConj x) u = -octConj (octMul u x) := by rw [h0, neg_neg]
  have hn : octConj (-octConj (octMul u x)) = -octConj (octConj (octMul u x)) :=
    map_neg octConjLinear _
  simp only [Module.End.mul_apply, octConjLinear_apply, LinearMap.neg_apply, leftMul_apply,
    rightMul_apply]
  rw [h1, hn, octConj_conj]

/-- The cyclic seed: `(B, K C K, A)` of `(L_u, R_u, L_u + R_u)` is `(R_u, -L_u - R_u, L_u)`. -/
theorem cyclicAction_seedTriple {u : Octonion} (hu : octRe u = 0) :
    cyclicAction (seedTriple u) = (rightMul u, -leftMul u - rightMul u, leftMul u) := by
  simp only [cyclicAction, seedTriple]
  rw [mul_add, add_mul, conj_leftMul_conj hu, cyc_conj_rightMul_conj hu]
  simp only [Prod.mk.injEq, true_and, and_true]
  abel

/-- The first cyclic Peirce slot `E₂₃` is acted on by the second projection of the restricted
related triple. -/
theorem firstCyclicSlot_eq_secondProj (D : diagonalFixer) (x : Albert) :
    (cyclicSlots ((D : Module.End ℝ Albert) x)).1 =
      (secondProjEquiv (peirceRestrictionEquiv D) : Module.End ℝ Octonion) (cyclicSlots x).1 := by
  rw [secondProjEquiv_apply, secondProj_apply, peirceRestrictionEquiv_apply]
  exact (congrArg (fun E : Module.End ℝ Albert => (E x).o12) (extendTriple_restrictTriple D.2)).symm

end CKM.NativeDerivationTriality

#print axioms CKM.NativeDerivationTriality.cyclicSlots_extendTriple
#print axioms CKM.NativeDerivationTriality.cyclicAction_seedTriple
#print axioms CKM.NativeDerivationTriality.firstCyclicSlot_eq_secondProj
