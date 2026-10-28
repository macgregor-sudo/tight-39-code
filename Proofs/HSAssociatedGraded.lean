/-
Selected declarations adapted from the OpenAI math project (Apache-2.0):
https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a
Original: lean/OAI/RingTheory/Multiplicity/LechBoundedEquiv.lean; IdealGradedRing.lean
Declarations: Lech.IdealGraded nextPower/Piece, length telescoping, Rees grading, quotient grade and degree-one generators.
Changes: selected-declaration extraction, narrow imports, current module format;
any compatibility repairs are local to these selected mathematical proofs.
No individual declaration authorship is inferred. Thanks to the OpenAI math project.
License text: LICENSE.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, letter to Robert Hooke, 1676.
-/
module
public import HSGrading
public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.RingTheory.Length

@[expose] public section
noncomputable section
open scoped Classical BigOperators ENNReal
namespace OAI

namespace Lech
namespace IdealGraded

variable {A : Type*} [CommRing A]

def nextPower (I : Ideal A) (n : ℕ) : Submodule A ↥(I ^ n) :=
  Submodule.comap (I ^ n).subtype (I ^ (n + 1))

abbrev Piece (I : Ideal A) (n : ℕ) := ↥(I ^ n) ⧸ nextPower I n

lemma pow_succ_le (I : Ideal A) (n : ℕ) : I ^ (n + 1) ≤ I ^ n := by
  exact Ideal.pow_le_pow_right (Nat.le_succ n)

lemma torsion_piece (I : Ideal A) (n : ℕ) :
    Module.IsTorsionBySet A (Piece I n) I := by
  rw [Module.isTorsionBySet_quotient_iff]
  intro x a ha
  change a * (x : A) ∈ I ^ (n + 1)
  rw [pow_succ']
  exact Ideal.mul_mem_mul ha x.property

noncomputable instance pieceModule (I : Ideal A) (n : ℕ) :
    Module (A ⧸ I) (Piece I n) := (torsion_piece I n).module

instance pieceTower (I : Ideal A) (n : ℕ) :
    IsScalarTower A (A ⧸ I) (Piece I n) :=
  (torsion_piece I n).isScalarTower

def inclusion (I : Ideal A) (n : ℕ) : Piece I n →ₗ[A] A ⧸ I ^ (n + 1) :=
  (nextPower I n).liftQ (((I ^ (n + 1)).mkQ).comp (I ^ n).subtype) (by
    intro x hx
    simpa only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.subtype_apply, nextPower, Submodule.mem_comap] using hx)

lemma inclusion_injective (I : Ideal A) (n : ℕ) :
    Function.Injective (inclusion I n) := by
  rw [← LinearMap.ker_eq_bot, inclusion, Submodule.ker_liftQ_eq_bot]
  simpa only [LinearMap.ker_comp, Submodule.ker_mkQ, nextPower] using (le_refl (nextPower I n))

def transition (I : Ideal A) (n : ℕ) :
    (A ⧸ I ^ (n + 1)) →ₗ[A] (A ⧸ I ^ n) :=
  (I ^ (n + 1)).mapQ (I ^ n) LinearMap.id (pow_succ_le I n)

lemma transition_surjective (I : Ideal A) (n : ℕ) :
    Function.Surjective (transition I n) := by
  intro x
  obtain ⟨a, rfl⟩ := (I ^ n).mkQ_surjective x
  exact ⟨(I ^ (n + 1)).mkQ a, rfl⟩

lemma piece_exact (I : Ideal A) (n : ℕ) :
    Function.Exact (inclusion I n) (transition I n) := by
  rw [LinearMap.exact_iff]
  simp only [inclusion, transition, Submodule.ker_mapQ, Submodule.range_liftQ,
    LinearMap.range_comp, Submodule.range_subtype, Submodule.comap_id]

lemma length_successor (I : Ideal A) (n : ℕ) :
    Module.length A (A ⧸ I ^ (n + 1)) =
      Module.length A (Piece I n) + Module.length A (A ⧸ I ^ n) :=
  Module.length_eq_add_of_exact (inclusion I n) (transition I n)
    (inclusion_injective I n) (transition_surjective I n) (piece_exact I n)

lemma length_eq_sum (I : Ideal A) (N : ℕ) :
    Module.length A (A ⧸ I ^ N) =
      ∑ n ∈ Finset.range N, Module.length A (Piece I n) := by
  induction N with
  | zero => simp
  | succ N ih => rw [length_successor, ih, Finset.sum_range_succ, add_comm]

instance pieceFinite [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    Module.Finite (A ⧸ I) (Piece I n) :=
  Module.Finite.of_restrictScalars_finite A (A ⧸ I) (Piece I n)

lemma length_piece_eq_finrank [IsNoetherianRing A] (I : Ideal A) [I.IsMaximal] (n : ℕ) :
    Module.length A (Piece I n) = (Module.finrank (A ⧸ I) (Piece I n) : ℕ∞) := by
  let := Ideal.Quotient.field I
  rw [Module.length_eq_of_surjective (R := A ⧸ I)
    (by simpa only [Ideal.Quotient.algebraMap_eq] using Ideal.Quotient.mk_surjective),
    Module.length_eq_finrank]

end IdealGraded
end Lech


namespace Lech.IdealGraded
open Polynomial DirectSum
open scoped Classical
variable {R : Type*} [CommRing R] (I : Ideal R)

def monomial (i : ℕ) : ↥(I ^ i) →ₗ[R] reesAlgebra I :=
  ((Polynomial.monomial i).comp (I ^ i).subtype).codRestrict (reesAlgebra I).toSubmodule
    (fun x => reesAlgebra.monomial_mem.mpr x.property)

@[simp] lemma monomial_coe (i : ℕ) (x : ↥(I ^ i)) :
    (monomial I i x : R[X]) = Polynomial.monomial i (x : R) := rfl

def coefficient (i : ℕ) : reesAlgebra I →ₗ[R] ↥(I ^ i) :=
  ((Polynomial.lcoeff R i).comp (reesAlgebra I).val.toLinearMap).codRestrict _
    (fun p => p.property i)

@[simp] lemma coefficient_coe (i : ℕ) (p : reesAlgebra I) :
    (coefficient I i p : R) = (p : R[X]).coeff i := rfl

@[simp] lemma coefficient_monomial (i : ℕ) (x : ↥(I ^ i)) :
    coefficient I i (monomial I i x) = x := by
  apply Subtype.ext
  change (Polynomial.monomial i (x : R)).coeff i = (x : R)
  simp

lemma monomial_injective (i : ℕ) : Function.Injective (monomial I i) :=
  Function.LeftInverse.injective (coefficient_monomial I i)

abbrev reesGrade (i : ℕ) : Submodule R (reesAlgebra I) := (monomial I i).range

def component (i : ℕ) : reesAlgebra I →ₗ[R] reesGrade I i :=
  (monomial I i).rangeRestrict.comp (coefficient I i)

@[simp] lemma component_coe (i : ℕ) (p : reesAlgebra I) :
    ((component I i p : reesAlgebra I) : R[X]) = Polynomial.monomial i ((p : R[X]).coeff i) := rfl

noncomputable def reesDecompose : reesAlgebra I →ₗ[R] ⨁ i, reesGrade I i where
  toFun p :=
    { toFun := fun i => component I i p
      support' := by
        classical
        exact Trunc.mk ⟨(p : R[X]).support.val, fun i => by
          by_cases hi : i ∈ (p : R[X]).support
          · exact Or.inl hi
          · apply Or.inr
            apply Subtype.ext
            apply Subtype.ext
            simp [component_coe, Polynomial.notMem_support_iff.mp hi]⟩ }
  map_add' p q := by apply DFinsupp.ext; intro i; exact (component I i).map_add p q
  map_smul' a p := by apply DFinsupp.ext; intro i; exact (component I i).map_smul a p

@[simp] lemma reesDecompose_apply (p : reesAlgebra I) (i : ℕ) :
    reesDecompose I p i = component I i p := rfl

lemma reesDecompose_support (p : reesAlgebra I) :
    (reesDecompose I p).support = (p : R[X]).support := by
  classical
  ext i
  simp only [DFinsupp.mem_support_iff, Polynomial.mem_support_iff, reesDecompose_apply]
  have he : component I i p = 0 ↔ (p : R[X]).coeff i = 0 := by
    rw [← Subtype.val_inj, ← Subtype.val_inj]
    simp only [component_coe, ZeroMemClass.coe_zero, Polynomial.monomial_eq_zero_iff]
  exact not_congr he

lemma reesDecompose_monomial (i : ℕ) (x : ↥(I ^ i)) :
    reesDecompose I (monomial I i x) =
      DirectSum.lof R ℕ (fun i => ↥(reesGrade I i)) i ((monomial I i).rangeRestrict x) := by
  rw [DirectSum.lof_eq_of]
  apply DFinsupp.ext
  intro j
  apply Subtype.ext
  apply Subtype.ext
  by_cases hij : i = j
  · subst j
    simp [component_coe]
  · simp [component_coe, Polynomial.coeff_monomial, hij,
      DirectSum.of_eq_of_ne _ _ _ (Ne.symm hij)]

noncomputable instance reesDecomposition : Decomposition (reesGrade I) :=
  Decomposition.ofLinearMap _ (reesDecompose I)
    (by
      classical
      apply LinearMap.ext
      intro p
      apply Subtype.ext
      rw [LinearMap.comp_apply, DirectSum.coeLinearMap_eq_dfinsuppSum]
      change (∑ i ∈ (reesDecompose I p).support,
        (reesDecompose I p i : reesAlgebra I) : reesAlgebra I).val = (p : R[X])
      rw [reesDecompose_support]
      change (reesAlgebra I).val (∑ i ∈ (p : R[X]).support,
        (reesDecompose I p i : reesAlgebra I)) = (p : R[X])
      rw [map_sum]
      simp only [reesDecompose_apply]
      exact (Polynomial.as_sum_support p.val).symm)
    (by
      apply DirectSum.linearMap_ext
      intro i
      apply LinearMap.ext
      rintro ⟨p, x, rfl⟩
      simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, LinearMap.id_apply]
      change reesDecompose I (monomial I i x) = _
      convert reesDecompose_monomial I i x using 1
      rfl)

@[simp] lemma rees_decompose_val (p : reesAlgebra I) (i : ℕ) :
    ((decompose (reesGrade I) p i : reesAlgebra I) : R[X]) =
      Polynomial.monomial i (p.val.coeff i) := rfl

 
def shifted : Ideal (reesAlgebra I) where
  carrier := {p | ∀ i, (p : R[X]).coeff i ∈ I ^ (i + 1)}
  zero_mem' i := by simp
  add_mem' hp hq i := by simpa using (I ^ (i + 1)).add_mem (hp i) (hq i)
  smul_mem' p q hq i := by
    change ((p : R[X]) * (q : R[X])).coeff i ∈ _
    rw [Polynomial.coeff_mul]
    apply Ideal.sum_mem
    rintro ⟨j, k⟩ hjk
    have hi : j + k = i := Finset.HasAntidiagonal.mem_antidiagonal.mp hjk
    have hh := Ideal.mul_mem_mul (p.property j) (hq k)
    rw [← pow_add] at hh
    simpa only [← hi, Nat.add_assoc] using hh

lemma shifted_homogeneous : SetLike.IsHomogeneous (reesGrade I) (shifted I) := by
  intro i p hp j
  change (Polynomial.monomial i (p.val.coeff i)).coeff j ∈ I ^ (j + 1)
  by_cases hij : i = j
  · subst j
    simpa using hp i
  · simp [Polynomial.coeff_monomial, hij]

end Lech.IdealGraded
namespace Lech.IdealGraded
open Polynomial DirectSum
variable {R : Type*} [CommRing R] (I : Ideal R)

abbrev Ring := reesAlgebra I ⧸ shifted I

lemma scalar_mem_shifted {r : R} (hr : r ∈ I) :
    algebraMap R (reesAlgebra I) r ∈ shifted I := by
  intro i
  change (Polynomial.C r).coeff i ∈ I ^ (i + 1)
  by_cases hi : i = 0
  · subst i; simpa using hr
  · simp [Polynomial.coeff_C, hi]

noncomputable instance gradedAlgebra : Algebra (R ⧸ I) (Ring I) :=
  Ideal.Quotient.algebraQuotientOfLEComap (fun _ hr => scalar_mem_shifted I hr)

instance gradedTower : IsScalarTower R (R ⧸ I) (Ring I) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

abbrev quotientR : reesAlgebra I →ₗ[R] Ring I := (shifted I).mkQ.restrictScalars R

lemma quotientR_ker_homogeneous : (quotientR I).ker.IsHomogeneous (reesGrade I) := by
  rw [LinearMap.ker_restrictScalars, Submodule.ker_mkQ]
  exact shifted_homogeneous I

noncomputable instance imageGrading : Decomposition (Grading.imagePiece (reesGrade I) (quotientR I)) :=
  Grading.imageDecomposition (reesGrade I) (quotientR I)
    (shifted I).mkQ_surjective (quotientR_ker_homogeneous I)

def grade (i : ℕ) : Submodule (R ⧸ I) (Ring I) where
  toAddSubmonoid := (Grading.imagePiece (reesGrade I) (quotientR I) i).toAddSubmonoid
  smul_mem' a x hx := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    change r • x ∈ _
    exact (Grading.imagePiece (reesGrade I) (quotientR I) i).smul_mem r hx

noncomputable instance gradeDecomposition : Decomposition (grade I) where
  decompose' := decompose (Grading.imagePiece (reesGrade I) (quotientR I))
  left_inv := (decompose (Grading.imagePiece (reesGrade I) (quotientR I))).left_inv
  right_inv := (decompose (Grading.imagePiece (reesGrade I) (quotientR I))).right_inv

lemma monomial_mem_shifted_iff (i : ℕ) (x : ↥(I ^ i)) :
    monomial I i x ∈ shifted I ↔ (x : R) ∈ I ^ (i + 1) := by
  constructor
  · intro hx
    have h := hx i
    simpa using h
  · intro hx j
    change (Polynomial.monomial i (x : R)).coeff j ∈ I ^ (j + 1)
    by_cases hij : i = j
    · subst j; simpa using hx
    · simp [Polynomial.coeff_monomial, hij]

def toRingR (i : ℕ) : Piece I i →ₗ[R] Ring I :=
  (nextPower I i).liftQ ((quotientR I).comp (monomial I i)) (by
    intro x hx
    change Ideal.Quotient.mk (shifted I) (monomial I i x) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((monomial_mem_shifted_iff I i x).mpr hx))

lemma toRingR_injective (i : ℕ) : Function.Injective (toRingR I i) := by
  rw [← LinearMap.ker_eq_bot, toRingR, Submodule.ker_liftQ_eq_bot]
  intro x hx
  change (x : R) ∈ I ^ (i + 1)
  apply (monomial_mem_shifted_iff I i x).mp
  exact Ideal.Quotient.eq_zero_iff_mem.mp hx

lemma toRingR_mem (i : ℕ) (x : Piece I i) : toRingR I i x ∈ grade I i := by
  obtain ⟨x, rfl⟩ := (nextPower I i).mkQ_surjective x
  exact ⟨monomial I i x, ⟨x, rfl⟩, rfl⟩

def toPiece (i : ℕ) : Piece I i →ₗ[R ⧸ I] grade I i where
  toFun x := ⟨toRingR I i x, toRingR_mem I i x⟩
  map_add' x y := Subtype.ext ((toRingR I i).map_add x y)
  map_smul' a x := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    apply Subtype.ext
    change toRingR I i (r • x) = r • toRingR I i x
    exact (toRingR I i).map_smul r x

lemma toPiece_bijective (i : ℕ) : Function.Bijective (toPiece I i) := by
  constructor
  · intro x y h
    apply toRingR_injective I i
    exact congrArg Subtype.val h
  · rintro ⟨_, p, ⟨x, rfl⟩, rfl⟩
    exact ⟨(nextPower I i).mkQ x, rfl⟩

noncomputable def pieceEquiv (i : ℕ) : Piece I i ≃ₗ[R ⧸ I] grade I i :=
  LinearEquiv.ofBijective (toPiece I i) (toPiece_bijective I i)

instance gradeFinite [IsNoetherianRing R] (i : ℕ) : Module.Finite (R ⧸ I) (grade I i) :=
  Module.Finite.of_surjective (toPiece I i) (toPiece_bijective I i).2

lemma grade_mul {i j : ℕ} {x y : Ring I} (hx : x ∈ grade I i) (hy : y ∈ grade I j) :
    x * y ∈ grade I (i + j) := by
  obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := hx
  obtain ⟨_, ⟨b, rfl⟩, rfl⟩ := hy
  let c : ↥(I ^ (i + j)) := ⟨(a : R) * (b : R), by
    rw [pow_add]; exact Ideal.mul_mem_mul a.property b.property⟩
  refine ⟨monomial I (i + j) c, ⟨c, rfl⟩, ?_⟩
  change Ideal.Quotient.mk (shifted I) (monomial I (i + j) c) =
    Ideal.Quotient.mk (shifted I) (monomial I i a) *
      Ideal.Quotient.mk (shifted I) (monomial I j b)
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  exact (Polynomial.monomial_mul_monomial _ _ _ _).symm

lemma exists_generators [IsNoetherianRing R] :
    ∃ (n : ℕ) (x : Fin n → Ring I),
      Algebra.adjoin (R ⧸ I) (Set.range x) = ⊤ ∧ ∀ j, x j ∈ grade I 1 := by
  obtain ⟨n, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian I)
  have hamem (j : Fin n) : a j ∈ I ^ 1 := by
    rw [pow_one, ← ha]
    exact Submodule.subset_span (Set.mem_range_self j)
  let u : Fin n → reesAlgebra I := fun j => monomial I 1 ⟨a j, hamem j⟩
  have hupoly : Algebra.adjoin R (Set.range (fun j => Polynomial.monomial 1 (a j))) =
      reesAlgebra I := by
    rw [← adjoin_monomial_eq_reesAlgebra, ← ha, Submodule.map_span, Algebra.adjoin_span,
      ← Set.range_comp]
    rfl
  have hu : Algebra.adjoin R (Set.range u) = ⊤ := by
    apply Subalgebra.map_injective (f := (reesAlgebra I).val) Subtype.val_injective
    rw [AlgHom.map_adjoin, Algebra.map_top, ← Set.range_comp]
    change Algebra.adjoin R (Set.range (fun j => Polynomial.monomial 1 (a j))) = _
    rw [hupoly]
    exact (Subalgebra.range_val _).symm
  let q := Ideal.Quotient.mkₐ R (shifted I)
  let x : Fin n → Ring I := fun j => q (u j)
  have hxR : Algebra.adjoin R (Set.range x) = ⊤ := by
    have h := congrArg (Subalgebra.map q) hu
    rw [AlgHom.map_adjoin, ← Set.range_comp, Algebra.map_top,
      (AlgHom.range_eq_top q).mpr Ideal.Quotient.mk_surjective] at h
    exact h
  have hx : Algebra.adjoin (R ⧸ I) (Set.range x) = ⊤ := by
    apply Subalgebra.restrictScalars_injective R
    rw [Algebra.Subalgebra.restrictScalars_adjoin, hxR, sup_top_eq, Subalgebra.restrictScalars_top]
  refine ⟨n, x, hx, ?_⟩
  intro j
  exact ⟨u j, ⟨⟨a j, hamem j⟩, rfl⟩, rfl⟩

end Lech.IdealGraded
end OAI
#print axioms OAI.Lech.IdealGraded.length_eq_sum
#print axioms OAI.Lech.IdealGraded.exists_generators
