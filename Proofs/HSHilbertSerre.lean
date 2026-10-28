/-
Selected declarations adapted from the OpenAI math project (Apache-2.0):
https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a
Original: lean/OAI/RingTheory/Multiplicity/LechHilbertSerre.lean
Declarations: Lech.hilbertSerre and IdealGraded.eventuallyPolynomial_piece/eventuallyPolynomial_length.
Changes: selected-declaration extraction, narrow imports, current module format;
any compatibility repairs are local to these selected mathematical proofs.
No individual declaration authorship is inferred. Thanks to the OpenAI math project.
License text: LICENSE.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, letter to Robert Hooke, 1676.
-/
module
public import HSEventualPolynomial
public import HSAssociatedGraded

@[expose] public section
noncomputable section
open scoped Classical BigOperators ENNReal
namespace OAI

namespace Lech
open DirectSum
universe u v w
variable (K : Type u) [Field K]

theorem hilbertSerre (n : ℕ) (S : Type v) (M : Type w)
    [CommRing S] [Algebra K S] [IsNoetherianRing S]
    [AddCommGroup M] [Module S M] [Module K M] [IsScalarTower K S M]
    [Module.Finite S M]
    (x : Fin n → S) (hx : Algebra.adjoin K (Set.range x) = ⊤)
    (G : ℕ → Submodule K M) [Decomposition G]
    [∀ i, Module.Finite K (G i)]
    (hG : ∀ j i (m : M), m ∈ G i → x j • m ∈ G (i + 1)) :
    EventuallyPolynomial (fun i => (Module.finrank K (G i) : ℚ)) := by
  induction n generalizing S M with
  | zero =>
      have hx0 : Algebra.adjoin K (∅ : Set S) = ⊤ := by simpa using hx
      let : Module.Finite K M := finite_of_no_generators hx0
      refine ⟨0, ?_⟩
      filter_upwards [Grading.eventually_eq_bot G] with i hi
      rw [hi]
      simp
  | succ n ih =>
      let fS : M →ₗ[S] M := LinearMap.lsmul S M (x 0)
      let f : M →ₗ[K] M := fS.restrictScalars K
      have hf : ∀ i, (G i).map f ≤ G (i + 1) := by
        rintro i _ ⟨m, hm, rfl⟩
        exact hG 0 i m hm
      let P : Submodule S M := fS.ker
      let Q : Submodule S M := fS.range
      let V := M ⧸ Q
      let q : M →ₗ[K] V := Q.mkQ.restrictScalars K
      let S' := S ⧸ Ideal.span {x 0}
      let x' : Fin n → S' := fun j => Ideal.Quotient.mk _ (x j.succ)
      have hx' : Algebra.adjoin K (Set.range x') = ⊤ := quotient_generators x hx
      let hPkill : Module.IsTorsionBy S P (x 0) := ker_smul_killed (M := M) (x 0)
      let hVkill : Module.IsTorsionBy S V (x 0) := coker_smul_killed (M := M) (x 0)
      let : Module S' P := hPkill.module
      let : Module S' V := hVkill.module
      have : IsScalarTower K S' P := inferInstance
      have : IsScalarTower K S' V := inferInstance
      have : IsScalarTower S S' P := inferInstance
      have : IsScalarTower S S' V := inferInstance
      have : Module.Finite S' P := Module.Finite.of_restrictScalars_finite S S' P
      have : Module.Finite S' V := Module.Finite.of_restrictScalars_finite S S' V
      let GP : ℕ → Submodule K P := fun i => (G i).comap (P.subtype.restrictScalars K)
      let GV : ℕ → Submodule K V := Grading.imagePiece G q
      have hPhom : (P.restrictScalars K).IsHomogeneous G := by
        exact Grading.ker_homogeneous G G f hf
      have hQhom : q.ker.IsHomogeneous G := by
        have hker : q.ker = f.range := by
          change (Q.mkQ.restrictScalars K).ker = f.range
          rw [LinearMap.ker_restrictScalars, Submodule.ker_mkQ]
          rfl
        rw [hker]
        exact Grading.range_homogeneous G G f hf
      let : Decomposition GP := Grading.subDecomposition G (P.restrictScalars K) hPhom
      let : Decomposition GV := Grading.imageDecomposition G q Q.mkQ_surjective hQhom
      have (i : ℕ) : Module.Finite K (GP i) := by
        exact Module.Finite.of_injective (Grading.subPieceMap G (P.restrictScalars K) i)
          (by
            intro a b h
            apply Subtype.ext
            apply Subtype.ext
            exact congrArg (fun z : G i => (z : M)) h)
      have (i : ℕ) : Module.Finite K (GV i) := by
        exact Module.Finite.of_surjective (Grading.pieceMap G q i)
          (Grading.pieceMap_surjective G q i)
      have hGP : ∀ j i (m : P), m ∈ GP i → x' j • m ∈ GP (i + 1) := by
        intro j i m hm
        change x j.succ • (m : M) ∈ G (i + 1)
        exact hG j.succ i m hm
      have hGV : ∀ j i (m : V), m ∈ GV i → x' j • m ∈ GV (i + 1) := by
        rintro j i _ ⟨m, hm, rfl⟩
        refine ⟨x j.succ • m, hG j.succ i m hm, ?_⟩
        exact Q.mkQ.map_smul _ _
      have hpolP := ih S' P x' hx' GP hGP
      have hpolV := ih S' V x' hx' GV hGV
      apply EventuallyPolynomial.of_recurrence hpolP hpolV
      intro i
      have hker : q.ker = f.range := by
        rw [LinearMap.ker_restrictScalars, Submodule.ker_mkQ]
        rfl
      have he := Grading.finrank_recurrence G f hf q hker i
      exact_mod_cast he



namespace IdealGraded

variable {A : Type*} [CommRing A]

end IdealGraded
end Lech






namespace Lech.IdealGraded
variable {R : Type*} [CommRing R] [IsNoetherianRing R]
lemma eventuallyPolynomial_piece (I : Ideal R) [I.IsMaximal] :
    Lech.EventuallyPolynomial (fun n => (Module.finrank (R ⧸ I) (Piece I n) : ℚ)) := by
  let := Ideal.Quotient.field I
  obtain ⟨n, x, hx, hxmem⟩ := exists_generators I
  have h := Lech.hilbertSerre (R ⧸ I) n (Ring I) (Ring I) x hx (grade I) (by
    intro j i m hm
    simpa only [smul_eq_mul, add_comm] using grade_mul I (hxmem j) hm)
  have he (n : ℕ) : Module.finrank (R ⧸ I) (Piece I n) =
      Module.finrank (R ⧸ I) (grade I n) := (pieceEquiv I n).finrank_eq
  simpa only [he] using h

lemma eventuallyPolynomial_length (I : Ideal R) [I.IsMaximal] :
    Lech.EventuallyPolynomial (fun n => ((Module.length R (R ⧸ I ^ n)).toNat : ℚ)) := by
  have hp := eventuallyPolynomial_piece I
  have he (N : ℕ) : ((Module.length R (R ⧸ I ^ N)).toNat : ℚ) =
      ∑ n ∈ Finset.range N, (Module.finrank (R ⧸ I) (Piece I n) : ℚ) := by
    rw [length_eq_sum]
    simp only [length_piece_eq_finrank]
    rw [← Nat.cast_sum, ENat.toNat_natCast, Nat.cast_sum]
  apply Lech.EventuallyPolynomial.of_sub_succ
  have heq : (fun N => ((Module.length R (R ⧸ I ^ (N + 1))).toNat : ℚ) -
      ((Module.length R (R ⧸ I ^ N)).toNat : ℚ)) =
      (fun N => (Module.finrank (R ⧸ I) (Piece I N) : ℚ)) := by
    funext N
    rw [he, he, Finset.sum_range_succ, add_sub_cancel_left]
  rwa [heq]
end Lech.IdealGraded

end OAI
#print axioms OAI.Lech.IdealGraded.eventuallyPolynomial_length
