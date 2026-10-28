/-
Selected declarations adapted from the OpenAI math project (Apache-2.0):
https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a
Original: lean/OAI/RingTheory/Multiplicity/LechBoundedEquiv.lean; SeparableOrderNormalizedLength.lean
Declarations: Lech.Grading image/sub decompositions and finite-rank recurrence; quotient_generators, finite_of_no_generators and torsion helpers.
Changes: selected-declaration extraction, narrow imports, current module format;
any compatibility repairs are local to these selected mathematical proofs.
No individual declaration authorship is inferred. Thanks to the OpenAI math project.
License text: LICENSE.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, letter to Robert Hooke, 1676.
-/
module
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Tactic

@[expose] public section
noncomputable section
open scoped Classical BigOperators ENNReal
namespace OAI

namespace Lech.Grading
open DirectSum
variable {R M N ι : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] [DecidableEq ι]
variable (G : ι → Submodule R M) [Decomposition G]
variable (f : M →ₗ[R] N)

def imagePiece (i : ι) : Submodule R N := (G i).map f

def pieceMap (i : ι) : G i →ₗ[R] imagePiece G f i :=
  (f.comp (G i).subtype).codRestrict _ (fun x => Submodule.mem_map_of_mem x.property)

omit [DecidableEq ι] [Decomposition G] in
@[simp] lemma pieceMap_coe (i : ι) (x : G i) :
    (pieceMap G f i x : N) = f (x : M) := rfl

def beforeQuotient : M →ₗ[R] ⨁ i, imagePiece G f i :=
  (DirectSum.lmap (pieceMap G f)).comp (decomposeLinearEquiv G).toLinearMap

@[simp] lemma beforeQuotient_piece (i : ι) (x : G i) :
    beforeQuotient G f x = DirectSum.lof R ι (fun i => ↥(imagePiece G f i)) i (pieceMap G f i x) := by
  simp [beforeQuotient]

lemma kernel_le_beforeQuotient (hf : f.ker.IsHomogeneous G) :
    f.ker ≤ (beforeQuotient G f).ker := by
  intro x hx
  apply DFinsupp.ext
  intro i
  apply Subtype.ext
  change f (decompose G x i : M) = 0
  exact hf i hx

noncomputable def imageDecompose (hs : Function.Surjective f)
    (hf : f.ker.IsHomogeneous G) : N →ₗ[R] ⨁ i, imagePiece G f i :=
  ((f.ker).liftQ (beforeQuotient G f) (kernel_le_beforeQuotient G f hf)).comp
    (f.quotKerEquivOfSurjective hs).symm.toLinearMap

@[simp] lemma imageDecompose_map (hs : Function.Surjective f)
    (hf : f.ker.IsHomogeneous G) (x : M) :
    imageDecompose G f hs hf (f x) = beforeQuotient G f x := by
  simp only [imageDecompose, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

lemma recompose_beforeQuotient :
    (DirectSum.coeLinearMap (imagePiece G f)).comp (beforeQuotient G f) = f := by
  apply DirectSum.decompose_lhom_ext G
  intro i
  ext x
  simp [beforeQuotient_piece]

@[instance_reducible]
noncomputable def imageDecomposition (hs : Function.Surjective f)
    (hf : f.ker.IsHomogeneous G) : Decomposition (imagePiece G f) :=
  Decomposition.ofLinearMap (imagePiece G f) (imageDecompose G f hs hf)
    (by
      ext y
      obtain ⟨x, rfl⟩ := hs y
      simpa only [LinearMap.comp_apply, LinearMap.id_apply, imageDecompose_map] using
        DFunLike.congr_fun (recompose_beforeQuotient G f) x)
    (by
      apply DirectSum.linearMap_ext
      intro i
      apply LinearMap.ext
      intro x
      obtain ⟨a, ha, he⟩ := x.property
      have hx : x = pieceMap G f i ⟨a, ha⟩ := Subtype.ext he.symm
      rw [hx]
      simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof,
        LinearMap.id_apply, pieceMap_coe, imageDecompose_map]
      exact beforeQuotient_piece G f i ⟨a, ha⟩)

variable (P : Submodule R M)

def subPiece (i : ι) : Submodule R P := Submodule.comap P.subtype (G i)

def subPieceMap (i : ι) : subPiece G P i →ₗ[R] G i :=
  { toFun := fun x => ⟨x.val.val, x.property⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

def subDecompose (hP : P.IsHomogeneous G) : P →ₗ[R] ⨁ i, subPiece G P i where
  toFun x :=
    { toFun := fun i => ⟨⟨decompose G x i, hP i x.property⟩, (decompose G x i).property⟩
      support' := (decompose G x).support'.map fun s =>
        ⟨s.val, fun i => (s.property i).imp id (fun hz => by
          apply Subtype.ext
          apply Subtype.ext
          change (decompose G x i : M) = 0
          exact congrArg (fun y : G i => (y : M)) hz)⟩ }
  map_add' x y := by
    apply DFinsupp.ext
    intro i
    apply Subtype.ext
    apply Subtype.ext
    change (decompose G ((x : M) + (y : M)) i : M) =
      (decompose G x i : M) + (decompose G y i : M)
    exact congrArg (fun z : G i => (z : M)) (DFunLike.congr_fun (map_add (decomposeAddEquiv G) (x : M) (y : M)) i)
  map_smul' a x := by
    apply DFinsupp.ext
    intro i
    apply Subtype.ext
    apply Subtype.ext
    change (decompose G (a • (x : M)) i : M) = a • (decompose G x i : M)
    exact congrArg (fun z : G i => (z : M)) (DFunLike.congr_fun (decompose_smul G a x) i)

@[simp] lemma subDecompose_lmap (hP : P.IsHomogeneous G) (x : P) :
    DirectSum.lmap (subPieceMap G P) (subDecompose G P hP x) = decompose G x := by
  apply DFinsupp.ext
  intro i
  rfl

omit [Decomposition G] in
lemma sub_lmap_recompose :
    P.subtype.comp (DirectSum.coeLinearMap (subPiece G P)) =
      (DirectSum.coeLinearMap G).comp (DirectSum.lmap (subPieceMap G P)) := by
  apply DirectSum.linearMap_ext
  intro i
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, DirectSum.lmap_lof]
  rfl

@[instance_reducible]
noncomputable def subDecomposition (hP : P.IsHomogeneous G) :
    Decomposition (subPiece G P) :=
  Decomposition.ofLinearMap (subPiece G P) (subDecompose G P hP)
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      have h := DFunLike.congr_fun (sub_lmap_recompose G P) (subDecompose G P hP x)
      simp only [LinearMap.comp_apply, subDecompose_lmap] at h
      exact h.trans ((decompose G).symm_apply_apply x))
    (by
      apply DirectSum.linearMap_ext
      intro i
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, LinearMap.id_apply]
      apply DFinsupp.ext
      intro j
      apply Subtype.ext
      apply Subtype.ext
      change (decompose G (x.val : M) j : M) = ((DirectSum.of (fun i => ↥(subPiece G P i)) i x) j : M)
      have hx : ((x : P) : M) ∈ G i := x.property
      rw [decompose_of_mem G hx]
      by_cases hij : i = j
      · subst j
        simp
      · simp [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hij)])


end Lech.Grading
namespace Lech.Grading
open DirectSum
variable {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N]
variable (G : ℕ → Submodule R M) (H : ℕ → Submodule R N)
  [Decomposition G] [Decomposition H]

def projection (i : ℕ) : M →ₗ[R] M :=
  (G i).subtype.comp ((DirectSum.component R ℕ (fun i => ↥(G i)) i).comp
    (decomposeLinearEquiv G).toLinearMap)

@[simp] lemma projection_apply (i : ℕ) (x : M) :
    projection G i x = (decompose G x i : M) := rfl

lemma proj_of_mem {i j : ℕ} {x : M} (hx : x ∈ G i) :
    projection G j x = if i = j then x else 0 := by
  by_cases hij : i = j
  · subst j
    simp [DirectSum.decompose_of_mem_same G hx]
  · simp [hij, DirectSum.decompose_of_mem_ne G hx hij]

variable (f : M →ₗ[R] N)
variable (hf : ∀ i, (G i).map f ≤ H (i + 1))
include hf

lemma projection_succ_comp (i : ℕ) :
    (projection H (i + 1)).comp f = f.comp (projection G i) := by
  apply DirectSum.decompose_lhom_ext G
  intro j
  apply LinearMap.ext
  intro x
  have hfx : f (x : M) ∈ H (j + 1) := hf j (Submodule.mem_map_of_mem x.property)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply]
  rw [proj_of_mem H hfx, proj_of_mem G x.property]
  by_cases hi : j = i <;> simp [hi]

lemma projection_zero_comp : (projection H 0).comp f = 0 := by
  apply DirectSum.decompose_lhom_ext G
  intro j
  apply LinearMap.ext
  intro x
  have hfx : f (x : M) ∈ H (j + 1) := hf j (Submodule.mem_map_of_mem x.property)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply]
  rw [proj_of_mem H hfx]
  simp

lemma ker_homogeneous : f.ker.IsHomogeneous G := by
  intro i x hx
  change f (projection G i x) = 0
  rw [← LinearMap.comp_apply, ← projection_succ_comp G H f hf,
    LinearMap.comp_apply, LinearMap.mem_ker.mp hx, map_zero]

lemma range_homogeneous : f.range.IsHomogeneous H := by
  intro i y hy
  obtain ⟨x, rfl⟩ := hy
  cases i with
  | zero =>
      have h := DFunLike.congr_fun (projection_zero_comp G H f hf) x
      change projection H 0 (f x) ∈ f.range
      rw [show projection H 0 (f x) = 0 from h]
      exact f.range.zero_mem
  | succ i =>
      refine ⟨projection G i x, ?_⟩
      exact (DFunLike.congr_fun (projection_succ_comp G H f hf i) x).symm

def step (i : ℕ) : G i →ₗ[R] H (i + 1) :=
  (f.comp (G i).subtype).codRestrict _ fun x =>
    hf i (Submodule.mem_map_of_mem x.property)

omit [Decomposition G] [Decomposition H] in
@[simp] lemma step_apply (i : ℕ) (x : G i) :
    (step G H f hf i x : N) = f (x : M) := rfl

omit [Decomposition G] [Decomposition H] in
lemma step_ker (i : ℕ) : (step G H f hf i).ker = f.ker.comap (G i).subtype := by
  ext x
  simp [LinearMap.mem_ker, Subtype.ext_iff]

lemma step_range (i : ℕ) :
    (step G H f hf i).range = f.range.comap (H (i + 1)).subtype := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, hx⟩
    change f x = (y : N) at hx
    refine ⟨decompose G x i, ?_⟩
    apply Subtype.ext
    change f (projection G i x) = (y : N)
    have he := DFunLike.congr_fun (projection_succ_comp G H f hf i) x
    rw [LinearMap.comp_apply, hx, proj_of_mem H y.property, ite_eq_left rfl] at he
    exact he.symm

end Lech.Grading


namespace Lech.Grading
open DirectSum Filter
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
variable (G : ℕ → Submodule K M) [Decomposition G]

lemma eventually_eq_bot [Module.Finite K M] : ∀ᶠ n in atTop, G n = ⊥ := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := K) (M := M)
  let t := s.biUnion (fun x => (decompose G x).support)
  refine Filter.eventually_atTop.mpr ⟨t.sup id + 1, fun n hn => ?_⟩
  have hp : projection G n = 0 := by
    apply (Submodule.linearMap_eq_zero_iff_of_span_eq_top _ hs).mpr
    intro x
    have hnot : n ∉ (decompose G x.val).support := by
      intro hx
      have hnt : n ∈ t := Finset.mem_biUnion.mpr ⟨x.val, x.property, hx⟩
      have ht := Finset.le_sup (f := id) hnt
      dsimp at ht
      omega
    have hz : decompose G x.val n = 0 := DFinsupp.notMem_support_iff.mp hnot
    exact congrArg (fun z : G n => (z : M)) hz
  apply eq_bot_iff.mpr
  intro x hx
  rw [Submodule.mem_bot]
  have he := DFunLike.congr_fun hp x
  simpa [proj_of_mem G hx] using he

omit [Decomposition G] in
lemma subPiece_finrank (P : Submodule K M) (i : ℕ) :
    Module.finrank K (subPiece G P i) = Module.finrank K (P.comap (G i).subtype) := by
  let e : subPiece G P i ≃ₗ[K] P.comap (G i).subtype :=
    { toFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      invFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact e.finrank_eq

variable {N : Type*} [AddCommGroup N] [Module K N]
omit [Decomposition G] in
lemma pieceMap_surjective (q : M →ₗ[K] N) (i : ℕ) :
    Function.Surjective (pieceMap G q i) := by
  rintro ⟨y, x, hx, hxy⟩
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

omit [Decomposition G] in
lemma pieceMap_ker (q : M →ₗ[K] N) (i : ℕ) :
    (pieceMap G q i).ker = q.ker.comap (G i).subtype := by
  ext x
  simp [LinearMap.mem_ker, Subtype.ext_iff]

lemma finrank_recurrence [∀ i, Module.Finite K (G i)]
    (f : M →ₗ[K] M) (hf : ∀ i, (G i).map f ≤ G (i + 1))
    (q : M →ₗ[K] N) (hq : q.ker = f.range) (i : ℕ) :
    Module.finrank K (G (i + 1)) + Module.finrank K (subPiece G f.ker i) =
      Module.finrank K (G i) + Module.finrank K (imagePiece G q (i + 1)) := by
  have h1 := (step G G f hf i).finrank_range_add_finrank_ker
  have h2 := (pieceMap G q (i + 1)).finrank_range_add_finrank_ker
  have he : Module.finrank K (pieceMap G q (i + 1)).range =
      Module.finrank K (imagePiece G q (i + 1)) := by
    rw [LinearMap.range_eq_top.mpr (pieceMap_surjective G q (i + 1))]
    simp
  rw [he, pieceMap_ker, hq, ← step_range G G f hf i] at h2
  rw [step_ker] at h1
  rw [subPiece_finrank]
  omega

end Lech.Grading
namespace Lech

variable {K S M : Type*} [Field K] [CommRing S] [Algebra K S]
  [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]

lemma quotient_generators {n : ℕ} (x : Fin (n + 1) → S)
    (hx : Algebra.adjoin K (Set.range x) = ⊤) :
    Algebra.adjoin K (Set.range (fun i : Fin n =>
      Ideal.Quotient.mk (Ideal.span {x 0}) (x i.succ))) = ⊤ := by
  let q := Ideal.Quotient.mkₐ K (Ideal.span {x 0})
  have he := congrArg (Subalgebra.map q) hx
  rw [AlgHom.map_adjoin, Algebra.map_top,
    (AlgHom.range_eq_top q).mpr (Ideal.Quotient.mk_surjective)] at he
  rw [Fin.range_fin_succ, Set.image_insert_eq, ← Set.range_comp] at he
  have hzero : q (x 0) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  rw [hzero, Algebra.adjoin_insert_zero] at he
  exact he

lemma finite_of_no_generators [Module.Finite S M]
    (hx : Algebra.adjoin K (∅ : Set S) = ⊤) : Module.Finite K M := by
  have hs : Function.Surjective (algebraMap K S) := by
    apply Algebra.surjective_algebraMap_iff.mpr
    simpa only [Algebra.adjoin_empty] using hx.symm
  exact ⟨by simpa using (Module.Finite.fg_top (R := S) (M := M)).restrictScalars_of_surjective hs⟩

variable (x : S)

lemma ker_smul_killed : Module.IsTorsionBy S (LinearMap.lsmul S M x).ker x := by
  intro m
  apply Subtype.ext
  exact LinearMap.mem_ker.mp m.property

lemma coker_smul_killed : Module.IsTorsionBy S (M ⧸ (LinearMap.lsmul S M x).range) x := by
  apply (Module.isTorsionBy_quotient_iff _ _).mpr
  intro m
  exact ⟨m, rfl⟩

end Lech
end OAI
#print axioms OAI.Lech.Grading.finrank_recurrence
