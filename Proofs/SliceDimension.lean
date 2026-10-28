module

public import SliceKernel
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Sym.Card

@[expose] public section

/-!
# Dimension counts for the slice

* `finrank_linearAnnihilator`: for a pivoted slice matrix `B : Matrix (Fin n) (Fin m) K`, the
  linear forms vanishing on the slice form a space of dimension `n - m`.
* (S3) `eq_linearAnnihilator_of_le_of_finrank_le`: a space `W` of linear forms vanishing on
  the slice with `dim W ≥ n - m` is the whole annihilator.
* `finrank_homogeneousSubmodule`: the forms of degree `d` in `m` variables have dimension
  `multichoose m d = (m + d - 1).choose d` (stars and bars, via `Sym.card_sym_eq_multichoose`).
* (S4) `finrank_quotient_sliceRelations_le`: if `W` is the annihilator, then
  `dim (S_(e+1) / W · S_e) ≤ dim (forms of degree e+1 in m variables)`, because restriction
  induces an injective map from the quotient.
-/

open MvPolynomial Module
open scoped Matrix

namespace SliceLemmas

variable {K : Type*} [Field K] {n m : ℕ}

/-- `linearForm` as a `K`-linear map from coefficient vectors to polynomials. -/
noncomputable def linearFormMap : (Fin n → K) →ₗ[K] MvPolynomial (Fin n) K where
  toFun := linearForm
  map_add' c c' := by
    simp [linearForm, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [linearForm, Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply,
      Finset.smul_sum, smul_eq_C_mul, mul_assoc]

theorem linearFormMap_apply (c : Fin n → K) : linearFormMap c = linearForm c := rfl

theorem linearFormMap_injective :
    Function.Injective (linearFormMap : (Fin n → K) →ₗ[K] MvPolynomial (Fin n) K) :=
  linearForm_injective

/-- The annihilator of the slice is the image, under `linearForm`, of the left kernel of `B`. -/
theorem linearAnnihilator_eq_map_ker (B : Matrix (Fin n) (Fin m) K) :
    linearAnnihilator B = (LinearMap.ker B.vecMulLinear).map linearFormMap := by
  ext ℓ
  rw [mem_linearAnnihilator_iff_vecMul, Submodule.mem_map]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨coeffVector ℓ, h2, linearForm_coeffVector h1⟩
  · rintro ⟨c, hc, rfl⟩
    refine ⟨linearForm_mem_homogeneousSubmodule c, ?_⟩
    rw [linearFormMap_apply, coeffVector_linearForm]
    exact hc

/-- Under the pivot condition, `c ↦ c ᵥ* B` is surjective onto `K^m`. -/
theorem vecMulLinear_surjective {B : Matrix (Fin n) (Fin m) K} {piv : Fin m → Fin n}
    (hB : IsPivot B piv) : Function.Surjective B.vecMulLinear := by
  classical
  let P : Matrix (Fin m) (Fin n) K := Matrix.of fun t j => if piv t = j then 1 else 0
  have hPB : P * B = 1 := by
    ext t t'
    rw [Matrix.mul_apply, Matrix.one_apply, ← hB t t']
    simp [P]
  intro y
  refine ⟨y ᵥ* P, ?_⟩
  rw [Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul, hPB, Matrix.vecMul_one]

theorem finrank_ker_vecMulLinear {B : Matrix (Fin n) (Fin m) K} {piv : Fin m → Fin n}
    (hB : IsPivot B piv) : finrank K (LinearMap.ker B.vecMulLinear) = n - m := by
  have h := LinearMap.finrank_range_add_finrank_ker B.vecMulLinear
  rw [LinearMap.range_eq_top.mpr (vecMulLinear_surjective hB), finrank_top,
    Module.finrank_fin_fun, Module.finrank_fin_fun] at h
  omega

instance linearAnnihilator_finiteDimensional (B : Matrix (Fin n) (Fin m) K) :
    FiniteDimensional K (linearAnnihilator B) := by
  rw [linearAnnihilator_eq_map_ker]
  infer_instance

/-- The linear forms vanishing on a pivoted slice form a space of dimension `n - m`. -/
theorem finrank_linearAnnihilator {B : Matrix (Fin n) (Fin m) K} {piv : Fin m → Fin n}
    (hB : IsPivot B piv) : finrank K (linearAnnihilator B) = n - m := by
  rw [linearAnnihilator_eq_map_ker, ← finrank_ker_vecMulLinear hB]
  exact (Submodule.equivMapOfInjective _ linearFormMap_injective _).finrank_eq.symm

/-- (S3) A space of linear forms vanishing on the slice, of dimension at least `n - m`, is the
whole annihilator. -/
theorem eq_linearAnnihilator_of_le_of_finrank_le {B : Matrix (Fin n) (Fin m) K}
    {piv : Fin m → Fin n} (hB : IsPivot B piv) {W : Submodule K (MvPolynomial (Fin n) K)}
    (hW : W ≤ linearAnnihilator B) (hdim : n - m ≤ finrank K W) : W = linearAnnihilator B :=
  Submodule.eq_of_le_of_finrank_le hW (by rw [finrank_linearAnnihilator hB]; exact hdim)

/-- Exponent vectors of total degree `d` in `m` variables correspond to multisets of size `d`
on `Fin m` (stars and bars). -/
noncomputable def degreeEqEquivSym (m d : ℕ) :
    {u : Fin m →₀ ℕ | u.degree = d} ≃ Sym (Fin m) d :=
  ((Sym.equivNatSum (Fin m) d).trans
    (Equiv.subtypeEquivRight fun P => by
      simp [Finsupp.degree_apply, Finsupp.sum])).symm

/-- The forms of degree `d` in `m` variables have dimension `multichoose m d`. -/
theorem finrank_homogeneousSubmodule (m d : ℕ) :
    finrank K (homogeneousSubmodule (Fin m) K d) = Nat.multichoose m d := by
  rw [homogeneousSubmodule_eq_finsupp_supported,
    (AddMonoidAlgebra.supportedEquivFinsupp (R := K) (S := K)
      {u : Fin m →₀ ℕ | u.degree = d}).finrank_eq,
    (Finsupp.domLCongr (M := K) (R := K) (degreeEqEquivSym m d)).finrank_eq,
    finrank_finsupp_self, Sym.card_sym_eq_multichoose, Fintype.card_fin]

theorem finrank_homogeneousSubmodule_eq_choose (m d : ℕ) :
    finrank K (homogeneousSubmodule (Fin m) K d) = (m + d - 1).choose d := by
  rw [finrank_homogeneousSubmodule, Nat.multichoose_eq]

instance homogeneousSubmodule_finite (m d : ℕ) :
    Module.Finite K (homogeneousSubmodule (Fin m) K d) :=
  Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg _ _ d)

/-- Restriction as a linear map between the forms of degree `d` in `n` and in `m` variables. -/
noncomputable def restrictHomogeneous (B : Matrix (Fin n) (Fin m) K) (d : ℕ) :
    homogeneousSubmodule (Fin n) K d →ₗ[K] homogeneousSubmodule (Fin m) K d :=
  LinearMap.codRestrict _ ((restrict B).toLinearMap ∘ₗ (homogeneousSubmodule (Fin n) K d).subtype)
    fun f => restrict_isHomogeneous B f.2

theorem restrictHomogeneous_apply (B : Matrix (Fin n) (Fin m) K) (d : ℕ)
    (f : homogeneousSubmodule (Fin n) K d) :
    (restrictHomogeneous B d f : MvPolynomial (Fin m) K) = restrict B f := rfl

/-- `W · S_e` viewed inside the space of forms of degree `e + 1`. -/
noncomputable def sliceRelationsIn (W : Submodule K (MvPolynomial (Fin n) K)) (e : ℕ) :
    Submodule K (homogeneousSubmodule (Fin n) K (e + 1)) :=
  (sliceRelations W e).comap (homogeneousSubmodule (Fin n) K (e + 1)).subtype

/-- When `W` is the annihilator, the kernel of restriction on forms of degree `e + 1` is
exactly `W · S_e`. -/
theorem ker_restrictHomogeneous {B : Matrix (Fin n) (Fin m) K} {piv : Fin m → Fin n}
    (hB : IsPivot B piv) {W : Submodule K (MvPolynomial (Fin n) K)}
    (hW : W = linearAnnihilator B) (e : ℕ) :
    LinearMap.ker (restrictHomogeneous B (e + 1)) = sliceRelationsIn W e := by
  ext f
  rw [LinearMap.mem_ker, sliceRelationsIn, Submodule.mem_comap, Submodule.subtype_apply,
    mem_sliceRelations_iff hB hW, ← Subtype.coe_inj, restrictHomogeneous_apply]
  simp [f.2]

/-- The map from `S_(e+1) / W · S_e` to forms of degree `e + 1` in `m` variables induced by
restriction. -/
noncomputable def quotientRestrict {B : Matrix (Fin n) (Fin m) K} {piv : Fin m → Fin n}
    (hB : IsPivot B piv) {W : Submodule K (MvPolynomial (Fin n) K)}
    (hW : W = linearAnnihilator B) (e : ℕ) :
    (homogeneousSubmodule (Fin n) K (e + 1) ⧸ sliceRelationsIn W e) →ₗ[K]
      homogeneousSubmodule (Fin m) K (e + 1) :=
  (sliceRelationsIn W e).liftQ (restrictHomogeneous B (e + 1))
    (ker_restrictHomogeneous hB hW e).ge

theorem quotientRestrict_injective {B : Matrix (Fin n) (Fin m) K} {piv : Fin m → Fin n}
    (hB : IsPivot B piv) {W : Submodule K (MvPolynomial (Fin n) K)}
    (hW : W = linearAnnihilator B) (e : ℕ) :
    Function.Injective (quotientRestrict hB hW e) := by
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ (ker_restrictHomogeneous hB hW e).le

/-- (S4) If `W` is the annihilator of the pivoted slice, then
`dim (S_(e+1) / W · S_e) ≤ multichoose m (e+1) = (m + e).choose (e + 1)`. -/
theorem finrank_quotient_sliceRelations_le {B : Matrix (Fin n) (Fin m) K}
    {piv : Fin m → Fin n} (hB : IsPivot B piv) {W : Submodule K (MvPolynomial (Fin n) K)}
    (hW : W = linearAnnihilator B) (e : ℕ) :
    finrank K (homogeneousSubmodule (Fin n) K (e + 1) ⧸ sliceRelationsIn W e) ≤
      Nat.multichoose m (e + 1) := by
  rw [← finrank_homogeneousSubmodule (K := K)]
  exact LinearMap.finrank_le_finrank_of_injective (quotientRestrict_injective hB hW e)

end SliceLemmas
