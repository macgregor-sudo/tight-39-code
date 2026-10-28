module

public import NativePhaseKernel
public import NativePhaseBookComplexification

@[expose] public section

/-! Pointwise recovery and coordinate change from the actual free-coordinate kernel
to the actual complexified raw Book kernel. CoordinateIndex retains common56 plus
BookRealIndex24; no Dictionary relabeling, D6 or Laurent claim is made. -/

noncomputable section
namespace Option2.NativeStress.PhaseBookChangeA6
open Matrix Module SliceLemmas
open scoped BigOperators

section Recovery
variable {K : Type*} [Field K] {m n k : ℕ}
variable (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin k) K)
variable (piv : Fin k → Fin n)

theorem mulVec_at_pivot (hB : IsPivot B piv) (x : Fin k → K) (t : Fin k) :
    (B *ᵥ x) (piv t) = x t := by
  classical
  unfold IsPivot at hB
  simp [Matrix.mulVec, dotProduct, hB]

theorem columns_mem_kernel (hAB : ∀ i t, ∑ j, A i j * B j t = 0) (x : Fin k → K) :
    B *ᵥ x ∈ LinearMap.ker A.mulVecLin := by
  have hab : A * B = 0 := by ext i t; exact hAB i t
  change A *ᵥ (B *ᵥ x) = 0
  rw [Matrix.mulVec_mulVec, hab, Matrix.zero_mulVec]

theorem kernel_coordinate_recovery (hB : IsPivot B piv)
    (hAB : ∀ i t, ∑ j, A i j * B j t = 0)
    (hdim : finrank K (LinearMap.ker A.mulVecLin) = k)
    (v : Fin n → K) (hv : v ∈ LinearMap.ker A.mulVecLin) :
    B *ᵥ (fun t => v (piv t)) = v := by
  have hinj : Function.Injective B.mulVecLin := by
    intro x y hxy
    funext t
    have h := congrFun hxy (piv t)
    simpa only [Matrix.mulVecLin_apply, mulVec_at_pivot B piv hB] using h
  have hle : LinearMap.range B.mulVecLin ≤ LinearMap.ker A.mulVecLin := by
    rintro _ ⟨x,rfl⟩
    exact columns_mem_kernel A B hAB x
  have heq : LinearMap.range B.mulVecLin = LinearMap.ker A.mulVecLin :=
    Submodule.eq_of_le_of_finrank_le hle (by
      rw [hdim, LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun])
  have hvr : v ∈ LinearMap.range B.mulVecLin := by rw [heq]; exact hv
  obtain ⟨x,hx⟩ := hvr
  have hp : (fun t => v (piv t)) = x := by
    funext t
    rw [← hx]
    exact mulVec_at_pivot B piv hB x t
  rw [hp]
  exact hx

def kernelRead : LinearMap.ker A.mulVecLin →ₗ[K] (Fin k → K) where
  toFun v t := v.val (piv t)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def kernelReadEquiv (hB : IsPivot B piv)
    (hAB : ∀ i t, ∑ j, A i j * B j t = 0)
    (hdim : finrank K (LinearMap.ker A.mulVecLin) = k) :
    LinearMap.ker A.mulVecLin ≃ₗ[K] (Fin k → K) :=
  LinearEquiv.ofBijective (kernelRead A piv) (by
    constructor
    · intro v w hvw
      apply Subtype.ext
      rw [← kernel_coordinate_recovery A B piv hB hAB hdim v.val v.property,
        ← kernel_coordinate_recovery A B piv hB hAB hdim w.val w.property]
      exact congrArg B.mulVec hvw
    · intro x
      refine ⟨⟨B *ᵥ x, columns_mem_kernel A B hAB x⟩, ?_⟩
      funext t
      exact mulVec_at_pivot B piv hB x t)

end Recovery

open PhasePivotA6 PhasePivotLocusA6 PhaseKernelA6 PhaseBookComplexificationA6
open CKM.NativeFourFamily

/-- The actual coordinate change preserves the explicit common56/real-Book24 labels. -/
theorem native_book_change (u : NativePhaseTorus) (hgood : IsGoodPhase u.1)
    (hpivot : u ∈ nativePivotLocus) :
    ∃ (B : Matrix (Fin 1053) (Fin 80) ℂ) (piv : Fin 80 → Fin 1053)
      (M : Matrix (Fin 80) CoordinateIndex ℂ) (N : Matrix CoordinateIndex (Fin 80) ℂ),
      IsPivot B piv ∧
      (∀ r t, ∑ j, nativeJ u.1 r j * B j t = 0) ∧
      (∀ i j, M i j = nativeComplexMatrix hgood (piv i) j) ∧
      B * M = nativeComplexMatrix hgood ∧ M * N = 1 ∧ N * M = 1 := by
  classical
  obtain ⟨B,piv,_,hB,hJB,_,_,hker⟩ := native_linear_slice_on_locus u hpivot
  let e := (nativeBookComplexEquiv hgood).trans
    (kernelReadEquiv (nativeJ u.1) B piv hB hJB hker)
  let M := LinearMap.toMatrix' e.toLinearMap
  let N := LinearMap.toMatrix' e.symm.toLinearMap
  have hM (i : Fin 80) (j : CoordinateIndex) :
      M i j = nativeComplexMatrix hgood (piv i) j := by
    change ((nativeBookComplexEquiv hgood (Pi.single j 1)).val) (piv i) = _
    rw [nativeBookComplexEquiv_matrix, Matrix.mulVec_single_one]
    rfl
  refine ⟨B,piv,M,N,hB,hJB,hM,?_,?_,?_⟩
  · ext i j
    have hv : (fun a => nativeComplexMatrix hgood a j) ∈
        LinearMap.ker (nativeJ u.1).mulVecLin := by
      have hh := (nativeBookComplexEquiv hgood (Pi.single j 1)).property
      rw [nativeBookComplexEquiv_matrix, Matrix.mulVec_single_one] at hh
      exact hh
    have hr := kernel_coordinate_recovery (nativeJ u.1) B piv hB hJB hker _ hv
    simpa only [Matrix.mul_apply, hM, Matrix.mulVec, dotProduct] using congrFun hr i
  · change LinearMap.toMatrix' e.toLinearMap * LinearMap.toMatrix' e.symm.toLinearMap = 1
    rw [← LinearMap.toMatrix'_comp]
    have hh : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact e.apply_symm_apply x
    rw [hh, LinearMap.toMatrix'_id]
  · change LinearMap.toMatrix' e.symm.toLinearMap * LinearMap.toMatrix' e.toLinearMap = 1
    rw [← LinearMap.toMatrix'_comp]
    have hh : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact e.symm_apply_apply x
    rw [hh, LinearMap.toMatrix'_id]

end Option2.NativeStress.PhaseBookChangeA6
