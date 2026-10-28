module

public import BookNativeEuclideanCriterion
public import BookNativeSelectedReducedQuadratic
public import NativeHStressFunctional

@[expose] public section

noncomputable section
namespace Option2.NativeStress.BookHT.PositiveKernel
open EuclideanCriterion BookOrthogonal SheetReduction TangentCoordinates
open CKM.NativeFirstOrder CKM.NativeGroupSlice CKM.NativeSliceImplicitReduction
open scoped BigOperators InnerProductSpace ContDiff

/-- Sum of block energies is the Euclidean norm squared, without changing the
Book outer maximum norm. -/
theorem totalSquaredLength_toBlocks (x : BookOrthogonal.E) :
    FourBlock.totalSquaredLength (toBlocks x) = ‖x‖ ^ 2 := by
  simp only [FourBlock.totalSquaredLength, EuclideanSpace.norm_sq_eq,
    Fintype.sum_prod_type, toBlocks_apply]

theorem norm_toBlocks_on_W (i : Fin 4) (x : BookOrthogonal.E) (hx : x ∈ W i) :
    ‖toBlocks x i‖ = ‖x‖ := by
  have ha := (mem_W_iff_onAxis i x).mp hx
  have hs : FourBlock.totalSquaredLength (toBlocks x) = ‖toBlocks x i‖ ^ 2 := by
    unfold FourBlock.totalSquaredLength
    apply Finset.sum_eq_single i
    · intro j hj hji
      rw [ha j hji, norm_zero, zero_pow (by decide)]
    · simp
  rw [totalSquaredLength_toBlocks] at hs
  nlinarith [norm_nonneg (toBlocks x i), norm_nonneg x]

/-- Actual Euclidean orthogonality to W_i forces precisely the i-th Book block
of the normal vector to vanish. -/
theorem orthogonal_block_zero (i : Fin 4) (n : BookOrthogonal.E)
    (hn : n ∈ (W i).orthogonal) : toBlocks n i = 0 := by
  have hz : ⟪blockPart i n, n⟫_ℝ = 0 :=
    (W i).inner_right_of_mem_orthogonal (blockPart_mem i n) hn
  have he : ⟪blockPart i n, n⟫_ℝ = ⟪blockPart i n, blockPart i n⟫_ℝ := by
    rw [PiLp.inner_apply, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : a.1 = i <;> simp [blockPart, h]
  have hzero : blockPart i n = 0 := inner_self_eq_zero.mp (he.symm.trans hz)
  apply PiLp.ext
  intro a
  have h := congrArg (fun x : BookOrthogonal.E => x (i,a)) hzero
  simpa [blockPart] using h

/-- The actual half-Hessian is a smooth bilinear diagonal on E. -/
theorem transverseQuadraticPart_contDiff :
    ContDiff ℝ ∞ (SupportedStress.transverseQuadraticPart fE) := by
  let B := fderiv ℝ (fderiv ℝ fE) (0 : EuclideanModel)
  have hi : ContDiff ℝ ∞ (fun x : BookOrthogonal.E => ((0 : Common), x)) :=
    contDiff_const.prodMk contDiff_id
  change ContDiff ℝ ∞ (fun x : BookOrthogonal.E => (1/2 : ℝ) • B (0,x) (0,x))
  exact ((B.contDiff.comp hi).clm_apply hi).const_smul (1/2 : ℝ)

private theorem contraction_derivative_kernel (ell : Residual →L[ℝ] Blocks)
    (Q : Blocks → Blocks) (w n : BookOrthogonal.E)
    (hQ : DifferentiableAt ℝ Q (toBlocks w))
    (he : ell ∘ SupportedStress.transverseQuadraticPart fE = Q ∘ toBlocks)
    (hk : (fderiv ℝ (SupportedStress.transverseQuadraticPart fE) w) n = 0) :
    (fderiv ℝ Q (toBlocks w)) (toBlocks n) = 0 := by
  have hd := congrArg (fun g : BookOrthogonal.E → Blocks => (fderiv ℝ g w) n) he
  rw [fderiv_comp w ell.differentiableAt
      (transverseQuadraticPart_contDiff.differentiable (by simp)).differentiableAt,
    fderiv_comp w hQ toBlocks.differentiableAt,
    ContinuousLinearMap.fderiv, ContinuousLinearEquiv.fderiv] at hd
  change ell ((fderiv ℝ (SupportedStress.transverseQuadraticPart fE) w) n) =
    (fderiv ℝ Q (toBlocks w)) (toBlocks n) at hd
  rw [hk, map_zero] at hd
  exact hd.symm

variable
  (hreproH : ∀ z : Blocks, NativeH.residualContraction (Option2.NativeStress.originalF
    (Option2.BookNativeBase.bookBase + realV z)) = H z)
  (hreproT : ∀ z : Blocks, ReducedQuadratic.selectedT (Option2.NativeStress.originalF
    (Option2.BookNativeBase.bookBase + realV z)) = T z)

include hreproH hreproT

/-- Differentiate the two actually derived contractions; the full polar terms
have no factor one-half. No polar-kernel conclusion is assumed. -/
theorem derivative_kernel_to_polar (w n : BookOrthogonal.E)
    (hk : (fderiv ℝ (SupportedStress.transverseQuadraticPart fE) w) n = 0) :
    QuadraticMap.polar H (toBlocks w) (toBlocks n) = 0 ∧
      QuadraticMap.polar T (toBlocks w) (toBlocks n) = 0 := by
  have hH : NativeH.residualContraction ∘ SupportedStress.transverseQuadraticPart fE =
      H ∘ toBlocks := by
    funext x
    change NativeH.residualContraction (SupportedStress.transverseQuadraticPart fE x) = H (toBlocks x)
    rw [transverseQuadraticPart_fE]
    exact ReducedQuadratic.selectedH_reduced_of_reproduction hreproH (toBlocks x)
  have hT : ReducedQuadratic.selectedT ∘ SupportedStress.transverseQuadraticPart fE =
      T ∘ toBlocks := by
    funext x
    change ReducedQuadratic.selectedT (SupportedStress.transverseQuadraticPart fE x) = T (toBlocks x)
    rw [transverseQuadraticPart_fE]
    exact ReducedQuadratic.selectedT_reduced_of_reproduction hreproT (toBlocks x)
  constructor
  · have h := contraction_derivative_kernel NativeH.residualContraction H w n
      (contDiff_H.differentiable (by simp)).differentiableAt hH hk
    rwa [fderiv_H_apply] at h
  · have h := contraction_derivative_kernel ReducedQuadratic.selectedT T w n
      (contDiff_T.differentiable (by simp)).differentiableAt hT hk
    rwa [fderiv_T_apply] at h

/-- Conditional only on the two exact native reproductions, the actual fE
quadratic has precisely the actual four orthogonal W axes as its zero set. -/
theorem actual_fE_quadratic_zero_cone (x : BookOrthogonal.E) :
    SupportedStress.transverseQuadraticPart fE x = 0 ↔
      x ∈ SupportedStress.blockUnion W := by
  rw [transverseQuadraticPart_fE]
  exact (ReducedQuadratic.actual_reduced_zero_cone_of_reproduction
    hreproH hreproT (toBlocks x)).trans (mem_blockUnion_iff x).symm

/-- Book's positive kernel identity now applies to the actual fE derivative
kernel, with its support, norm and polar hypotheses discharged. -/
theorem positive_Book_kernel (i : Fin 4) (w : W i) (hw : ‖w‖ = 1)
    (n : BookOrthogonal.E) (hn : n ∈ (W i).orthogonal) (hne : n ≠ 0)
    (hk : (fderiv ℝ (SupportedStress.transverseQuadraticPart fE) (w : BookOrthogonal.E)) n = 0) :
    0 < 3 * ⟪sigma (toBlocks (w : BookOrthogonal.E) i), H (toBlocks n) i⟫_ℝ := by
  have hp := derivative_kernel_to_polar hreproH hreproT (w : BookOrthogonal.E) n hk
  have hunit : ‖toBlocks (w : BookOrthogonal.E) i‖ = 1 :=
    (norm_toBlocks_on_W i (w : BookOrthogonal.E) w.property).trans hw
  have hw0 : toBlocks (w : BookOrthogonal.E) ≠ 0 := by
    intro hz
    rw [hz, Pi.zero_apply, norm_zero] at hunit
    norm_num at hunit
  have hn0 : toBlocks n ≠ 0 := by
    intro hz
    exact hne (toBlocks.injective (by simpa only [map_zero] using hz))
  exact BookHT.kernel_stress_pos i (toBlocks (w : BookOrthogonal.E)) (toBlocks n)
    ((mem_W_iff_onAxis i (w : BookOrthogonal.E)).mp w.property)
    (orthogonal_block_zero i n hn) hw0 hn0 hp.1 hp.2

/-- Explicit complex-Hermitian form of the same real pairing. -/
theorem positive_hermitian_kernel (i : Fin 4) (w : W i) (hw : ‖w‖ = 1)
    (n : BookOrthogonal.E) (hn : n ∈ (W i).orthogonal) (hne : n ≠ 0)
    (hk : (fderiv ℝ (SupportedStress.transverseQuadraticPart fE) (w : BookOrthogonal.E)) n = 0) :
    0 < 3 * (⟪sigma (toBlocks (w : BookOrthogonal.E) i), H (toBlocks n) i⟫_ℂ).re := by
  have he (u v : Triple) : ⟪u,v⟫_ℝ = (⟪u,v⟫_ℂ).re := by
    simp only [PiLp.inner_apply, Complex.re_sum, Complex.inner, RCLike.inner_apply]
  rw [← he]
  exact positive_Book_kernel hreproH hreproT i w hw n hn hne hk

/-- The exact base H functional used by the native field is positive on the
actual fE quadratic, with no desired positivity hypothesis. -/
theorem positive_native_base_H (i : Fin 4) (w : W i) (hw : ‖w‖ = 1)
    (n : BookOrthogonal.E) (hn : n ∈ (W i).orthogonal) (hne : n ≠ 0)
    (hk : (fderiv ℝ (SupportedStress.transverseQuadraticPart fE) (w : BookOrthogonal.E)) n = 0) :
    0 < NativeH.realStressFunctional i (toBlocks (w : BookOrthogonal.E))
      (SupportedStress.transverseQuadraticPart fE n) := by
  rw [NativeH.realStressFunctional_apply, transverseQuadraticPart_fE,
    ReducedQuadratic.selectedH_reduced_of_reproduction hreproH]
  exact positive_Book_kernel hreproH hreproT i w hw n hn hne hk

end Option2.NativeStress.BookHT.PositiveKernel
