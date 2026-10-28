module

public import TCBound
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Algebra.Ring.Real

@[expose] public section

/-!
# A7: local constancy of the labelled frame partition 

On `tightLocus` (labelled 39-point pure codes with the bound, in the product topology of the 27
native upper coordinates) every distinct overlap is `0` or `1/3` (`tight_overlap_values`), and each
overlap `C ↦ ⟨codePoint C i, codePoint C j⟩` is continuous (a bilinear form in the coordinates via
`upperCoordinateEquiv`). So within distance `< 1/6` of its value it cannot jump, and the relation
`i = j ∨ ⟨·,·⟩ = 0` is locally constant on the locus. No claim about stabilizers is made.
-/

noncomputable section

namespace CKM.NativeTightCode

open Glennie Topology

/-- The native trace pairing transported to coordinates, as a bilinear map. -/
private def stable_innerCoord :
    (Fin 27 → ℝ) →ₗ[ℝ] (Fin 27 → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun u v => inner (NativePolynomial.upperCoordinateEquiv.symm u)
      (NativePolynomial.upperCoordinateEquiv.symm v))
    (fun u u' v => by
      simp only [map_add, CKM.NativeDerivationTriality.Reuse.inner_add_left])
    (fun r u v => by
      simp only [map_smul, CKM.NativeDerivationTriality.Reuse.inner_smul_left, smul_eq_mul])
    (fun u v v' => by
      simp only [map_add, CKM.NativeDerivationTriality.Reuse.inner_add_right])
    (fun r u v => by
      simp only [map_smul, CKM.NativeDerivationTriality.Reuse.inner_smul_right, smul_eq_mul])

/-- Coordinate expansion of the transported pairing. -/
private theorem stable_inner_expand (u v : Fin 27 → ℝ) :
    inner (NativePolynomial.upperCoordinateEquiv.symm u)
        (NativePolynomial.upperCoordinateEquiv.symm v) =
      ∑ k, ∑ l, u k * (v l * stable_innerCoord (fun j => if k = j then 1 else 0)
        (fun j => if l = j then 1 else 0)) := by
  change stable_innerCoord u v = _
  rw [LinearMap.pi_apply_eq_sum_univ stable_innerCoord u, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.smul_apply, LinearMap.pi_apply_eq_sum_univ _ v, smul_eq_mul, Finset.mul_sum]
  rfl

theorem codePoint_codeCoords (P : Fin 39 → Albert) : codePoint (codeCoords P) = P := by
  funext i
  exact NativePolynomial.upperCoordinateEquiv.symm_apply_apply (P i)

theorem continuous_inner_codePoint (i j : Fin 39) :
    Continuous fun C : CodeCoords => inner (codePoint C i) (codePoint C j) := by
  simp only [codePoint, stable_inner_expand]
  refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => ?_
  fun_prop

/-- Near every point of the tight locus (relative neighbourhood), the same labelled pairs have
zero overlap. -/
theorem zeroRel_eventually_eq {C : CodeCoords} (hC : C ∈ tightLocus) :
    ∀ᶠ C' in 𝓝[tightLocus] C, ∀ i j, zeroRel C' i j ↔ zeroRel C i j := by
  have hnear : ∀ᶠ C' in 𝓝 C, ∀ i j,
      |inner (codePoint C' i) (codePoint C' j) - inner (codePoint C i) (codePoint C j)| < 1 / 6 := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    have h := ((continuous_inner_codePoint i j).tendsto C).eventually
      (Metric.ball_mem_nhds (inner (codePoint C i) (codePoint C j)) (by norm_num : (0 : ℝ) < 1 / 6))
    filter_upwards [h] with C' hC'
    simpa [Metric.mem_ball, Real.dist_eq] using hC'
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hnear, eventually_mem_nhdsWithin]
    with C' hC' hmem i j
  unfold zeroRel
  by_cases hij : i = j
  · simp [hij]
  · simp only [hij, false_or]
    have hv := tight_overlap_values (codePoint C) hC.1 hC.2 i j hij
    have hv' := tight_overlap_values (codePoint C') hmem.1 hmem.2 i j hij
    have hd := abs_lt.1 (hC' i j)
    constructor
    · intro h0
      rcases hv with h | h
      · exact h
      · exfalso; linarith [hd.1, hd.2]
    · intro h0
      rcases hv' with h | h
      · exact h
      · exfalso; linarith [hd.1, hd.2]

/-- The labelled partition relation is locally constant on the tight locus. -/
theorem isLocallyConstant_zeroRel :
    IsLocallyConstant fun C : tightLocus => zeroRel C.1 := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro C
  rw [eventually_nhds_subtype_iff tightLocus C (fun C' => zeroRel C' = zeroRel C.1)]
  filter_upwards [zeroRel_eventually_eq C.2] with C' hC'
  funext i j
  exact propext (hC' i j)

/-- Native form: every tight native code has a coordinate neighbourhood on which every tight code
has the same zero-overlap pairs. -/
theorem zero_pairs_locally_constant (P : Fin 39 → Albert) (hpure : ∀ i, IsPure (P i))
    (hov : OverlapBound P) :
    ∃ U : Set CodeCoords, IsOpen U ∧ codeCoords P ∈ U ∧
      ∀ Q : Fin 39 → Albert, (∀ i, IsPure (Q i)) → OverlapBound Q → codeCoords Q ∈ U →
        ∀ i j, (i = j ∨ inner (Q i) (Q j) = 0) ↔ (i = j ∨ inner (P i) (P j) = 0) := by
  have hP : codeCoords P ∈ tightLocus := by
    refine ⟨fun i => ?_, ?_⟩
    · rw [codePoint_codeCoords]; exact hpure i
    · rw [codePoint_codeCoords]; exact hov
  obtain ⟨U, hU, hPU, hsub⟩ := mem_nhdsWithin.1 (zeroRel_eventually_eq hP)
  refine ⟨U, hU, hPU, fun Q hQpure hQov hQU i j => ?_⟩
  have hQ : codeCoords Q ∈ tightLocus := by
    refine ⟨fun i => ?_, ?_⟩
    · rw [codePoint_codeCoords]; exact hQpure i
    · rw [codePoint_codeCoords]; exact hQov
  have h := hsub ⟨hQU, hQ⟩ i j
  simpa only [zeroRel, codePoint_codeCoords] using h

#print axioms codePoint_codeCoords
#print axioms continuous_inner_codePoint
#print axioms zeroRel_eventually_eq
#print axioms isLocallyConstant_zeroRel
#print axioms zero_pairs_locally_constant

end CKM.NativeTightCode
