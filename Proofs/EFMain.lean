module

public import EFIndex
public import EFSums

@[expose] public section

/-!
# Native exact-frame energy sandwich and equality

For `P : Fin 39 → Albert`, a label equivalence `e : Fin 39 ≃ Fin 13 × Fin 3` with
`∀ h, Frame (framesOf e P h)`, and the literal hypotheses of the source-admitted
`SupportedStress.NativeFrames.thirteen_frame_overlap_loss_sandwich` (reused, not reproved):
* `(m/2) D ≤ E39 φ P - E0 φ ≤ (M/2) D`;
* `E39 φ P = E0 φ ↔ (all 702 cross overlaps = 1/3) ↔ OverlapBound P`;
* at equality `P` is injective (from purity, self-overlap `1` and `OverlapBound`).
The baseline is a sharp minimum on this exact-frame/domain-restricted class only. No best curvature
constant, distance exponent or global optimality among arbitrary 39 pure points is asserted.

References. The 39-point code of thirteen orthogonal triples with cross overlap `1/3` is
Cohn–Kumar–Minton, arXiv:1308.3188v4, Thm 8.3 (p. 49); they cite its universal optimality
(energy minimization over all 39-point sets for absolutely monotone potentials) from Cohn–Kumar,
J. Amer. Math. Soc. 20 (2007), Thm 8.2 (p. 131). The present statement is different: a two-sided
quadratic comparison for frame-split configurations under curvature bounds `m ≤ φ'' ≤ M`, with no
monotonicity and no minimization over arbitrary configurations; the equality set is not claimed to
be a single code (CKM p. 49 give a four-parameter family). The scalar step (reused) is the standard
strong-convexity / smoothness Taylor bound, e.g. Boyd–Vandenberghe, Convex Optimization, §9.1.2,
(9.8) p. 459 and (9.13) p. 461. The row sums `∑ⱼ ⟨p, qⱼ⟩ = trace p = 1` use only `∑ⱼ qⱼ = 1`.
-/

noncomputable section

namespace CKM.NativeExactFrameEnergy

open Glennie SupportedStress.NativeFrames CKM.NativeTightCode

/-- **Indexed native sandwich.** -/
theorem native_energy_sandwich (P : Fin 39 → Albert) (e : Fin 39 ≃ Fin 13 × Fin 3)
    (hframe : ∀ h, Frame (framesOf e P h))
    (φ : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U) (hconvex : Convex ℝ U)
    (hφ : ContDiffOn ℝ 2 φ U) (hbase : (1 / 3 : ℝ) ∈ U)
    (m M : ℝ) (hm : 0 < m)
    (hcurv : ∀ x ∈ U, m ≤ deriv (deriv φ) x ∧ deriv (deriv φ) x ≤ M)
    (hnear : ∀ k : ThirteenCrossPair, thirteenCrossOverlap (framesOf e P) k ∈ U) :
    (m / 2) * D (framesOf e P) ≤ E39 φ P - E0 φ ∧
      E39 φ P - E0 φ ≤ (M / 2) * D (framesOf e P) := by
  rw [E39_eq_thirteenFrameEnergy φ e P]
  unfold E0 D
  exact thirteen_frame_overlap_loss_sandwich (framesOf e P) hframe φ U hU hconvex hφ hbase
    m M hm hcurv hnear

/-- For an exact-frame labelling, all cross overlaps are `1/3` iff the native overlap bound holds. -/
theorem cross_eq_third_iff_overlapBound (P : Fin 39 → Albert) (e : Fin 39 ≃ Fin 13 × Fin 3)
    (hframe : ∀ h, Frame (framesOf e P h)) :
    (∀ k : ThirteenCrossPair, thirteenCrossOverlap (framesOf e P) k = 1 / 3) ↔
      OverlapBound P := by
  constructor
  · intro hall i j hij
    by_cases hb : (e i).1 = (e j).1
    · have hne : (e i).2 ≠ (e j).2 := fun h2 => hij (e.injective (Prod.ext hb h2))
      have h0 := (hframe (e i).1).orthogonal (e i).2 (e j).2 hne
      have hi : framesOf e P (e i).1 (e i).2 = P i := by simp [framesOf]
      have hj : framesOf e P (e i).1 (e j).2 = P j := by rw [hb]; simp [framesOf]
      rw [hi, hj] at h0
      have : Glennie.inner (P i) (P j) = 0 := by
        unfold Glennie.inner
        rw [h0]
        simp [Glennie.trace]
      rw [this]
      norm_num
    · rcases lt_or_gt_of_ne hb with hlt | hlt
      · have h := hall (⟨((e i).1, (e j).1), hlt⟩, ((e i).2, (e j).2))
        have hc : thirteenCrossOverlap (framesOf e P) (⟨((e i).1, (e j).1), hlt⟩, ((e i).2, (e j).2))
            = Glennie.inner (P i) (P j) := by
          simp [thirteenCrossOverlap, framesOf, Glennie.inner]
        rw [hc] at h
        rw [h]
      · have h := hall (⟨((e j).1, (e i).1), hlt⟩, ((e j).2, (e i).2))
        have hc : thirteenCrossOverlap (framesOf e P) (⟨((e j).1, (e i).1), hlt⟩, ((e j).2, (e i).2))
            = Glennie.inner (P j) (P i) := by
          simp [thirteenCrossOverlap, framesOf, Glennie.inner]
        rw [hc, Glennie.inner_comm] at h
        rw [h]
  · intro hov
    apply cross_eq_third_of_le (framesOf e P) hframe
    rintro ⟨⟨⟨h, k⟩, hlt⟩, ⟨a, b⟩⟩
    have hne : e.symm (h, a) ≠ e.symm (k, b) := by
      intro heq
      have := congrArg Prod.fst (e.symm.injective heq)
      exact (ne_of_lt hlt) this
    exact hov _ _ hne

/-- **Equality characterization.** -/
theorem native_energy_equality (P : Fin 39 → Albert) (e : Fin 39 ≃ Fin 13 × Fin 3)
    (hframe : ∀ h, Frame (framesOf e P h))
    (φ : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U) (hconvex : Convex ℝ U)
    (hφ : ContDiffOn ℝ 2 φ U) (hbase : (1 / 3 : ℝ) ∈ U)
    (m M : ℝ) (hm : 0 < m)
    (hcurv : ∀ x ∈ U, m ≤ deriv (deriv φ) x ∧ deriv (deriv φ) x ≤ M)
    (hnear : ∀ k : ThirteenCrossPair, thirteenCrossOverlap (framesOf e P) k ∈ U) :
    (E39 φ P = E0 φ ↔ ∀ k : ThirteenCrossPair, thirteenCrossOverlap (framesOf e P) k = 1 / 3) ∧
      ((∀ k : ThirteenCrossPair, thirteenCrossOverlap (framesOf e P) k = 1 / 3) ↔
        OverlapBound P) := by
  obtain ⟨hlo, hhi⟩ := native_energy_sandwich P e hframe φ U hU hconvex hφ hbase m M hm hcurv hnear
  refine ⟨⟨fun hE => ?_, fun hall => ?_⟩, cross_eq_third_iff_overlapBound P e hframe⟩
  · have hDnn := D_nonneg (framesOf e P)
    have hDle : D (framesOf e P) ≤ 0 := by
      by_contra hc
      have := mul_pos (half_pos hm) (lt_of_not_ge hc)
      rw [hE, sub_self] at hlo
      linarith
    exact (D_eq_zero_iff _).mp (le_antisymm hDle hDnn)
  · have hD := (D_eq_zero_iff (framesOf e P)).mpr hall
    rw [hD, mul_zero] at hlo hhi
    linarith

theorem energy_eq_baseline_iff_overlapBound (P : Fin 39 → Albert) (e : Fin 39 ≃ Fin 13 × Fin 3)
    (hframe : ∀ h, Frame (framesOf e P h))
    (φ : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U) (hconvex : Convex ℝ U)
    (hφ : ContDiffOn ℝ 2 φ U) (hbase : (1 / 3 : ℝ) ∈ U)
    (m M : ℝ) (hm : 0 < m)
    (hcurv : ∀ x ∈ U, m ≤ deriv (deriv φ) x ∧ deriv (deriv φ) x ≤ M)
    (hnear : ∀ k : ThirteenCrossPair, thirteenCrossOverlap (framesOf e P) k ∈ U) :
    E39 φ P = E0 φ ↔ OverlapBound P := by
  obtain ⟨h1, h2⟩ := native_energy_equality P e hframe φ U hU hconvex hφ hbase m M hm hcurv hnear
  exact h1.trans h2

/-- The baseline is a lower bound on this exact-frame/domain-restricted class. -/
theorem baseline_le_energy (P : Fin 39 → Albert) (e : Fin 39 ≃ Fin 13 × Fin 3)
    (hframe : ∀ h, Frame (framesOf e P h))
    (φ : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U) (hconvex : Convex ℝ U)
    (hφ : ContDiffOn ℝ 2 φ U) (hbase : (1 / 3 : ℝ) ∈ U)
    (m M : ℝ) (hm : 0 < m)
    (hcurv : ∀ x ∈ U, m ≤ deriv (deriv φ) x ∧ deriv (deriv φ) x ≤ M)
    (hnear : ∀ k : ThirteenCrossPair, thirteenCrossOverlap (framesOf e P) k ∈ U) :
    E0 φ ≤ E39 φ P := by
  obtain ⟨hlo, -⟩ := native_energy_sandwich P e hframe φ U hU hconvex hφ hbase m M hm hcurv hnear
  have hDnn := D_nonneg (framesOf e P)
  have := mul_nonneg (half_pos hm).le hDnn
  linarith

/-- Pure points with the overlap bound are distinct (self-overlap `1 > 1/3`). Any `N`. -/
theorem injective_of_overlapBound {N : ℕ} (P : Fin N → Albert) (hpure : ∀ i, IsPure (P i))
    (hov : OverlapBound P) : Function.Injective P := by
  intro i j hij
  by_contra hne
  have h := hov i j hne
  rw [hij] at h
  have h1 : Glennie.inner (P j) (P j) = 1 := by
    unfold Glennie.inner
    rw [(hpure j).1, (hpure j).2]
  rw [h1] at h
  norm_num at h

/-- At equality the 39 labelled points are distinct; derived, not assumed. -/
theorem injective_of_energy_eq_baseline (P : Fin 39 → Albert) (e : Fin 39 ≃ Fin 13 × Fin 3)
    (hframe : ∀ h, Frame (framesOf e P h))
    (φ : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U) (hconvex : Convex ℝ U)
    (hφ : ContDiffOn ℝ 2 φ U) (hbase : (1 / 3 : ℝ) ∈ U)
    (m M : ℝ) (hm : 0 < m)
    (hcurv : ∀ x ∈ U, m ≤ deriv (deriv φ) x ∧ deriv (deriv φ) x ≤ M)
    (hnear : ∀ k : ThirteenCrossPair, thirteenCrossOverlap (framesOf e P) k ∈ U)
    (heq : E39 φ P = E0 φ) : Function.Injective P := by
  have hpure : ∀ i, IsPure (P i) := by
    intro i
    have h := isPure_of_frame (hframe (e i).1) (e i).2
    simp only [framesOf, Prod.mk.eta, Equiv.symm_apply_apply] at h
    exact h
  have hov : OverlapBound P :=
    (energy_eq_baseline_iff_overlapBound P e hframe φ U hU hconvex hφ hbase m M hm hcurv hnear).mp heq
  exact injective_of_overlapBound P hpure hov

end CKM.NativeExactFrameEnergy
