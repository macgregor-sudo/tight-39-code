module

public import TCBasic
public import TCGram

@[expose] public section

/-!
# A7: the 39-point code bound and its equality case 

Attribution: the bound is the instance of the linear-programming bound of Cohn–Kumar–Minton,
*Optimal simplices and codes in projective spaces*, arXiv:1308.3188v4, Proposition 2.5 (p. 8;
attributed there to Kabatiansky–Levenshtein and Delsarte–Goethals–Seidel), for the octonionic
projective plane with the degree-2 certificate `f(t) = t(t - 1/3)`; CKM does not print `N ≤ 39`
or this Gram-trace argument, which is written out here directly in native terms.

MASTER §6.11. With `H = centeredGram P` (diagonal `2/3`, off-diagonal `⟨P i, P j⟩ - 1/3 ∈ [-1/3, 0]`
by `overlap_nonneg` and the bound): `gram_trace_sq_le` gives `(2N/3)² ≤ 26 Σ H²`;
`Σ H² = 4N/9 + Σ_{i≠j} H²` and `h² ≤ -h/3` on `[-1/3, 0]` give
`Σ H² = 2N/3 - (1/3) 1ᵀH1 + Σ_{i≠j} (H² + H/3) ≤ 2N/3 - (1/3) 1ᵀH1`, and
`1ᵀH1 = ⟨Σ centered, Σ centered⟩ ≥ 0`. Hence `N ≤ 39` (trivial for `N = 0`). At `N = 39` all
inequalities are equalities: every off-diagonal `H ∈ {0, -1/3}` and `Σ centered = 0`, so
`Σ P i = 13 • 1` and every Gram row sums to `13`.
-/

noncomputable section

namespace CKM.NativeTightCode

open Glennie

open CKM.NativeDerivationTriality.Reuse in
private theorem bound_inner_zero_left (y : Albert) : inner (0 : Albert) y = 0 := by
  simpa using inner_smul_left (0 : ℝ) y y

open CKM.NativeDerivationTriality.Reuse in
/-- Finite-sum linearity of the native pairing in the left argument. -/
theorem bound_inner_sum_left {ι : Type*} (s : Finset ι) (f : ι → Albert) (y : Albert) :
    inner (∑ i ∈ s, f i) y = ∑ i ∈ s, inner (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [bound_inner_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, inner_add_left, ih]

/-- Finite-sum linearity of the native pairing in the right argument. -/
theorem bound_inner_sum_right {ι : Type*} (s : Finset ι) (x : Albert) (f : ι → Albert) :
    inner x (∑ i ∈ s, f i) = ∑ i ∈ s, inner x (f i) := by
  rw [inner_comm, bound_inner_sum_left]
  exact Finset.sum_congr rfl fun i _ => inner_comm _ _

/-- The nonnegative defect `δ_ij = [i = j]·(2/3) - (H_ij² + H_ij/3)` of the centered Gram entries. -/
private def boundDefect {N : ℕ} (P : Fin N → Albert) (i j : Fin N) : ℝ :=
  (if i = j then (2 / 3 : ℝ) else 0) -
    ((inner (centered (P i)) (centered (P j))) ^ 2 + inner (centered (P i)) (centered (P j)) / 3)

private theorem bound_defect_nonneg {N : ℕ} (P : Fin N → Albert) (hpure : ∀ i, IsPure (P i))
    (hov : OverlapBound P) (i j : Fin N) : 0 ≤ boundDefect P i j := by
  unfold boundDefect
  rw [inner_centered (hpure i) (hpure j)]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    rw [inner_self_of_pure (hpure i)]
    norm_num
  · simp only [hij, ↓reduceIte]
    have h0 := overlap_nonneg (hpure i).1 (hpure j).1
    have h1 := hov i j hij
    nlinarith

/-- The core inequality: `(2N/3)² + 26·S/3 + 26·Σ δ ≤ 26·(2N/3)`, with `S = ⟨Σ c, Σ c⟩`. -/
private theorem bound_core {N : ℕ} (P : Fin N → Albert) (hpure : ∀ i, IsPure (P i)) :
    (2 * (N : ℝ) / 3) ^ 2 + 26 * (inner (∑ i, centered (P i)) (∑ i, centered (P i)) / 3) +
      26 * ∑ i, ∑ j, boundDefect P i j ≤ 26 * (2 * (N : ℝ) / 3) := by
  have hdiag : ∑ i, inner (centered (P i)) (centered (P i)) = 2 * (N : ℝ) / 3 := by
    rw [Finset.sum_congr rfl fun i _ => by
      rw [inner_centered (hpure i) (hpure i), inner_self_of_pure (hpure i)]]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hgram := gram_trace_sq_le (fun i => centered (P i)) (fun i => trace_centered (hpure i))
  rw [hdiag] at hgram
  have hS : inner (∑ i, centered (P i)) (∑ i, centered (P i)) =
      ∑ i, ∑ j, inner (centered (P i)) (centered (P j)) := by
    rw [bound_inner_sum_left]
    exact Finset.sum_congr rfl fun i _ => bound_inner_sum_right _ _ _
  have hpt : ∀ i j : Fin N, (inner (centered (P i)) (centered (P j))) ^ 2 =
      (if i = j then (2 / 3 : ℝ) else 0) - (1 / 3 : ℝ) * inner (centered (P i)) (centered (P j)) -
        boundDefect P i j := by
    intro i j; unfold boundDefect; ring
  have hsq : ∑ i, ∑ j, (inner (centered (P i)) (centered (P j))) ^ 2 =
      2 * (N : ℝ) / 3 - (∑ i, ∑ j, inner (centered (P i)) (centered (P j))) / 3 -
        ∑ i, ∑ j, boundDefect P i j := by
    simp only [hpt, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [← Finset.mul_sum]
    ring
  rw [hsq, ← hS] at hgram
  linarith

/-- At `N = 39` the core inequality is an equality: `S = 0` and every defect vanishes. -/
private theorem bound_tight (P : Fin 39 → Albert) (hpure : ∀ i, IsPure (P i))
    (hov : OverlapBound P) :
    inner (∑ i, centered (P i)) (∑ i, centered (P i)) = 0 ∧ ∀ i j, boundDefect P i j = 0 := by
  have hcore := bound_core P hpure
  have hS := Glennie.inner_self_nonneg (∑ i, centered (P i))
  have hDn : ∀ i j, 0 ≤ boundDefect P i j := bound_defect_nonneg P hpure hov
  have hD : 0 ≤ ∑ i, ∑ j, boundDefect P i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hDn i j
  push_cast at hcore
  have hD0 : ∑ i, ∑ j, boundDefect P i j = 0 := by linarith
  refine ⟨by linarith, fun i j => ?_⟩
  have hrow := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => hDn i j).mp hD0 i (Finset.mem_univ i)
  exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hDn i j).mp hrow j (Finset.mem_univ j)

/-- **Code bound.** A family of native pure points with distinct-pair overlaps `≤ 1/3` has at most
`39` members. -/
theorem card_le_39 {N : ℕ} (P : Fin N → Albert) (hpure : ∀ i, IsPure (P i))
    (hov : OverlapBound P) : N ≤ 39 := by
  have hcore := bound_core P hpure
  have hS := Glennie.inner_self_nonneg (∑ i, centered (P i))
  have hD : 0 ≤ ∑ i, ∑ j, boundDefect P i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => bound_defect_nonneg P hpure hov i j
  have hN : (N : ℝ) ≤ 39 := by
    by_contra h
    have h' := not_le.mp h
    nlinarith
  exact_mod_cast hN

/-- At `N = 39`, distinct overlaps take only the values `0` and `1/3`. -/
theorem tight_overlap_values (P : Fin 39 → Albert) (hpure : ∀ i, IsPure (P i))
    (hov : OverlapBound P) :
    ∀ i j, i ≠ j → inner (P i) (P j) = 0 ∨ inner (P i) (P j) = 1 / 3 := by
  intro i j hij
  have h := (bound_tight P hpure hov).2 i j
  unfold boundDefect at h
  rw [inner_centered (hpure i) (hpure j)] at h
  simp only [hij, ↓reduceIte] at h
  have hprod : inner (P i) (P j) * (inner (P i) (P j) - 1 / 3) = 0 := by linear_combination -h
  rcases mul_eq_zero.mp hprod with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linarith)

/-- At `N = 39`, the points sum to `13 • 1`. -/
theorem tight_sum (P : Fin 39 → Albert) (hpure : ∀ i, IsPure (P i)) (hov : OverlapBound P) :
    ∑ i, P i = (13 : ℝ) • (1 : Albert) := by
  have h0 : ∑ i, centered (P i) = 0 :=
    (Glennie.inner_self_eq_zero _).mp (bound_tight P hpure hov).1
  have hc : ∑ i, centered (P i) = ∑ i, P i - (13 : ℝ) • (1 : Albert) := by
    simp only [centered, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    norm_num
  rw [hc] at h0
  exact sub_eq_zero.mp h0

/-- At `N = 39`, every Gram row sums to `13`. -/
theorem tight_row_sum (P : Fin 39 → Albert) (hpure : ∀ i, IsPure (P i)) (hov : OverlapBound P)
    (i : Fin 39) : ∑ j, inner (P i) (P j) = 13 := by
  rw [← bound_inner_sum_right, tight_sum P hpure hov,
    CKM.NativeDerivationTriality.Reuse.inner_smul_right, inner_one_right, (hpure i).2]
  norm_num

#print axioms card_le_39
#print axioms tight_overlap_values
#print axioms tight_sum
#print axioms tight_row_sum

end CKM.NativeTightCode
