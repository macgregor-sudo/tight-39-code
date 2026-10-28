module

public import FreeVariables
public import ChainMidCount

@[expose] public section

/-!
# CHAINMID prototype: steps 4–5 + Vandermonde assembled (generic field, no data)

From (i) a pivoted 80-dimensional slice `B` with `L·B = 0` and `rank L ≥ n − 80`,
(ii) a coordinate change `M : 80 → 56 ⊕ 24` with right inverse `N` (`M * N = 1`),
(iii) forms `t` in the 24 `x`-variables whose images lie in the span of the transformed restricted quadrics,
(iv) a per-degree bound `h(m) ≤ 4·C(m+5,5) + 1540·C(m+4,4)` for `K[x₁..x₂₄]/(t)`,
we get the cumulative bound on the uncut relation quotients consumed by
`equationJet_finrank_le_cumulative_relations`:
`∑_{d≤N} finrank (equationCutPiece g E w [] d) ≤ 4·C(N+62,62) + 1540·C(N+61,61)`.
-/

open MvPolynomial Module Finset PolynomialJets SliceLemmas

namespace ChainMid

variable {K : Type*} [Field K] {n : ℕ} {ι ε κ κ' : Type*} [Fintype ι]

theorem restrictedQuadric_isHomogeneous {m : ℕ} (B : Matrix (Fin n) (Fin m) K)
    (g : ι → MvPolynomial (Fin n) K) (w : κ → ι → K) (s : κ) :
    (restrictedQuadric B g w s).IsHomogeneous 2 :=
  restrict_isHomogeneous B (equationAnnihilatorQuadric_isHomogeneous g (w s))

/-- Per-degree form of steps 4–5. -/
theorem finrank_equationCutPiece_le_convolution {B : Matrix (Fin n) (Fin 80) K}
    {piv : Fin 80 → Fin n} (hB : IsPivot B piv) (g : ι → MvPolynomial (Fin n) K) (E : ε → ι)
    (w : κ → ι → K) (hvanish : cutLinearSpace g E [] ≤ linearAnnihilator B)
    (hdim : n - 80 ≤ finrank K (cutLinearSpace g E []))
    (M : Matrix (Fin 80) (Fin 56 ⊕ Fin 24) K) (N : Matrix (Fin 56 ⊕ Fin 24) (Fin 80) K)
    (hMN : M * N = 1) (t : κ' → MvPolynomial (Fin 24) K) (ht : ∀ k, (t k).IsHomogeneous 2)
    (htspan : ∀ k, rename (Sum.inr : Fin 24 → Fin 56 ⊕ Fin 24) (t k) ∈
      Submodule.span K (Set.range fun s => linSubst M (restrictedQuadric B g w s))) (d : ℕ) :
    finrank K (equationCutPiece g E w [] d) ≤
      ∑ ij ∈ antidiagonal d,
        finrank K (homogeneousSubmodule (Fin 24) K ij.1 ⧸ quadricRelations t ij.1) *
          (ij.2 + 55).choose 55 := by
  rw [finrank_equationCutPiece_nil_eq hB g E w hvanish hdim d]
  refine (finrank_quotient_le_of_linSubst M N hMN _ (restrictedQuadric_isHomogeneous B g w)
    (fun k => rename Sum.inr (t k)) htspan d).trans ?_
  refine (finrank_quotient_free_le (τc := Fin 56) ht d).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [finrank_homogeneousSubmodule, Nat.multichoose_eq,
    show 56 + ij.2 - 1 = ij.2 + 55 by omega, Nat.choose_symm_add]

/-- Cumulative form, the shape consumed by the jet chain (`cumulative f N = ∑_{d ≤ N} f d`). -/
theorem cumulative_equationCutPiece_le {B : Matrix (Fin n) (Fin 80) K}
    {piv : Fin 80 → Fin n} (hB : IsPivot B piv) (g : ι → MvPolynomial (Fin n) K) (E : ε → ι)
    (w : κ → ι → K) (hvanish : cutLinearSpace g E [] ≤ linearAnnihilator B)
    (hdim : n - 80 ≤ finrank K (cutLinearSpace g E []))
    (M : Matrix (Fin 80) (Fin 56 ⊕ Fin 24) K) (N : Matrix (Fin 56 ⊕ Fin 24) (Fin 80) K)
    (hMN : M * N = 1) (t : κ' → MvPolynomial (Fin 24) K) (ht : ∀ k, (t k).IsHomogeneous 2)
    (htspan : ∀ k, rename (Sum.inr : Fin 24 → Fin 56 ⊕ Fin 24) (t k) ∈
      Submodule.span K (Set.range fun s => linSubst M (restrictedQuadric B g w s)))
    (hh : ∀ m, finrank K (homogeneousSubmodule (Fin 24) K m ⧸ quadricRelations t m) ≤
      4 * (m + 5).choose 5 + 1540 * (m + 4).choose 4) (N0 : ℕ) :
    HilbertFunctions.JetBounds.cumulative
        (fun d => finrank K (equationCutPiece g E w [] d)) N0 ≤
      4 * (N0 + 62).choose 62 + 1540 * (N0 + 61).choose 61 := by
  unfold HilbertFunctions.JetBounds.cumulative
  exact (Finset.sum_le_sum fun d _ =>
    finrank_equationCutPiece_le_convolution hB g E w hvanish hdim M N hMN t ht htspan d).trans
    (cumulative_convolution_bound _ hh N0)

end ChainMid
