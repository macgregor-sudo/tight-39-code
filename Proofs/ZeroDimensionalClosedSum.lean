module
public import ClosedStratumSeparation

/-! The countable closed-sum theorem in dimension zero, proved by successive
absorption of the closed strata. No higher-dimensional sum theorem is used. -/
@[expose] public section
noncomputable section
namespace SmallInductiveClosedSum
open Set Topology TopologicalSpace
variable {X : Type*} [TopologicalSpace X]

/-- An open pair whose closures remain disjoint during the recursion. -/
structure SeparatedOpenPair (X : Type*) [TopologicalSpace X] where
  left : Set X
  right : Set X
  left_open : IsOpen left
  right_open : IsOpen right
  separated : Disjoint (closure left) (closure right)

variable [NormalSpace X] [SecondCountableTopology X]

/-- Arbitrary disjoint closed sets have a clopen separator when a countable
closed cover consists of zero-dimensional subspaces. -/
theorem zero_dimensional_closed_cover_separator
    (F : ℕ → Set X) (hF : ∀ n, IsClosed (F n))
    (hdim : ∀ n, HasSmallInductiveDimensionLE ↥(F n) 0)
    (hcover : (⋃ n, F n) = univ)
    (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
    ∃ C : Set X, IsClopen C ∧ A ⊆ C ∧ C ⊆ Bᶜ := by
  classical
  obtain ⟨U₀,V₀,hU₀,hV₀,hAU₀,hBV₀,hUV₀⟩ :=
    normal_separation_disjoint_closures A B hA hB hAB
  let p₀ : SeparatedOpenPair X := ⟨U₀,V₀,hU₀,hV₀,hUV₀⟩
  have hn : ∀ n (p : SeparatedOpenPair X), ∃ q : SeparatedOpenPair X,
      closure p.left ⊆ q.left ∧ closure p.right ⊆ q.right ∧ F n ⊆ q.left ∪ q.right := by
    intro n p
    obtain ⟨U,V,hU,hV,hLU,hRV,hFUV,hUV⟩ := absorb_closed_zero_dimensional
      (F n) (hF n) (hdim n) (closure p.left) (closure p.right)
      isClosed_closure isClosed_closure p.separated
    exact ⟨⟨U,V,hU,hV,hUV⟩,hLU,hRV,hFUV⟩
  choose next hnext using hn
  let P : ℕ → SeparatedOpenPair X := Nat.rec p₀ (fun n p => next n p)
  have hstep (n : ℕ) : closure (P n).left ⊆ (P (n+1)).left ∧
      closure (P n).right ⊆ (P (n+1)).right ∧ F n ⊆ (P (n+1)).left ∪ (P (n+1)).right :=
    hnext n (P n)
  have hmonoL : Monotone (fun n => (P n).left) :=
    monotone_nat_of_le_succ fun n => subset_closure.trans (hstep n).1
  have hmonoR : Monotone (fun n => (P n).right) :=
    monotone_nat_of_le_succ fun n => subset_closure.trans (hstep n).2.1
  let U : Set X := ⋃ n, (P n).left
  let V : Set X := ⋃ n, (P n).right
  have hU : IsOpen U := isOpen_iUnion fun n => (P n).left_open
  have hV : IsOpen V := isOpen_iUnion fun n => (P n).right_open
  have hUV : Disjoint U V := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hy
    exact disjoint_left.mp (P (max i j)).separated
      (subset_closure (hmonoL (le_max_left i j) hi))
      (subset_closure (hmonoR (le_max_right i j) hj))
  have hfull : U ∪ V = univ := by
    apply eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ n, F n := by rw [hcover]; trivial
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    rcases (hstep n).2.2 hn with hl | hr
    · exact Or.inl (mem_iUnion.mpr ⟨n+1,hl⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨n+1,hr⟩)
  have hcomp : Uᶜ = V := by
    ext x
    constructor
    · intro hx
      have hf : x ∈ U ∪ V := by rw [hfull]; trivial
      exact hf.resolve_left hx
    · intro hx hu
      exact disjoint_left.mp hUV hu hx
  refine ⟨U,⟨?_,hU⟩,?_,?_⟩
  · rw [← isOpen_compl_iff,hcomp]
    exact hV
  · intro x hx
    exact mem_iUnion.mpr ⟨0,hAU₀ hx⟩
  · intro x hx hb
    exact disjoint_left.mp hUV hx (mem_iUnion.mpr ⟨0,hBV₀ hb⟩)

/-- Countable closed sums preserve small inductive dimension at most zero.
Normality, second countability and T₁ suffice; in particular this covers every
second-countable metric space, including empty strata and an empty space. -/
theorem zero_dimensional_countable_closed_sum [T1Space X]
    (F : ℕ → Set X) (hF : ∀ n, IsClosed (F n))
    (hdim : ∀ n, HasSmallInductiveDimensionLE ↥(F n) 0)
    (hcover : (⋃ n, F n) = univ) : HasSmallInductiveDimensionLE X 0 := by
  apply hasSmallInductiveDimensionLT_one_iff.mpr
  apply isTopologicalBasis_of_isOpen_of_nhds (fun _ h => h.isOpen)
  intro x O hx hO
  have hd : Disjoint ({x} : Set X) Oᶜ := by
    exact disjoint_left.mpr (fun y hy hn => hn (mem_singleton_iff.mp hy ▸ hx))
  obtain ⟨C,hC,hxC,hCO⟩ := zero_dimensional_closed_cover_separator F hF hdim hcover
    {x} Oᶜ isClosed_singleton hO.isClosed_compl hd
  exact ⟨C,hC,hxC (mem_singleton x),by simpa only [compl_compl] using hCO⟩

end SmallInductiveClosedSum
#print axioms SmallInductiveClosedSum.zero_dimensional_countable_closed_sum
