module

public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Order.Sub.Prod
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section

/-!
# Counting standard monomials of a monomial ideal 

`cnt G S m` = number of exponent vectors `e : Fin n → ℕ` of total degree `m`, supported in `S`, not divisible by any
`g ∈ G` (divisibility = pointwise `≤`).  Generic lemmas:
* `cnt_split`  : the pivot/colon recursion on a variable `x ∈ S` (exact identity);
* `cnt_mono`   : weakening (dropping / replacing generators by multiples only increases the count);
* `cnt_zero_of_mem` : a generator equal to `1` (exponent `0`) kills everything;
* `cnt_nil_le` : with no generators and `#S ≤ k+1`, the count is at most `C(m+k, k)`.
-/

open Finset

namespace StdCount

variable {n : ℕ}

/-- `e` is supported in `S` and divisible by no `g ∈ G`. -/
def Std (G : List (Fin n → ℕ)) (S : Finset (Fin n)) (e : Fin n → ℕ) : Prop :=
  (∀ i, i ∉ S → e i = 0) ∧ ∀ g ∈ G, ¬ g ≤ e

open Classical in
noncomputable def cnt (G : List (Fin n → ℕ)) (S : Finset (Fin n)) (m : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple n m).filter (Std G S)).card

/-- colon by the variable `x`: `g ↦ g / x` (exponent of `x` decreased, truncated at 0). -/
def colon (x : Fin n) (g : Fin n → ℕ) : Fin n → ℕ := g - Pi.single x 1

theorem cnt_mono {G G' : List (Fin n → ℕ)} {S : Finset (Fin n)} (m : ℕ)
    (h : ∀ g' ∈ G', ∃ g ∈ G, g ≤ g') : cnt G S m ≤ cnt G' S m := by
  classical
  unfold cnt
  apply card_le_card
  intro e he
  simp only [Finset.mem_filter] at he ⊢
  refine ⟨he.1, he.2.1, ?_⟩
  intro g' hg' hle
  obtain ⟨g, hg, hgg'⟩ := h g' hg'
  exact he.2.2 g hg (le_trans hgg' hle)

theorem cnt_zero_of_mem {G : List (Fin n → ℕ)} {S : Finset (Fin n)} (m : ℕ) (h : (0 : Fin n → ℕ) ∈ G) :
    cnt G S m = 0 := by
  classical
  unfold cnt
  rw [card_eq_zero, filter_eq_empty_iff]
  intro e _ hs
  exact hs.2 0 h (fun i => Nat.zero_le _)

private theorem single_le {x : Fin n} {e : Fin n → ℕ} (hx : e x ≠ 0) : (Pi.single x 1 : Fin n → ℕ) ≤ e := by
  intro i
  by_cases hi : i = x
  · subst hi; simp; omega
  · simp [hi]

private theorem sub_add_single {x : Fin n} {e : Fin n → ℕ} (hle : (Pi.single x 1 : Fin n → ℕ) ≤ e) :
    e - Pi.single x 1 + Pi.single x 1 = e := funext fun i => Nat.sub_add_cancel (hle i)

private theorem add_sub_single {x : Fin n} {e : Fin n → ℕ} : e + Pi.single x 1 - Pi.single x 1 = e :=
  funext fun i => by simp

private theorem sum_add_single {x : Fin n} {e : Fin n → ℕ} :
    ∑ i, (e + Pi.single x 1 : Fin n → ℕ) i = ∑ i, e i + 1 := by
  simp [Finset.sum_add_distrib]

theorem cnt_split {G : List (Fin n → ℕ)} {S : Finset (Fin n)} {x : Fin n} (hx : x ∈ S) (m : ℕ) :
    cnt G S (m + 1) = cnt G (S.erase x) (m + 1) + cnt (G.map (colon x)) S m := by
  classical
  unfold cnt
  rw [← card_filter_add_card_filter_not (s := (Finset.Nat.antidiagonalTuple n (m + 1)).filter (Std G S))
    (fun e : Fin n → ℕ => e x = 0)]
  congr 1
  · -- vectors with e x = 0
    apply congrArg Finset.card
    ext e
    simp only [Finset.mem_filter, Std, Finset.mem_erase, ne_eq, not_and]
    constructor
    · rintro ⟨⟨hm, hs, hg⟩, h0⟩
      refine ⟨hm, ?_, hg⟩
      intro i hi
      by_cases hix : i = x
      · subst hix; exact h0
      · exact hs i (fun h => hi hix h)
    · rintro ⟨hm, hs, hg⟩
      refine ⟨⟨hm, ?_, hg⟩, hs x (fun h => absurd rfl h)⟩
      intro i hi
      exact hs i (fun _ h => hi h)
  · -- vectors with e x ≠ 0, shifted down by x
    symm
    apply Finset.card_nbij' (fun e => e + Pi.single x 1) (fun e => e - Pi.single x 1)
    · intro e he
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple, Std,
        List.mem_map] at he ⊢
      obtain ⟨hm, hs, hg⟩ := he
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · rw [sum_add_single, hm]
      · intro i hi
        have hix : i ≠ x := fun h => hi (h ▸ hx)
        simp [hs i hi, hix]
      · intro g hgG hle
        refine hg (colon x g) ⟨g, hgG, rfl⟩ ?_
        unfold colon
        exact tsub_le_iff_right.mpr hle
      · simp
    · intro e he
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple, Std,
        List.mem_map] at he ⊢
      obtain ⟨⟨hm, hs, hg⟩, h0⟩ := he
      have hle := single_le h0
      have hsum : (∑ i, (e - Pi.single x 1 : Fin n → ℕ) i) + 1 = m + 1 := by
        rw [← sum_add_single, sub_add_single hle, hm]
      refine ⟨by omega, ?_, ?_⟩
      · intro i hi
        simp [hs i hi]
      · rintro g' ⟨g, hgG, rfl⟩ hle'
        apply hg g hgG
        unfold colon at hle'
        have := tsub_le_iff_right.mp hle'
        rwa [sub_add_single hle] at this
    · intro e _
      exact add_sub_single
    · intro e he
      simp only [Finset.mem_coe, Finset.mem_filter] at he
      exact sub_add_single (single_le he.2)

theorem cnt_zero_eq {G : List (Fin n → ℕ)} {S : Finset (Fin n)} {x : Fin n} :
    cnt G S 0 = cnt G (S.erase x) 0 := by
  classical
  unfold cnt
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple, Std, Finset.mem_erase, ne_eq, not_and]
  constructor
  · rintro ⟨hm, hs, hg⟩
    have he : ∀ i, e i = 0 := fun i => (Finset.sum_eq_zero_iff.mp hm) i (mem_univ i)
    exact ⟨hm, fun i _ => he i, hg⟩
  · rintro ⟨hm, hs, hg⟩
    exact ⟨hm, fun i hi => hs i (fun _ h => hi h), hg⟩

theorem cnt_le_one_zero (G : List (Fin n → ℕ)) (S : Finset (Fin n)) : cnt G S 0 ≤ 1 := by
  classical
  unfold cnt
  calc _ ≤ (Finset.Nat.antidiagonalTuple n 0).card := card_filter_le _ _
    _ = 1 := by simp [Finset.Nat.antidiagonalTuple_zero_right]

theorem cnt_empty_succ (G : List (Fin n → ℕ)) (m : ℕ) : cnt G ∅ (m + 1) = 0 := by
  classical
  unfold cnt
  rw [card_eq_zero, filter_eq_empty_iff]
  intro e he hs
  rw [Finset.Nat.mem_antidiagonalTuple] at he
  have : ∑ i, e i = 0 := Finset.sum_eq_zero (fun i _ => hs.1 i (Finset.notMem_empty i))
  omega

/-- free count: with no generators and `#S ≤ k + 1`, at most `C(m+k, k)` vectors. -/
theorem cnt_nil_le : ∀ (k : ℕ) (S : Finset (Fin n)), S.card ≤ k + 1 → ∀ m, cnt [] S m ≤ (m + k).choose k := by
  intro k
  induction k with
  | zero =>
    intro S hS m
    cases m with
    | zero => simpa using cnt_le_one_zero [] S
    | succ m =>
      rcases Finset.card_le_one.mp (by omega : S.card ≤ 1) with h
      by_cases hSe : S = ∅
      · subst hSe; rw [cnt_empty_succ]; exact Nat.zero_le _
      · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hSe
        have hE : S.erase x = ∅ := by
          ext y; simp only [mem_erase, Finset.notMem_empty, iff_false, not_and]
          intro hyx hy; exact hyx (h y hy x hx)
        -- induct on m for the singleton
        have key : ∀ m, cnt [] S m ≤ 1 := by
          intro m
          induction m with
          | zero => exact cnt_le_one_zero [] S
          | succ m ih =>
            rw [cnt_split hx, hE, cnt_empty_succ]; simpa using ih
        simpa using key (m + 1)
  | succ k ihk =>
    intro S hS m
    induction m with
    | zero => simpa using cnt_le_one_zero [] S
    | succ m ihm =>
      by_cases hSe : S = ∅
      · subst hSe; rw [cnt_empty_succ]; exact Nat.zero_le _
      · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hSe
        rw [cnt_split hx]
        have h1 : (S.erase x).card ≤ k + 1 := by rw [Finset.card_erase_of_mem hx]; omega
        have := ihk (S.erase x) h1 (m + 1)
        simp only [List.map_nil]
        calc cnt [] (S.erase x) (m + 1) + cnt [] S m ≤ (m + 1 + k).choose k + (m + (k + 1)).choose (k + 1) :=
              Nat.add_le_add this ihm
          _ = (m + 1 + (k + 1)).choose (k + 1) := by
              rw [show m + 1 + (k + 1) = (m + k + 1) + 1 by omega, Nat.choose_succ_succ',
                show m + 1 + k = m + k + 1 by omega, show m + (k + 1) = m + k + 1 by omega]

end StdCount
