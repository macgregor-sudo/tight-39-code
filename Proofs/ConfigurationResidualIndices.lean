/-
# Canonical indices for the two configuration residual families

Strict unordered pairs are enumerated in lexicographic order, by separating
the pairs beginning with zero and recursively shifting the remaining pairs.
The two residual row families are then explicit sums and products of finite
types. Their equivalences retain the original point-first coordinate order,
all 741 lexicographic F pairs, and all 78 lexicographic G frame pairs.

This first-party index adapter implements the typed-row indexing. It
does not define residual polynomials or prove any native equation, ideal or
certificate identity. No enumeration table, default lookup or cardinality-only
equivalence is used. The small grouped-order controls distinguish an earlier
sample checker's within-first order from the canonical original F row order.

Imported finite-equivalence and finite-sum results are from mathlib:
https://github.com/leanprover-community/mathlib4,
commit 065356127b1dc0016f66b7283ce0ce2c4055aa55, Apache-2.0.
No upstream proof body is copied. Thanks to mathlib's contributors for these
standard results. No release license is assigned to new first-party code.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
Quotation source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/
module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section
set_option backward.proofsInPublic true

namespace ConfigurationResidualIndices

open scoped BigOperators

/-- An unordered pair, stored in its increasing orientation. -/
abbrev Pair (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}

theorem pair_zero_elim (p : Pair 0) : False := Fin.elim0 p.val.1

theorem pair_one_elim (p : Pair 1) : False := by
  have hi := p.val.1.isLt
  have hj := p.val.2.isLt
  have hp := p.property
  change p.val.1.val < p.val.2.val at hp
  omega

/-- The size of the strict upper triangle, using the lexicographic recursion. -/
def triangular : ℕ → ℕ
  | 0 => 0
  | n + 1 => n + triangular n

/-- The first block of pairs: `(0,j+1)`. -/
def pairZero {n : ℕ} (j : Fin n) : Pair (n + 1) :=
  ⟨(0, j.succ), by change 0 < j.val + 1; omega⟩

/-- Shift both entries of an increasing pair by one. -/
def pairSucc {n : ℕ} (p : Pair n) : Pair (n + 1) :=
  ⟨(p.val.1.succ, p.val.2.succ), by
    change p.val.1.val + 1 < p.val.2.val + 1
    have hp := p.property
    change p.val.1.val < p.val.2.val at hp
    omega⟩

/-- Separate the first lexicographic block from the shifted smaller triangle. -/
def pairSeparate (n : ℕ) (p : Pair (n + 1)) : Fin n ⊕ Pair n :=
  if h : p.val.1.val = 0 then
    .inl ⟨p.val.2.val - 1, by
      have hj := p.val.2.isLt
      have hp := p.property
      change p.val.1.val < p.val.2.val at hp
      omega⟩
  else
    .inr ⟨(⟨p.val.1.val - 1, by have hi := p.val.1.isLt; omega⟩,
      ⟨p.val.2.val - 1, by have hj := p.val.2.isLt; omega⟩), by
        change p.val.1.val - 1 < p.val.2.val - 1
        have hp := p.property
        change p.val.1.val < p.val.2.val at hp
        omega⟩

/-- Reassemble the two lexicographic blocks, without any default case. -/
def pairAssemble (n : ℕ) : Fin n ⊕ Pair n → Pair (n + 1)
  | .inl j => pairZero j
  | .inr p => pairSucc p

def pairSeparate_pairZero (n : ℕ) (j : Fin n) :
    pairSeparate n (pairZero j) = .inl j := by
  unfold pairSeparate pairZero
  simp only [Fin.val_zero]
  congr 1

def pairSeparate_pairSucc (n : ℕ) (p : Pair n) :
    pairSeparate n (pairSucc p) = .inr p := by
  unfold pairSeparate pairSucc
  have h : p.val.1.val + 1 ≠ 0 := by omega
  simp only [Fin.val_succ, h]
  congr 1

def pairAssemble_separate (n : ℕ) (p : Pair (n + 1)) :
    pairAssemble n (pairSeparate n p) = p := by
  unfold pairSeparate
  split_ifs with h
  · dsimp only [pairAssemble, pairZero]
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · exact h.symm
    · change p.val.2.val - 1 + 1 = p.val.2.val
      have hp := p.property
      change p.val.1.val < p.val.2.val at hp
      omega
  · dsimp only [pairAssemble, pairSucc]
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · change p.val.1.val - 1 + 1 = p.val.1.val
      omega
    · change p.val.2.val - 1 + 1 = p.val.2.val
      have hp := p.property
      change p.val.1.val < p.val.2.val at hp
      omega

/-- The structural split of increasing pairs, including empty summands. -/
def pairSplit (n : ℕ) : Pair (n + 1) ≃ Fin n ⊕ Pair n where
  toFun := pairSeparate n
  invFun := pairAssemble n
  left_inv := pairAssemble_separate n
  right_inv := by
    rintro (j | p)
    · exact pairSeparate_pairZero n j
    · exact pairSeparate_pairSucc n p

/-- The pair rank, defined by its lexicographic blocks, rather than cardinality. -/
def pairRank : (n : ℕ) → Pair n ≃ Fin (triangular n)
  | 0 =>
    { toFun := fun p => Fin.elim0 p.val.1
      invFun := Fin.elim0
      left_inv := fun p => Fin.elim0 p.val.1
      right_inv := fun i => Fin.elim0 i }
  | n + 1 =>
    (pairSplit n).trans
      ((Equiv.sumCongr (Equiv.refl (Fin n)) (pairRank n)).trans finSumFinEquiv)

theorem pairRank_pairZero (n : ℕ) (j : Fin n) :
    pairRank (n + 1) (pairZero j) = Fin.castAdd (triangular n) j := by
  change finSumFinEquiv
    ((Equiv.sumCongr (Equiv.refl (Fin n)) (pairRank n))
      (pairSeparate n (pairZero j))) = _
  rw [pairSeparate_pairZero]
  rfl

theorem pairRank_pairSucc (n : ℕ) (p : Pair n) :
    pairRank (n + 1) (pairSucc p) = Fin.natAdd n (pairRank n p) := by
  change finSumFinEquiv
    ((Equiv.sumCongr (Equiv.refl (Fin n)) (pairRank n))
      (pairSeparate n (pairSucc p))) = _
  rw [pairSeparate_pairSucc]
  rfl

/-- Literal `combinations(range(n),2)` rank: preceding rows plus within-row offset. -/
def lexRank (n : ℕ) (i j : Fin n) : ℕ :=
  Finset.sum (Finset.range i.val) (fun r => n - 1 - r) + (j.val - i.val - 1)

theorem lexRank_zero (n : ℕ) (j : Fin (n + 1)) :
    lexRank (n + 1) 0 j = j.val - 1 := by
  simp [lexRank]

theorem lexRank_succ (n : ℕ) (i j : Fin n) :
    lexRank (n + 1) i.succ j.succ = n + lexRank n i j := by
  unfold lexRank
  simp only [Fin.val_succ]
  rw [Finset.sum_range_succ']
  have hs : Finset.sum (Finset.range i.val) (fun r => n + 1 - 1 - (r + 1)) =
      Finset.sum (Finset.range i.val) (fun r => n - 1 - r) := by
    apply Finset.sum_congr rfl
    intro r hr
    omega
  rw [hs]
  omega

/-- The recursive equivalence has exactly the literal pair-rank formula. -/
theorem pairRank_val (n : ℕ) (p : Pair n) :
    (pairRank n p).val = lexRank n p.val.1 p.val.2 := by
  induction n with
  | zero => exact Fin.elim0 p.val.1
  | succ n ih =>
    rcases h : pairSeparate n p with j | q
    · have hp : pairZero j = p := by
        have hp := pairAssemble_separate n p
        rw [h] at hp
        exact hp
      rw [← hp, pairRank_pairZero]
      simp [lexRank, pairZero]
    · have hp : pairSucc q = p := by
        have hp := pairAssemble_separate n p
        rw [h] at hp
        exact hp
      rw [← hp, pairRank_pairSucc]
      change n + (pairRank n q).val = lexRank (n + 1) q.val.1.succ q.val.2.succ
      rw [ih, lexRank_succ]

theorem triangular_thirteen : triangular 13 = 78 := rfl
theorem triangular_thirtyNine : triangular 39 = 741 := rfl

/-- The literal within-frame pair order `(0,1),(0,2),(1,2)`. -/
def withinPair : Fin 3 ≃ Pair 3 := (pairRank 3).symm

theorem withinPair_zero : withinPair 0 = ⟨(0, 1), by decide⟩ := by
  apply (pairRank 3).injective
  rw [show pairRank 3 (withinPair 0) = (0 : Fin 3) from (pairRank 3).apply_symm_apply (0 : Fin 3)]
  apply Fin.ext
  rfl

theorem withinPair_one : withinPair 1 = ⟨(0, 2), by decide⟩ := by
  apply (pairRank 3).injective
  rw [show pairRank 3 (withinPair 1) = (1 : Fin 3) from (pairRank 3).apply_symm_apply (1 : Fin 3)]
  apply Fin.ext
  rfl

theorem withinPair_two : withinPair 2 = ⟨(1, 2), by decide⟩ := by
  apply (pairRank 3).injective
  rw [show pairRank 3 (withinPair 2) = (2 : Fin 3) from (pairRank 3).apply_symm_apply (2 : Fin 3)]
  apply Fin.ext
  rfl

abbrev IdRow := Fin 39 × Fin 27
abbrev TraceRow := Fin 39
abbrev SumRow := Fin 13 × Fin 27
abbrev WithinRow := (Fin 13 × Fin 3) × Fin 27
abbrev CrossRow := Pair 13 × (Fin 3 × Fin 3)
abbrev FLabel := IdRow ⊕ (TraceRow ⊕ (SumRow ⊕ Pair 39))
abbrev GLabel := IdRow ⊕ (WithinRow ⊕ (SumRow ⊕ CrossRow))

/-- Point-first within-frame product coordinate: `k+27*(s+3*f)`. -/
def withinNumber : WithinRow ≃ Fin 1053 :=
  (Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin 27))).trans finProdFinEquiv

/-- Lexicographic frame pair, then point pair: `b+3*a+9*L13(f,g)`. -/
def crossNumber : CrossRow ≃ Fin 702 :=
  (Equiv.prodCongr (pairRank 13) finProdFinEquiv).trans finProdFinEquiv

/-- Original F blocks: idempotency, trace, sum and all lexicographic point pairs. -/
def fNumber : FLabel ≃ Fin 2184 :=
  (Equiv.sumCongr finProdFinEquiv
    ((Equiv.sumCongr (Equiv.refl (Fin 39))
      ((Equiv.sumCongr finProdFinEquiv (pairRank 39)).trans finSumFinEquiv)).trans
      finSumFinEquiv)).trans finSumFinEquiv

/-- Original G blocks: idempotency, within product, sum and cross-frame overlaps. -/
def gNumber : GLabel ≃ Fin 3159 :=
  (Equiv.sumCongr finProdFinEquiv
    ((Equiv.sumCongr withinNumber
      ((Equiv.sumCongr finProdFinEquiv crossNumber).trans finSumFinEquiv)).trans
      finSumFinEquiv)).trans finSumFinEquiv

def fId (i : Fin 39) (k : Fin 27) : FLabel := .inl (i, k)
def fTrace (i : Fin 39) : FLabel := .inr (.inl i)
def fSum (f : Fin 13) (k : Fin 27) : FLabel := .inr (.inr (.inl (f, k)))
def fPair (p : Pair 39) : FLabel := .inr (.inr (.inr p))
def gId (i : Fin 39) (k : Fin 27) : GLabel := .inl (i, k)
def gWithin (f : Fin 13) (s : Fin 3) (k : Fin 27) : GLabel :=
  .inr (.inl ((f, s), k))
def gSum (f : Fin 13) (k : Fin 27) : GLabel := .inr (.inr (.inl (f, k)))
def gCross (p : Pair 13) (a b : Fin 3) : GLabel := .inr (.inr (.inr (p, (a, b))))

theorem fNumber_id_val (i : Fin 39) (k : Fin 27) :
    (fNumber (fId i k)).val = 27 * i.val + k.val := by
  change k.val + 27 * i.val = _
  omega

theorem fNumber_trace_val (i : Fin 39) :
    (fNumber (fTrace i)).val = 1053 + i.val := rfl

theorem fNumber_sum_val (f : Fin 13) (k : Fin 27) :
    (fNumber (fSum f k)).val = 1092 + 27 * f.val + k.val := by
  change 1053 + (39 + (k.val + 27 * f.val)) = _
  omega

theorem fNumber_pair_val (p : Pair 39) :
    (fNumber (fPair p)).val = 1443 + lexRank 39 p.val.1 p.val.2 := by
  change 1053 + (39 + (351 + (pairRank 39 p).val)) = _
  rw [pairRank_val]
  omega

theorem gNumber_id_val (i : Fin 39) (k : Fin 27) :
    (gNumber (gId i k)).val = 27 * i.val + k.val := by
  change k.val + 27 * i.val = _
  omega

theorem gNumber_within_val (f : Fin 13) (s : Fin 3) (k : Fin 27) :
    (gNumber (gWithin f s k)).val = 1053 + 81 * f.val + 27 * s.val + k.val := by
  change 1053 + (k.val + 27 * (s.val + 3 * f.val)) = _
  omega

theorem gNumber_sum_val (f : Fin 13) (k : Fin 27) :
    (gNumber (gSum f k)).val = 2106 + 27 * f.val + k.val := by
  change 1053 + (1053 + (k.val + 27 * f.val)) = _
  omega

theorem gNumber_cross_val (p : Pair 13) (a b : Fin 3) :
    (gNumber (gCross p a b)).val =
      2457 + 9 * lexRank 13 p.val.1 p.val.2 + 3 * a.val + b.val := by
  change 1053 + (1053 + (351 + (b.val + 3 * a.val + 9 * (pairRank 13 p).val))) = _
  rw [pairRank_val]
  omega

/-- Expose a numbered row API from a typed family with no missing/default row. -/
def fRow {S : Type*} (F : FLabel → S) (r : Fin 2184) : S := F (fNumber.symm r)
def gRow {S : Type*} (G : GLabel → S) (r : Fin 3159) : S := G (gNumber.symm r)

theorem fRow_number {S : Type*} (F : FLabel → S) (r : FLabel) :
    fRow F (fNumber r) = F r := congrArg F (fNumber.symm_apply_apply r)

theorem gRow_number {S : Type*} (G : GLabel → S) (r : GLabel) :
    gRow G (gNumber r) = G r := congrArg G (gNumber.symm_apply_apply r)

theorem gNumber_first_within (k : Fin 27) :
    (gNumber (gWithin 0 0 k)).val = 1053 + k.val := by
  simpa using gNumber_within_val 0 0 k

theorem gNumber_frame_one_sum (k : Fin 27) :
    (gNumber (gSum 1 k)).val = 2133 + k.val := by
  have h := gNumber_sum_val 1 k
  change (gNumber (gSum 1 k)).val = 2133 + k.val
  omega

theorem fNumber_first_trace : fNumber (fTrace 0) = (1053 : Fin 2184) := rfl

theorem gNumber_first_cross (b : Fin 3) :
    (gNumber (gCross ⟨(0, 1), by decide⟩ 0 b)).val = 2457 + b.val := by
  have h := gNumber_cross_val ⟨(0, 1), by decide⟩ 0 b
  simpa [lexRank] using h

/-- Canonical F row 1445 is `(0,3)`, not the sample checker's third within pair. -/
theorem canonical_pair_zero_three :
    fNumber (fPair ⟨(0, 3), by decide⟩) = (1445 : Fin 2184) := by decide

/-- The earlier grouped row 1445 is pair `(1,2)` and therefore canonical row 1481. -/
theorem grouped_within_1445_to_canonical :
    fNumber (fPair ⟨(1, 2), by decide⟩) = (1481 : Fin 2184) := by decide

/-- Include the first frame's literal increasing point pair in the 39 point labels. -/
def firstFramePair (p : Pair 3) : Pair 39 :=
  ⟨(⟨p.val.1.val, by have hi := p.val.1.isLt; omega⟩,
    ⟨p.val.2.val, by have hj := p.val.2.isLt; omega⟩), p.property⟩

/-- Grouped row `1443+2` uses the third literal within pair and maps to 1481. -/
theorem grouped_first_frame_third_pair :
    fNumber (fPair (firstFramePair (withinPair 2))) = (1481 : Fin 2184) := by
  rw [withinPair_two]
  exact grouped_within_1445_to_canonical

theorem canonical_1445_inverse :
    fNumber.symm (1445 : Fin 2184) = fPair ⟨(0, 3), by decide⟩ := by
  rw [← canonical_pair_zero_three]
  exact fNumber.symm_apply_apply _

end ConfigurationResidualIndices

/- Public-boundary consumer of the canonical F/G row indices. -/


#check ConfigurationResidualIndices.Pair
#print axioms ConfigurationResidualIndices.Pair
#check ConfigurationResidualIndices.pair_zero_elim
#print axioms ConfigurationResidualIndices.pair_zero_elim
#check ConfigurationResidualIndices.pair_one_elim
#print axioms ConfigurationResidualIndices.pair_one_elim
#check ConfigurationResidualIndices.triangular
#print axioms ConfigurationResidualIndices.triangular
#check ConfigurationResidualIndices.pairZero
#print axioms ConfigurationResidualIndices.pairZero
#check ConfigurationResidualIndices.pairSucc
#print axioms ConfigurationResidualIndices.pairSucc
#check ConfigurationResidualIndices.pairSeparate
#print axioms ConfigurationResidualIndices.pairSeparate
#check ConfigurationResidualIndices.pairAssemble
#print axioms ConfigurationResidualIndices.pairAssemble
#check ConfigurationResidualIndices.pairSeparate_pairZero
#print axioms ConfigurationResidualIndices.pairSeparate_pairZero
#check ConfigurationResidualIndices.pairSeparate_pairSucc
#print axioms ConfigurationResidualIndices.pairSeparate_pairSucc
#check ConfigurationResidualIndices.pairAssemble_separate
#print axioms ConfigurationResidualIndices.pairAssemble_separate
#check ConfigurationResidualIndices.pairSplit
#print axioms ConfigurationResidualIndices.pairSplit
#check ConfigurationResidualIndices.pairRank
#print axioms ConfigurationResidualIndices.pairRank
#check ConfigurationResidualIndices.pairRank_pairZero
#print axioms ConfigurationResidualIndices.pairRank_pairZero
#check ConfigurationResidualIndices.pairRank_pairSucc
#print axioms ConfigurationResidualIndices.pairRank_pairSucc
#check ConfigurationResidualIndices.lexRank
#print axioms ConfigurationResidualIndices.lexRank
#check ConfigurationResidualIndices.lexRank_zero
#print axioms ConfigurationResidualIndices.lexRank_zero
#check ConfigurationResidualIndices.lexRank_succ
#print axioms ConfigurationResidualIndices.lexRank_succ
#check ConfigurationResidualIndices.pairRank_val
#print axioms ConfigurationResidualIndices.pairRank_val
#check ConfigurationResidualIndices.triangular_thirteen
#print axioms ConfigurationResidualIndices.triangular_thirteen
#check ConfigurationResidualIndices.triangular_thirtyNine
#print axioms ConfigurationResidualIndices.triangular_thirtyNine
#check ConfigurationResidualIndices.withinPair
#print axioms ConfigurationResidualIndices.withinPair
#check ConfigurationResidualIndices.withinPair_zero
#print axioms ConfigurationResidualIndices.withinPair_zero
#check ConfigurationResidualIndices.withinPair_one
#print axioms ConfigurationResidualIndices.withinPair_one
#check ConfigurationResidualIndices.withinPair_two
#print axioms ConfigurationResidualIndices.withinPair_two
#check ConfigurationResidualIndices.IdRow
#print axioms ConfigurationResidualIndices.IdRow
#check ConfigurationResidualIndices.TraceRow
#print axioms ConfigurationResidualIndices.TraceRow
#check ConfigurationResidualIndices.SumRow
#print axioms ConfigurationResidualIndices.SumRow
#check ConfigurationResidualIndices.WithinRow
#print axioms ConfigurationResidualIndices.WithinRow
#check ConfigurationResidualIndices.CrossRow
#print axioms ConfigurationResidualIndices.CrossRow
#check ConfigurationResidualIndices.FLabel
#print axioms ConfigurationResidualIndices.FLabel
#check ConfigurationResidualIndices.GLabel
#print axioms ConfigurationResidualIndices.GLabel
#check ConfigurationResidualIndices.withinNumber
#print axioms ConfigurationResidualIndices.withinNumber
#check ConfigurationResidualIndices.crossNumber
#print axioms ConfigurationResidualIndices.crossNumber
#check ConfigurationResidualIndices.fNumber
#print axioms ConfigurationResidualIndices.fNumber
#check ConfigurationResidualIndices.gNumber
#print axioms ConfigurationResidualIndices.gNumber
#check ConfigurationResidualIndices.fId
#print axioms ConfigurationResidualIndices.fId
#check ConfigurationResidualIndices.fTrace
#print axioms ConfigurationResidualIndices.fTrace
#check ConfigurationResidualIndices.fSum
#print axioms ConfigurationResidualIndices.fSum
#check ConfigurationResidualIndices.fPair
#print axioms ConfigurationResidualIndices.fPair
#check ConfigurationResidualIndices.gId
#print axioms ConfigurationResidualIndices.gId
#check ConfigurationResidualIndices.gWithin
#print axioms ConfigurationResidualIndices.gWithin
#check ConfigurationResidualIndices.gSum
#print axioms ConfigurationResidualIndices.gSum
#check ConfigurationResidualIndices.gCross
#print axioms ConfigurationResidualIndices.gCross
#check ConfigurationResidualIndices.fNumber_id_val
#print axioms ConfigurationResidualIndices.fNumber_id_val
#check ConfigurationResidualIndices.fNumber_trace_val
#print axioms ConfigurationResidualIndices.fNumber_trace_val
#check ConfigurationResidualIndices.fNumber_sum_val
#print axioms ConfigurationResidualIndices.fNumber_sum_val
#check ConfigurationResidualIndices.fNumber_pair_val
#print axioms ConfigurationResidualIndices.fNumber_pair_val
#check ConfigurationResidualIndices.gNumber_id_val
#print axioms ConfigurationResidualIndices.gNumber_id_val
#check ConfigurationResidualIndices.gNumber_within_val
#print axioms ConfigurationResidualIndices.gNumber_within_val
#check ConfigurationResidualIndices.gNumber_sum_val
#print axioms ConfigurationResidualIndices.gNumber_sum_val
#check ConfigurationResidualIndices.gNumber_cross_val
#print axioms ConfigurationResidualIndices.gNumber_cross_val
#check ConfigurationResidualIndices.fRow
#print axioms ConfigurationResidualIndices.fRow
#check ConfigurationResidualIndices.gRow
#print axioms ConfigurationResidualIndices.gRow
#check ConfigurationResidualIndices.fRow_number
#print axioms ConfigurationResidualIndices.fRow_number
#check ConfigurationResidualIndices.gRow_number
#print axioms ConfigurationResidualIndices.gRow_number
#check ConfigurationResidualIndices.gNumber_first_within
#print axioms ConfigurationResidualIndices.gNumber_first_within
#check ConfigurationResidualIndices.gNumber_frame_one_sum
#print axioms ConfigurationResidualIndices.gNumber_frame_one_sum
#check ConfigurationResidualIndices.fNumber_first_trace
#print axioms ConfigurationResidualIndices.fNumber_first_trace
#check ConfigurationResidualIndices.gNumber_first_cross
#print axioms ConfigurationResidualIndices.gNumber_first_cross
#check ConfigurationResidualIndices.canonical_pair_zero_three
#print axioms ConfigurationResidualIndices.canonical_pair_zero_three
#check ConfigurationResidualIndices.grouped_within_1445_to_canonical
#print axioms ConfigurationResidualIndices.grouped_within_1445_to_canonical
#check ConfigurationResidualIndices.firstFramePair
#print axioms ConfigurationResidualIndices.firstFramePair
#check ConfigurationResidualIndices.grouped_first_frame_third_pair
#print axioms ConfigurationResidualIndices.grouped_first_frame_third_pair
#check ConfigurationResidualIndices.canonical_1445_inverse
#print axioms ConfigurationResidualIndices.canonical_1445_inverse
