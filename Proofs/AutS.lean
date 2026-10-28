module

public import TitsProduct
public import PointsS
public import ConfigS

@[expose] public section

/-!
# Automorphisms (brief C4)

(i) The Tits-pair action `titsAct g k (a, B, Bt) = (g a adj g, g B adj k, (adj g)ᵀ Bt kᵀ)` for
`det g = det k = 1` preserves `titsProduct`, unit, trace and pairing; transported to native
coordinates it is `pairAct ι h g k`, an `IsAut`.
(ii) Signed permutations `sgnPerm perm sgn x k = sgn k * x (perm k)` are automorphisms whenever the
decidable integer predicate `IsStructureAut perm pinv sgn` and the per-output tensor compatibility
`numOK perm sgn k` hold.
-/

namespace TitsS

open NativePolynomial.CoordinateMaps NativePolynomial.IntegralStructureConstants Matrix

variable {S : Type*} [CommRing S] (ι : Q12 →+* S)

/-! ### The Tits-pair action -/

section TitsAct

variable (g k : M3 S)

/-- Conjugation on the hermitian slot. -/
def cA (a : M3 S) : M3 S := g * a * adjugate g
/-- Twisted conjugation on the `B` slot. -/
def cB (B : M3 S) : M3 S := g * B * adjugate k
/-- Twisted conjugation on the partner slot. -/
def cBt (Bt : M3 S) : M3 S := (adjugate g)ᵀ * Bt * kᵀ

/-- The Tits-pair action on triples. -/
def titsAct (p : Tits S) : Tits S := (cA g p.1, cB g k p.2.1, cBt g k p.2.2)

variable {g k}

theorem mul_adj (hg : det g = 1) : g * adjugate g = 1 := by rw [mul_adjugate, hg, one_smul]
theorem adj_mul (hg : det g = 1) : adjugate g * g = 1 := by rw [adjugate_mul, hg, one_smul]
theorem adj_adj (hg : det g = 1) : adjugate (adjugate g) = g := by
  rw [adjugate_adjugate g (by simp), hg, one_pow, one_smul]
theorem transpose_mul_adj_transpose (hg : det g = 1) : gᵀ * (adjugate g)ᵀ = 1 := by
  rw [← transpose_mul, adj_mul hg, transpose_one]
theorem adj_transpose_mul_transpose (hg : det g = 1) : (adjugate g)ᵀ * gᵀ = 1 := by
  rw [← transpose_mul, mul_adj hg, transpose_one]

theorem cA_add (a b : M3 S) : cA g (a + b) = cA g a + cA g b := by
  simp [cA, Matrix.mul_add, Matrix.add_mul]
theorem cA_sub (a b : M3 S) : cA g (a - b) = cA g a - cA g b := by
  simp [cA, Matrix.mul_sub, Matrix.sub_mul]
theorem cA_smul (c : S) (a : M3 S) : cA g (c • a) = c • cA g a := by
  simp [cA, Matrix.mul_smul]
theorem cA_zero : cA g (0 : M3 S) = 0 := by simp [cA]
theorem cB_add (a b : M3 S) : cB g k (a + b) = cB g k a + cB g k b := by
  simp [cB, Matrix.mul_add, Matrix.add_mul]
theorem cB_sub (a b : M3 S) : cB g k (a - b) = cB g k a - cB g k b := by
  simp [cB, Matrix.mul_sub, Matrix.sub_mul]
theorem cB_smul (c : S) (a : M3 S) : cB g k (c • a) = c • cB g k a := by
  simp [cB, Matrix.mul_smul]
theorem cB_zero : cB g k (0 : M3 S) = 0 := by simp [cB]
theorem cBt_add (a b : M3 S) : cBt g k (a + b) = cBt g k a + cBt g k b := by
  simp [cBt, Matrix.mul_add, Matrix.add_mul]
theorem cBt_sub (a b : M3 S) : cBt g k (a - b) = cBt g k a - cBt g k b := by
  simp [cBt, Matrix.mul_sub, Matrix.sub_mul]
theorem cBt_smul (c : S) (a : M3 S) : cBt g k (c • a) = c • cBt g k a := by
  simp [cBt, Matrix.mul_smul]
theorem cBt_zero : cBt g k (0 : M3 S) = 0 := by simp [cBt]

variable (hg : det g = 1) (hk : det k = 1)
include hg

theorem cA_one : cA g (1 : M3 S) = 1 := by rw [cA, Matrix.mul_one, mul_adj hg]

theorem cA_mul (a b : M3 S) : cA g (a * b) = cA g a * cA g b := by
  simp only [cA, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (adjugate g) g, adj_mul hg, Matrix.one_mul]

theorem trace_cA (a : M3 S) : trace (cA g a) = trace a := by
  rw [cA, trace_mul_comm, ← Matrix.mul_assoc, adj_mul hg, Matrix.one_mul]

theorem cA_mul_cB (a B : M3 S) : cA g a * cB g k B = cB g k (a * B) := by
  simp only [cA, cB, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (adjugate g) g, adj_mul hg, Matrix.one_mul]

theorem smul_one_sub_cA_mul_cB (c : S) (a B : M3 S) :
    (c • (1 : M3 S) - cA g a) * cB g k B = cB g k ((c • 1 - a) * B) := by
  rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul,
    Matrix.one_mul, cA_mul_cB hg, cB_sub, cB_smul]

theorem cA_transpose_mul_cBt (a Bt : M3 S) :
    (cA g a)ᵀ * cBt g k Bt = cBt g k (aᵀ * Bt) := by
  simp only [cA, cBt, transpose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc gᵀ (adjugate g)ᵀ, transpose_mul_adj_transpose hg, Matrix.one_mul]

theorem smul_one_sub_cA_transpose_mul_cBt (c : S) (a Bt : M3 S) :
    (c • (1 : M3 S) - (cA g a)ᵀ) * cBt g k Bt = cBt g k ((c • 1 - aᵀ) * Bt) := by
  rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul,
    Matrix.one_mul, cA_transpose_mul_cBt hg, cBt_sub, cBt_smul]

theorem adj_cBt (X : M3 S) : adjugate (cBt g k X) = (adjugate k)ᵀ * (adjugate X * gᵀ) := by
  rw [cBt, adjugate_mul_distrib, adjugate_mul_distrib, ← adjugate_transpose, ← adjugate_transpose,
    adj_adj hg]

theorem crossT_cBt (Bt Dt : M3 S) :
    crossT (cBt g k Bt) (cBt g k Dt) = cB g k (crossT Bt Dt) := by
  simp only [crossT, cB, ← cBt_add, adj_cBt hg, transpose_sub, transpose_mul, transpose_transpose,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

include hk

omit hg in
theorem cB_mul_cBt_transpose (B Dt : M3 S) :
    cB g k B * (cBt g k Dt)ᵀ = cA g (B * Dtᵀ) := by
  simp only [cB, cBt, cA, transpose_mul, transpose_transpose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (adjugate k) k, adj_mul hk, Matrix.one_mul]

omit hg in
theorem adj_cB (X : M3 S) : adjugate (cB g k X) = k * (adjugate X * adjugate g) := by
  rw [cB, adjugate_mul_distrib, adjugate_mul_distrib, adj_adj hk]

omit hg in
theorem crossT_cB (B D : M3 S) :
    crossT (cB g k B) (cB g k D) = cBt g k (crossT B D) := by
  simp only [crossT, cBt, ← cB_add, adj_cB hk, transpose_sub, transpose_mul, transpose_transpose,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

/-- The Tits-pair action preserves the Tits product (`det g = det k = 1`). -/
theorem titsAct_product (h : S) (p q : Tits S) :
    titsProduct h (titsAct g k p) (titsAct g k q) = titsAct g k (titsProduct h p q) := by
  obtain ⟨a, B, Bt⟩ := p
  obtain ⟨c, D, Dt⟩ := q
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [titsProduct, titsAct]
    simp only [cB_mul_cBt_transpose hk, trace_cA hg]
    simp only [cA_add, cA_sub, cA_smul, cA_one hg, cA_mul hg]
  · simp only [titsProduct, titsAct]
    simp only [trace_cA hg, smul_one_sub_cA_mul_cB hg, crossT_cBt hg]
    simp only [cB_add, cB_smul]
  · simp only [titsProduct, titsAct]
    simp only [trace_cA hg, smul_one_sub_cA_transpose_mul_cBt hg, crossT_cB hk]
    simp only [cBt_add, cBt_smul]

omit hg hk in
theorem titsAct_add (p q : Tits S) : titsAct g k (p + q) = titsAct g k p + titsAct g k q := by
  simp [titsAct, cA_add, cB_add, cBt_add]

omit hg hk in
theorem titsAct_zero : titsAct g k (0 : Tits S) = 0 := by
  simp [titsAct, cA_zero, cB_zero, cBt_zero]

omit hk in
theorem titsAct_unit : titsAct g k ((1, 0, 0) : Tits S) = (1, 0, 0) := by
  simp [titsAct, cA_one hg, cB_zero, cBt_zero]

end TitsAct

/-! ### Transport to native coordinates -/

theorem titsOfNative_add (x y : Fin 27 → S) :
    titsOfNative ι (x + y) = titsOfNative ι x + titsOfNative ι y := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp only [titsOfNative, Prod.fst_add, Prod.snd_add, Matrix.add_apply, Matrix.of_apply,
      Matrix.cons_val, Fin.isValue, Pi.add_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    ring

theorem titsOfNative_zero : titsOfNative ι (0 : Fin 27 → S) = 0 := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [titsOfNative]

/-- The Tits-pair action in native coordinates. -/
def pairAct (h : S) (g k : M3 S) (x : Fin 27 → S) : Fin 27 → S :=
  titsToNative ι h (titsAct g k (titsOfNative ι x))

theorem pairAct_isAut (h : S) (h2 : (2 : S) * h = 1) {g k : M3 S} (hg : det g = 1)
    (hk : det k = 1) : IsAut h (pairAct ι h g k) where
  map_add x y := by
    rw [pairAct, pairAct, pairAct, titsOfNative_add, titsAct_add, titsToNative_add]
  map_zero := by
    rw [pairAct, titsOfNative_zero, titsAct_zero, titsToNative_zero]
  map_prod x y := by
    rw [pairAct, pairAct, pairAct, titsOfNative_product, ← titsAct_product hg hk,
      product_titsToNative ι h h2]
  map_unit := by
    rw [pairAct, titsOfNative_unit, titsAct_unit hg, titsToNative_unit ι h h2]
  map_trace x := by
    rw [pairAct, trace_titsToNative ι h h2, ← trace_titsOfNative ι]
    exact trace_cA hg _
  map_pairing x y := by
    rw [pairAct, pairAct, pairing_titsToNative ι h h2, pairing_titsOfNative ι]
    simp only [titsAct]
    rw [← cA_mul hg, cB_mul_cBt_transpose hk, cB_mul_cBt_transpose hk, trace_cA hg,
      trace_cA hg, trace_cA hg]

/-- The diagonal action on a non-anchor point: `pt (U, Ut) ↦ pt (g U adj g, (adj g)ᵀ Ut gᵀ)`. -/
theorem pairAct_pt (h t : S) (h2 : (2 : S) * h = 1) {g : M3 S} (hg : det g = 1) (U Ut : M3 S) :
    pairAct ι h g g (pt ι h t U Ut) = pt ι h t (cA g U) (cBt g g Ut) := by
  rw [pairAct, pt, pt, ofNative_toNative ι h h2]
  simp only [titsAct, ptTits, cA_smul, cA_one hg, cB_smul, cBt_smul]
  rfl

theorem pairAct_anc (h : S) (h2 : (2 : S) * h = 1) (g k : M3 S) (a : M3 S) :
    pairAct ι h g k (anc ι h a) = anc ι h (cA g a) := by
  rw [pairAct, anc, anc, ofNative_toNative ι h h2]
  simp only [titsAct, ancTits, cB_zero, cBt_zero]

/-- `UPair` is preserved by the diagonal action. -/
theorem UPair.conj {g : M3 S} (hg : det g = 1) {U Ut : M3 S} (hU : UPair U Ut) :
    UPair (cA g U) (cBt g g Ut) := by
  constructor
  · have : cA g U = cB g g U := rfl
    rw [this, cB_mul_cBt_transpose hg, hU.1, cA_one hg]
  · have : cA g U = cB g g U := rfl
    rw [this, adj_cB hg, hU.2, cBt, transpose_mul, transpose_mul, transpose_transpose,
      transpose_transpose]

theorem trace_cA_mul_cBt_transpose {g : M3 S} (hg : det g = 1) (U Vt : M3 S) :
    trace (cA g U * (cBt g g Vt)ᵀ) = trace (U * Vtᵀ) := by
  have : cA g U = cB g g U := rfl
  rw [this, cB_mul_cBt_transpose hg, trace_cA hg]

/-! ### Signed permutations -/

/-- `(sgnPerm perm sgn x) k = sgn k * x (perm k)` (the transport-table convention). -/
def sgnPerm (perm : Fin 27 → Fin 27) (sgn : Fin 27 → ℤ) (x : Fin 27 → S) : Fin 27 → S :=
  fun k => (sgn k : S) * x (perm k)

/-- Tensor compatibility for output `k` (decidable; one `decide` per `k`). -/
def numOK (perm : Fin 27 → Fin 27) (sgn : Fin 27 → ℤ) (k : Fin 27) : Prop :=
  ∀ i j : Fin 27, sgn k * numerator (perm i) (perm j) (perm k) = sgn i * sgn j * numerator i j k

instance (perm : Fin 27 → Fin 27) (sgn : Fin 27 → ℤ) (k : Fin 27) : Decidable (numOK perm sgn k) := by
  unfold numOK; infer_instance

/-- The remaining decidable integer conditions. -/
def IsStructureAut (perm pinv : Fin 27 → Fin 27) (sgn : Fin 27 → ℤ) : Prop :=
  (∀ k, pinv (perm k) = k) ∧ (∀ k, perm (pinv k) = k) ∧ (∀ k, sgn k * sgn k = 1) ∧
    (∀ k, sgn k * (if (perm k).val < 3 then 1 else 0) = (if k.val < 3 then (1 : ℤ) else 0)) ∧
    (∀ k : Fin 27, k.val < 3 → perm k = k ∧ sgn k = 1) ∧
    (∀ k, coordinateTraceWeight (perm k) = coordinateTraceWeight k)

instance (perm pinv : Fin 27 → Fin 27) (sgn : Fin 27 → ℤ) : Decidable (IsStructureAut perm pinv sgn) := by
  unfold IsStructureAut; infer_instance

/-- The permutation as an `Equiv`. -/
def permEquiv (perm pinv : Fin 27 → Fin 27) (hl : ∀ k, pinv (perm k) = k)
    (hr : ∀ k, perm (pinv k) = k) : Fin 27 ≃ Fin 27 :=
  ⟨perm, pinv, hl, hr⟩

theorem sgnPerm_isAut (h : S) {perm pinv : Fin 27 → Fin 27} {sgn : Fin 27 → ℤ}
    (hA : IsStructureAut perm pinv sgn) (hnum : ∀ k, numOK perm sgn k) :
    IsAut h (sgnPerm perm sgn : (Fin 27 → S) → (Fin 27 → S)) := by
  obtain ⟨hl, hr, hsq, hunit, hdiag, hw⟩ := hA
  let e := permEquiv perm pinv hl hr
  have he : ∀ i, e i = perm i := fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y; funext k; simp [sgnPerm, mul_add]
  · funext k; simp [sgnPerm]
  · intro x y
    funext k
    simp only [sgnPerm, coordinateProduct_apply]
    rw [← Equiv.sum_comp e (fun i => ∑ j, x i * y j * (h * (numerator i j (perm k) : S)))]
    simp only [he]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp e (fun j => x (perm i) * y j * (h * (numerator (perm i) j (perm k) : S)))]
    simp only [he]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hn : ((sgn k : ℤ) : S) * (numerator (perm i) (perm j) (perm k) : S) =
        (sgn i : S) * (sgn j : S) * (numerator i j k : S) := by
      have := congrArg (Int.cast (R := S)) (hnum k i j)
      push_cast at this
      exact this
    linear_combination (x (perm i) * y (perm j) * h) * hn
  · funext k
    have hu := hunit k
    have hu' : (((sgn k * (if (perm k).val < 3 then 1 else 0) : ℤ)) : S) =
        ((if k.val < 3 then (1 : ℤ) else 0 : ℤ) : S) := by rw [hu]
    push_cast at hu'
    simpa [sgnPerm, coordinateUnit] using hu'
  · intro x
    simp only [coordinateTrace_apply, sgnPerm]
    rw [(hdiag 0 (by decide)).1, (hdiag 0 (by decide)).2, (hdiag 1 (by decide)).1,
      (hdiag 1 (by decide)).2, (hdiag 2 (by decide)).1, (hdiag 2 (by decide)).2]
    simp
  · intro x y
    simp only [coordinatePairing, sgnPerm]
    rw [← Equiv.sum_comp e (fun i => (coordinateTraceWeight i : S) * x i * y i)]
    simp only [he]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hs : ((sgn i : ℤ) : S) * (sgn i : S) = 1 := by
      have := congrArg (Int.cast (R := S)) (hsq i)
      push_cast at this
      exact this
    rw [hw i]
    linear_combination ((coordinateTraceWeight i : S) * x (perm i) * y (perm i)) * hs

/-- Lists → permutation / sign functions (the tables `T*_perm`, `T*_sign`). -/
def permOfList (l : List ℕ) (k : Fin 27) : Fin 27 := ⟨l.getD k.val 0 % 27, Nat.mod_lt _ (by norm_num)⟩
def sgnOfList (l : List ℤ) (k : Fin 27) : ℤ := l.getD k.val 0

/-- The identity transport satisfies everything (sanity test of the decidable predicate). -/
theorem id_isStructureAut : IsStructureAut (fun k => k) (fun k => k) (fun _ => 1) := by decide

theorem id_numOK (k : Fin 27) : numOK (fun k => k) (fun _ => 1) k := by
  intro i j; simp

end TitsS

#print axioms TitsS.titsAct_product
#print axioms TitsS.pairAct_isAut
#print axioms TitsS.pairAct_pt
#print axioms TitsS.UPair.conj
#print axioms TitsS.sgnPerm_isAut
#print axioms TitsS.id_isStructureAut
