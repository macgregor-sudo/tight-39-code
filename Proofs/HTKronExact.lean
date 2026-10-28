module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Int.GCD
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-!
# Kronecker exactness for integer polynomial identities (generic, data-free)

If an integer combination of distinct powers of a base `B` vanishes and every coefficient is
smaller than `B` in absolute value, then every coefficient vanishes (uniqueness of base-`B`
expansions with digits in `(-B, B)`). Specialised to quadratic forms through a Sidon exponent
assignment, one exact evaluation decides an identity of quadratic forms.
Classical (Kronecker substitution); first-party Lean.
-/

namespace HTKron

open scoped BigOperators

/-- Base-`B` uniqueness with digits in `(-B, B)`.

Induction inserting the minimum exponent `a`: every other term is divisible by `B ^ (a + 1)`,
hence so is `c a * B ^ a`; cancelling `B ^ a` gives `B ∣ c a`, and `|c a| < B` forces `c a = 0`. -/
theorem digits_eq_zero (B : ℤ) (hB : 1 < B) (E : Finset ℕ) (c : ℕ → ℤ)
    (hc : ∀ e ∈ E, |c e| < B) (h : ∑ e ∈ E, c e * B ^ e = 0) :
    ∀ e ∈ E, c e = 0 := by
  induction E using Finset.induction_on_min with
  | empty => simp
  | insert a s has ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (has a h)
    rw [Finset.sum_insert ha] at h
    have hBa : B ^ a ≠ 0 := pow_ne_zero _ (by omega)
    have hdvd : B * B ^ a ∣ c a * B ^ a := by
      rw [eq_neg_of_add_eq_zero_left h, dvd_neg, ← pow_succ']
      exact Finset.dvd_sum fun e he => (pow_dvd_pow B (has e he)).mul_left _
    have hca : c a = 0 :=
      Int.eq_zero_of_abs_lt_dvd ((mul_dvd_mul_iff_right hBa).mp hdvd)
        (hc a (Finset.mem_insert_self a s))
    rw [hca, zero_mul, zero_add] at h
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact hca
    · exact ih (fun e he => hc e (Finset.mem_insert_of_mem he)) h e he

/-- Quadratic-form version: `M j l` for `j ≤ l` is the coefficient of `y j * y l`, the point is
`y j = B ^ s j`, and `s` is Sidon on unordered pairs.

The double sum is a sum over ordered pairs `j ≤ l` of `M j l * B ^ (s j + s l)`; the exponent map
is injective on such pairs, so reindexing by the exponent and applying `digits_eq_zero` gives the
claim. -/
theorem quadratic_coeff_eq_zero {n : ℕ} (B : ℤ) (hB : 1 < B) (s : Fin n → ℕ)
    (hs : ∀ j l j' l' : Fin n, j ≤ l → j' ≤ l' → s j + s l = s j' + s l' → j = j' ∧ l = l')
    (M : Fin n → Fin n → ℤ) (hM : ∀ j l, j ≤ l → |M j l| < B)
    (h : ∑ j : Fin n, ∑ l : Fin n, (if j ≤ l then M j l else 0) * (B ^ s j * B ^ s l) = 0) :
    ∀ j l, j ≤ l → M j l = 0 := by
  classical
  let P : Finset (Fin n × Fin n) := Finset.univ.filter fun p => p.1 ≤ p.2
  have memP : ∀ p, p ∈ P ↔ p.1 ≤ p.2 := by simp [P]
  let f : Fin n × Fin n → ℕ := fun p => s p.1 + s p.2
  have hinj : Set.InjOn f P := by
    intro p hp q hq hpq
    obtain ⟨h1, h2⟩ := hs _ _ _ _ ((memP p).mp hp) ((memP q).mp hq) hpq
    exact Prod.ext h1 h2
  let c : ℕ → ℤ := fun e => ∑ q ∈ P with f q = e, M q.1 q.2
  have hcf : ∀ p ∈ P, c (f p) = M p.1 p.2 := by
    intro p hp
    refine Finset.sum_eq_single_of_mem p (Finset.mem_filter.mpr ⟨hp, rfl⟩) ?_
    intro q hq hqp
    rw [Finset.mem_filter] at hq
    exact absurd (hinj hq.1 hp hq.2) hqp
  have hsum : ∑ e ∈ P.image f, c e * B ^ e = 0 := by
    rw [Finset.sum_image hinj, ← h, ← Fintype.sum_prod_type', Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with hp
    · rw [hcf p ((memP p).mpr hp), pow_add]
    · simp
  have hcB : ∀ e ∈ P.image f, |c e| < B := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    rw [hcf p hp]
    exact hM _ _ ((memP p).mp hp)
  intro j l hjl
  have hjlP : (j, l) ∈ P := (memP _).mpr hjl
  have := digits_eq_zero B hB (P.image f) c hcB hsum (f (j, l)) (Finset.mem_image_of_mem f hjlP)
  rwa [hcf _ hjlP] at this

end HTKron

#print axioms HTKron.digits_eq_zero
#print axioms HTKron.quadratic_coeff_eq_zero
