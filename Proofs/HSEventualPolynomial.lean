/-
Selected declarations adapted from the OpenAI math project (Apache-2.0):
https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a
Original: lean/OAI/RingTheory/Multiplicity/SeparableOrderNormalizedLength.lean
Declarations: sumPolynomial through EventuallyPolynomial.of_recurrence.
Changes: selected-declaration extraction, narrow imports, current module format;
any compatibility repairs are local to these selected mathematical proofs.
No individual declaration authorship is inferred. Thanks to the OpenAI math project.
License text: LICENSE.
“If I have seen further it is by standing on the sholders of Giants.” — Isaac
Newton, letter to Robert Hooke, 1676.
-/
module
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.Tactic

@[expose] public section
noncomputable section
open scoped Classical BigOperators ENNReal
namespace OAI

namespace Lech
open Polynomial Filter
open scoped BigOperators

noncomputable def sumPolynomial (p : ℚ[X]) : ℚ[X] :=
  ∑ j ∈ p.support, Polynomial.C (p.coeff j / (j + 1 : ℚ)) *
    (Polynomial.bernoulli (j + 1) - Polynomial.C (_root_.bernoulli (j + 1)))

lemma sumPolynomial_eval (p : ℚ[X]) (n : ℕ) :
    (sumPolynomial p).eval (n : ℚ) = ∑ k ∈ Finset.range n, p.eval (k : ℚ) := by
  simp only [sumPolynomial, eval_finsetSum, eval_mul, eval_C, eval_sub]
  have h (j : ℕ) :
      Polynomial.eval (n : ℚ) (Polynomial.bernoulli (j + 1)) - _root_.bernoulli (j + 1) =
        (j + 1 : ℚ) * ∑ k ∈ Finset.range n, (k : ℚ) ^ j :=
    (Polynomial.sum_range_pow_eq_bernoulli_sub n j).symm
  simp_rw [h]
  have hn (j : ℕ) : (j + 1 : ℚ) ≠ 0 := by positivity
  simp_rw [← mul_assoc, div_mul_cancel₀ _ (hn _), Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  exact (Polynomial.eval_eq_sum (p := p) (x := (k : ℚ))).symm

def EventuallyPolynomial (f : ℕ → ℚ) : Prop :=
  ∃ p : ℚ[X], ∀ᶠ n in atTop, f n = p.eval (n : ℚ)

lemma eventuallyPolynomial_zero : EventuallyPolynomial (fun _ : ℕ => (0 : ℚ)) :=
  ⟨0, by simp⟩

lemma EventuallyPolynomial.add {f g : ℕ → ℚ}
    (hf : EventuallyPolynomial f) (hg : EventuallyPolynomial g) :
    EventuallyPolynomial (fun n => f n + g n) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, by filter_upwards [hp, hq] with n hn hm; simp [hn, hm]⟩

lemma EventuallyPolynomial.sub {f g : ℕ → ℚ}
    (hf : EventuallyPolynomial f) (hg : EventuallyPolynomial g) :
    EventuallyPolynomial (fun n => f n - g n) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨p - q, by filter_upwards [hp, hq] with n hn hm; simp [hn, hm]⟩

lemma EventuallyPolynomial.succ {f : ℕ → ℚ} (hf : EventuallyPolynomial f) :
    EventuallyPolynomial (fun n => f (n + 1)) := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨p.comp (Polynomial.X + 1), ?_⟩
  have ht := (Filter.tendsto_add_atTop_nat 1).eventually hp
  filter_upwards [ht] with n hn
  simpa using hn

lemma EventuallyPolynomial.of_sub_succ {f : ℕ → ℚ}
    (hf : EventuallyPolynomial (fun n => f (n + 1) - f n)) :
    EventuallyPolynomial f := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hp
  let q := sumPolynomial p
  have hq (n : ℕ) : q.eval (n + 1 : ℚ) - q.eval (n : ℚ) = p.eval (n : ℚ) := by
    have he := sumPolynomial_eval p (n + 1)
    rw [Finset.sum_range_succ, ← sumPolynomial_eval p n] at he
    dsimp [q]
    push_cast at he
    linarith
  refine ⟨q + Polynomial.C (f N - q.eval (N : ℚ)), Filter.eventually_atTop.mpr ⟨N, ?_⟩⟩
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      have hstep := hN n hn
      have hqstep := hq n
      simp only [eval_add, eval_C] at ih ⊢
      push_cast
      linarith

lemma EventuallyPolynomial.of_recurrence {f k c : ℕ → ℚ}
    (hk : EventuallyPolynomial k) (hc : EventuallyPolynomial c)
    (hrec : ∀ n, f (n + 1) + k n = f n + c (n + 1)) : EventuallyPolynomial f := by
  apply EventuallyPolynomial.of_sub_succ
  have h := hc.succ.sub hk
  have he : (fun n => f (n + 1) - f n) = (fun n => c (n + 1) - k n) := by
    funext n
    linarith [hrec n]
  rwa [he]

end Lech

end OAI
#print axioms OAI.Lech.EventuallyPolynomial.of_sub_succ
