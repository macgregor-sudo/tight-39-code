module

public import HTPCValDerC

@[expose] public section

/-!
# The 24 real derivation-extension generators are trace-skew, unit-killing, trace-free derivations
(first-party). One kernel decision per generator (`gen_ok_*`), then `gen_props`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace Option2.NativeStress.HTPhaseComplete

open NativePolynomial.IntegralStructureConstants

/-- Entry-wise skewness check (only positions present in the list need checking). -/
def skewE (l : List IEnt) : Bool :=
  l.all fun e => coordinateTraceWeight e.1 * iAt l e.1 e.2.1 + coordinateTraceWeight e.2.1 * iAt l e.2.1 e.1 = 0

theorem iAt_ne_zero_mem (l : List IEnt) (m n : Fin 27) (h : iAt l m n ≠ 0) :
    ∃ e ∈ l, e.1 = m ∧ e.2.1 = n := by
  induction l with
  | nil => simp [iAt] at h
  | cons e l ih =>
    by_cases he : e.1 = m ∧ e.2.1 = n
    · exact ⟨e, List.mem_cons_self .., he⟩
    · have : iAt (e :: l) m n = iAt l m n := by simp [iAt, he]
      obtain ⟨e', h1, h2⟩ := ih (by rwa [this] at h)
      exact ⟨e', List.mem_cons_of_mem _ h1, h2⟩

theorem skew_int (l : List IEnt) (h : skewE l = true) (m n : Fin 27) :
    coordinateTraceWeight m * iAt l m n + coordinateTraceWeight n * iAt l n m = 0 := by
  simp only [skewE, List.all_eq_true, decide_eq_true_eq] at h
  by_cases h1 : iAt l m n ≠ 0
  · obtain ⟨e, he, rfl, rfl⟩ := iAt_ne_zero_mem l m n h1; exact h e he
  · by_cases h2 : iAt l n m ≠ 0
    · obtain ⟨e, he, h3, h4⟩ := iAt_ne_zero_mem l n m h2
      have := h e he; rw [h3, h4] at this; linarith
    · push_neg at h1 h2; rw [h1, h2]; ring

def genOK (l : List IEnt) : Bool :=
  decide (derBound l < kX) && decide (kronF l = 0) && skewE l && unitOK l && traceOK l

theorem gen_props {R : Type*} [CommRing R] (l : List IEnt) (h : genOK l = true) :
    IsDer (iMat (R := R) l) ∧ IsSkew (iMat (R := R) l) ∧ KillsUnit (iMat (R := R) l) ∧
      TraceFree (iMat (R := R) l) := by
  simp only [genOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hb, hk⟩, hs⟩, hu⟩, ht⟩ := h
  refine ⟨isDer_of_kronF l hb hk, ?_, killsUnit_of l hu, traceFree_of l ht⟩
  intro m n
  have := congrArg (Int.cast : ℤ → R) (skew_int l hs m n)
  simp only [iMat]; push_cast at this; exact this

theorem gen_ok_Rd0 : genOK aRd0 = true := by decide +kernel
theorem gen_ok_Is0 : genOK aIs0 = true := by decide +kernel
theorem gen_ok_Rd1 : genOK aRd1 = true := by decide +kernel
theorem gen_ok_Is1 : genOK aIs1 = true := by decide +kernel
theorem gen_ok_Rd2 : genOK aRd2 = true := by decide +kernel
theorem gen_ok_Is2 : genOK aIs2 = true := by decide +kernel
theorem gen_ok_Rd3 : genOK aRd3 = true := by decide +kernel
theorem gen_ok_Is3 : genOK aIs3 = true := by decide +kernel
theorem gen_ok_Rd4 : genOK aRd4 = true := by decide +kernel
theorem gen_ok_Is4 : genOK aIs4 = true := by decide +kernel
theorem gen_ok_Rd5 : genOK aRd5 = true := by decide +kernel
theorem gen_ok_Is5 : genOK aIs5 = true := by decide +kernel
theorem gen_ok_Rd6 : genOK aRd6 = true := by decide +kernel
theorem gen_ok_Is6 : genOK aIs6 = true := by decide +kernel
theorem gen_ok_Rd7 : genOK aRd7 = true := by decide +kernel
theorem gen_ok_Is7 : genOK aIs7 = true := by decide +kernel
theorem gen_ok_Rd8 : genOK aRd8 = true := by decide +kernel
theorem gen_ok_Is8 : genOK aIs8 = true := by decide +kernel
theorem gen_ok_Rd9 : genOK aRd9 = true := by decide +kernel
theorem gen_ok_Is9 : genOK aIs9 = true := by decide +kernel
theorem gen_ok_Rd10 : genOK aRd10 = true := by decide +kernel
theorem gen_ok_Is10 : genOK aIs10 = true := by decide +kernel
theorem gen_ok_Rd11 : genOK aRd11 = true := by decide +kernel
theorem gen_ok_Is11 : genOK aIs11 = true := by decide +kernel

/-- Every pair of `aPairs` has both generators checked. -/
theorem aPairs_ok : ∀ pr ∈ aPairs, genOK pr.2.2.2.1 = true ∧ genOK pr.2.2.2.2 = true := by
  intro pr hpr
  simp only [aPairs, List.mem_cons, List.mem_nil_iff, or_false] at hpr
  rcases hpr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨gen_ok_Rd0, gen_ok_Is0⟩
  · exact ⟨gen_ok_Rd1, gen_ok_Is1⟩
  · exact ⟨gen_ok_Rd2, gen_ok_Is2⟩
  · exact ⟨gen_ok_Rd3, gen_ok_Is3⟩
  · exact ⟨gen_ok_Rd4, gen_ok_Is4⟩
  · exact ⟨gen_ok_Rd5, gen_ok_Is5⟩
  · exact ⟨gen_ok_Rd6, gen_ok_Is6⟩
  · exact ⟨gen_ok_Rd7, gen_ok_Is7⟩
  · exact ⟨gen_ok_Rd8, gen_ok_Is8⟩
  · exact ⟨gen_ok_Rd9, gen_ok_Is9⟩
  · exact ⟨gen_ok_Rd10, gen_ok_Is10⟩
  · exact ⟨gen_ok_Rd11, gen_ok_Is11⟩

end Option2.NativeStress.HTPhaseComplete
#print axioms Option2.NativeStress.HTPhaseComplete.aPairs_ok
#print axioms Option2.NativeStress.HTPhaseComplete.gen_props
