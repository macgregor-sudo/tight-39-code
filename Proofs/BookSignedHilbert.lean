module

public import BookGradedSpecialization
public import A6Step67Main

@[expose] public section

noncomputable section
namespace Option2.NativeStress.BookHilbertCharZero
open MvPolynomial Module

/-- Lift the checker's two residue representatives to the actual signs. -/
def signedCoefficient (c : ℕ) : ℤ := if c = 1 then 1 else -1

/-- The SAME 48 ordered trinomials and exact MONO grevlex variable order,
with integral ±1 coefficients, rather than positive residue representatives. -/
def integerTrinomial (s : Fin 48) : MvPolynomial (Fin 24) ℤ :=
  ((MonoKV.tri s.val).map fun e =>
    monomial (MonoSound.vfin e.1 + MonoSound.vfin e.2.1) (signedCoefficient e.2.2)).sum

def trinomials (K : Type*) [CommRing K] : Fin 48 → MvPolynomial (Fin 24) K :=
  fun s => MvPolynomial.map (Int.castRingHom K) (integerTrinomial s)

 theorem tri_signs : ∀ s < 48, ∀ e ∈ MonoKV.tri s, e.2.2 = 1 ∨ e.2.2 = 1048572 := by
  decide +kernel

 theorem map_signedCoefficient (c : ℕ) (hc : c = 1 ∨ c = 1048572) :
    (Int.castRingHom A6Compact.F) (signedCoefficient c) = (c : A6Compact.F) := by
  rcases hc with rfl | rfl
  · simp [signedCoefficient]
  · change (-1 : ZMod 1048573) = 1048572
    decide +kernel

 theorem trinomials_modP : trinomials A6Compact.F = MonoSound.t := by
  funext s
  rw [trinomials, integerTrinomial, map_list_sum]
  change List.sum _ = List.sum _
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  simp only [Function.comp_apply, map_monomial]
  rw [map_signedCoefficient _ (tri_signs s.val s.isLt e he)]

 theorem integerTrinomial_homogeneous (s : Fin 48) : (integerTrinomial s).IsHomogeneous 2 := by
  unfold integerTrinomial
  generalize hL : (MonoKV.tri s.val).map _ = L
  have h : ∀ p ∈ L, p.IsHomogeneous 2 := by
    intro p hp
    rw [← hL] at hp
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
    obtain ⟨ha,hb⟩ := MonoSound.tri_lt s.val s.isLt e he
    apply isHomogeneous_monomial
    rw [map_add, MonoSound.vfin_of_lt ha, MonoSound.vfin_of_lt hb,
      Finsupp.degree_single, Finsupp.degree_single]
  clear hL
  induction L with
  | nil => exact isHomogeneous_zero _ _ _
  | cons p L ih =>
    rw [List.sum_cons]
    exact (h p List.mem_cons_self).add (ih fun q hq => h q (List.mem_cons_of_mem _ hq))

/-- Unconditional universal characteristic-zero bound in the exact signed
MONO variable order. Each degree uses one common integral relation matrix. -/
theorem signed_hilbert_bound (K : Type*) [Field K] [CharZero K] (d : ℕ) :
    finrank K (homogeneousSubmodule (Fin 24) K d ⧸ ChainMid.quadricRelations (trinomials K) d) ≤
      4 * (d+5).choose 5 + 1540 * (d+4).choose 4 := by
  have h := graded_finrank_map_le integerTrinomial integerTrinomial_homogeneous d
    (Int.castRingHom A6Compact.F) (Int.castRingHom K) (Int.cast_injective (α := K))
  change finrank K (homogeneousSubmodule (Fin 24) K d ⧸ ChainMid.quadricRelations (trinomials K) d) ≤
    finrank A6Compact.F (homogeneousSubmodule (Fin 24) A6Compact.F d ⧸
      ChainMid.quadricRelations (trinomials A6Compact.F) d) at h
  rw [trinomials_modP] at h
  exact h.trans (A6Compact.step67_bound d)

end Option2.NativeStress.BookHilbertCharZero
