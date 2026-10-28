module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Basic.Real.Basic

/-!
# Finite averaging for a `C₃ × C₃` action

For two commuting real-linear endomorphisms of order dividing three,
the four cyclic subgroups `⟨ρ₀⟩, ⟨ρ₁⟩, ⟨ρ₀²ρ₁²⟩, ⟨ρ₀²ρ₁⟩` cover the nontrivial elements of the group
they generate, so `Σ_H P_H = 1 + 3 P_K` for the averaging projections; taking traces gives the
dimension formula. No independence of `ρ₀, ρ₁` is assumed.
-/

@[expose] public section

namespace CKM.NativeFirstOrder

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The subspace fixed by a linear endomorphism. -/
def fixedSpace (g : Module.End ℝ V) : Submodule ℝ V := LinearMap.ker (g - 1)

theorem mem_fixedSpace {g : Module.End ℝ V} {v : V} : v ∈ fixedSpace g ↔ g v = v := by
  simp [fixedSpace, sub_eq_zero]

/-- Unnormalised averaging operator `1 + g + g²`. -/
private def avgQ (g : Module.End ℝ V) : Module.End ℝ V := 1 + g + g ^ 2

/-- Averaging projection `(1 + g + g²)/3`. -/
private noncomputable def avgP (g : Module.End ℝ V) : Module.End ℝ V := (3 : ℝ)⁻¹ • avgQ g

private lemma mul_avgQ {g : Module.End ℝ V} (h : g ^ 3 = 1) : g * avgQ g = avgQ g := by
  have h3 : g * g ^ 2 = g ^ 3 := by rw [← pow_succ']
  rw [avgQ, mul_add, mul_add, mul_one, ← pow_two, h3, h]
  abel

private lemma mul_avgP {g : Module.End ℝ V} (h : g ^ 3 = 1) : g * avgP g = avgP g := by
  rw [avgP, mul_smul_comm, mul_avgQ h]

private lemma avgQ_eq_smul (g : Module.End ℝ V) : avgQ g = (3 : ℝ) • avgP g := by
  rw [avgP, smul_smul]; norm_num

private lemma isProj_avgP {g : Module.End ℝ V} (h : g ^ 3 = 1) :
    LinearMap.IsProj (fixedSpace g) (avgP g) where
  map_mem x := by
    rw [mem_fixedSpace, ← Module.End.mul_apply, mul_avgP h]
  map_id x hx := by
    rw [mem_fixedSpace] at hx
    have hx2 : (g ^ 2) x = x := by rw [pow_two, Module.End.mul_apply, hx, hx]
    simp only [avgP, avgQ, LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply, hx, hx2]
    rw [show x + x + x = (3 : ℝ) • x by module, smul_smul]
    norm_num

private lemma commute_avgP {a b : Module.End ℝ V} (hc : Commute a b) : Commute b (avgP a) := by
  have hQ : Commute b (avgQ a) :=
    ((Commute.one_right b).add_right hc.symm).add_right (hc.symm.pow_right 2)
  change b * avgP a = avgP a * b
  rw [avgP, mul_smul_comm, hQ.eq, smul_mul_assoc]

private lemma isProj_avgP_mul {a b : Module.End ℝ V} (hc : Commute a b) (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) :
    LinearMap.IsProj (fixedSpace a ⊓ fixedSpace b) (avgP a * avgP b) where
  map_mem x := by
    rw [Submodule.mem_inf, mem_fixedSpace, mem_fixedSpace, ← Module.End.mul_apply,
      ← Module.End.mul_apply, ← mul_assoc, mul_avgP ha, ← mul_assoc, (commute_avgP hc).eq,
      mul_assoc, mul_avgP hb]
    exact ⟨rfl, rfl⟩
  map_id x hx := by
    rw [Submodule.mem_inf] at hx
    rw [Module.End.mul_apply, (isProj_avgP hb).map_id x hx.2, (isProj_avgP ha).map_id x hx.1]

private lemma sq_sq_of_cube {a : Module.End ℝ V} (h : a ^ 3 = 1) : (a ^ 2) ^ 2 = a := by
  rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, h, one_mul]

/-- The covering identity `Σ_H (1 + h + h²) = 3 + (1 + ρ₀ + ρ₀²)(1 + ρ₁ + ρ₁²)`. -/
private lemma avgQ_sum {a b : Module.End ℝ V} (hc : Commute a b) (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) :
    avgQ a + avgQ b + avgQ (a ^ 2 * b ^ 2) + avgQ (a ^ 2 * b) = 1 + 1 + 1 + avgQ a * avgQ b := by
  have e1 : (a ^ 2 * b ^ 2) ^ 2 = a * b := by
    rw [(hc.pow_pow 2 2).mul_pow 2, sq_sq_of_cube ha, sq_sq_of_cube hb]
  have e2 : (a ^ 2 * b) ^ 2 = a * b ^ 2 := by
    rw [(hc.pow_left 2).mul_pow 2, sq_sq_of_cube ha]
  simp only [avgQ, e1, e2]
  noncomm_ring

private lemma trace_avgP {g : Module.End ℝ V} [FiniteDimensional ℝ V] (h : g ^ 3 = 1) :
    LinearMap.trace ℝ V (avgP g) = (Module.finrank ℝ ↥(fixedSpace g) : ℝ) :=
  (isProj_avgP h).trace

theorem finrank_add_three_mul_finrank_fixed_inf [FiniteDimensional ℝ V]
    (ρ₀ ρ₁ : Module.End ℝ V) (hcomm : ρ₀ * ρ₁ = ρ₁ * ρ₀) (h₀ : ρ₀ ^ 3 = 1) (h₁ : ρ₁ ^ 3 = 1) :
    Module.finrank ℝ V + 3 * Module.finrank ℝ ↥(fixedSpace ρ₀ ⊓ fixedSpace ρ₁) =
      Module.finrank ℝ ↥(fixedSpace ρ₀) + Module.finrank ℝ ↥(fixedSpace ρ₁) +
        Module.finrank ℝ ↥(fixedSpace (ρ₀ ^ 2 * ρ₁ ^ 2)) +
        Module.finrank ℝ ↥(fixedSpace (ρ₀ ^ 2 * ρ₁)) := by
  have hc : Commute ρ₀ ρ₁ := hcomm
  have hc2 : (ρ₀ ^ 2 * ρ₁ ^ 2) ^ 3 = 1 := by
    rw [(hc.pow_pow 2 2).mul_pow 3, ← pow_mul, ← pow_mul, mul_comm 2 3, pow_mul, pow_mul, h₀, h₁,
      one_pow, one_mul]
  have hc3 : (ρ₀ ^ 2 * ρ₁) ^ 3 = 1 := by
    rw [(hc.pow_left 2).mul_pow 3, ← pow_mul, mul_comm 2 3, pow_mul, h₀, h₁, one_pow, one_mul]
  have key := congrArg (LinearMap.trace ℝ V) (avgQ_sum hc h₀ h₁)
  simp only [map_add, avgQ_eq_smul, smul_mul_smul_comm, map_smul, smul_eq_mul, LinearMap.trace_one,
    trace_avgP h₀, trace_avgP h₁, trace_avgP hc2, trace_avgP hc3,
    (isProj_avgP_mul hc h₀ h₁).trace] at key
  have hR : (Module.finrank ℝ V : ℝ) + 3 * (Module.finrank ℝ ↥(fixedSpace ρ₀ ⊓ fixedSpace ρ₁) : ℝ) =
      Module.finrank ℝ ↥(fixedSpace ρ₀) + Module.finrank ℝ ↥(fixedSpace ρ₁) +
        Module.finrank ℝ ↥(fixedSpace (ρ₀ ^ 2 * ρ₁ ^ 2)) +
        Module.finrank ℝ ↥(fixedSpace (ρ₀ ^ 2 * ρ₁)) := by
    linarith
  exact_mod_cast hR

end CKM.NativeFirstOrder
