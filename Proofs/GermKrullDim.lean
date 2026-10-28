module

/-
Krull dimension of the actual convergent germ ring.
First-party composition over pinned Mathlib and accepted project modules; no upstream
proof body copied. Pin: Lean v4.35.0-rc2, Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Imports: AnalyticPullback, ConvergentGermSCVDomain (accepted SCV
identity-principle consumer; SCV source by Bastiaan J Braams, Apache-2.0, with its notices),
ConvergentGermLocalRing, ConvergentResidualJetLength, ConvergentGermJetDimensions and the
accepted FLT growth port GrowthDimension.Consumer (original by Akhil Mathew, Apache-2.0).
Thank you to those authors and the Lean and Mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.

Content. `ringKrullDim (GermRing n) = n`.
* Lower bound: the pullbacks along the coordinate truncations
  `π_k x = (x_0, …, x_{k-1}, 0, …, 0)` are algebra maps `GermRing n → GermRing n` into a
  domain, so their kernels are primes; `k ↦ ker π_k` is antitone and strictly so, witnessed
  by the coordinate germs. This is a chain of `n + 1` primes. No Hadamard division, no
  quotient identification `GermRing n ⧸ (z_k) ≃ GermRing (n-1)`, no "dim ≥ growth degree".
* Upper bound: jets of length at most `C(N+n, n) ≤ (N+1)^n` and the accepted FLT growth port.
-/
public import AnalyticPullback
public import ConvergentGermSCVDomain
public import ConvergentGermLocalRing
public import ConvergentResidualJetLength
public import ConvergentGermJetDimensions
public import GrowthDimension.Consumer
public import Mathlib.Order.KrullDimension
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

noncomputable section

open Filter ConvergentResidualJets
open scoped Topology

namespace GermKrullDim

variable {n : ℕ}

/-- The coordinate truncation keeping the first `k` coordinates. -/
def trunc (n k : ℕ) : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun j : Fin n =>
    if (j : ℕ) < k then ContinuousLinearMap.proj j else 0

theorem trunc_apply (k : ℕ) (x : Fin n → ℂ) (j : Fin n) :
    trunc n k x j = if (j : ℕ) < k then x j else 0 := by
  unfold trunc
  by_cases h : (j : ℕ) < k <;> simp [h]

theorem trunc_comp_of_le {k k' : ℕ} (hk : k' ≤ k) (x : Fin n → ℂ) :
    trunc n k (trunc n k' x) = trunc n k' x := by
  funext j
  simp only [trunc_apply]
  by_cases h : (j : ℕ) < k'
  · simp [h, lt_of_lt_of_le h hk]
  · simp [h]

/-- Pullback of germs along the truncation, an algebra map into the same germ ring. -/
def truncPullback (n k : ℕ) : GermRing n →ₐ[ℂ] GermRing n :=
  AnalyticPullback.pullback (trunc n k) ((trunc n k).analyticAt 0) (map_zero _)

theorem exists_ofAnalyticAt (f : GermRing n) :
    ∃ g : (Fin n → ℂ) → ℂ, ∃ hg : AnalyticAt ℂ g 0, f = ofAnalyticAt g hg := by
  obtain ⟨g, hg, hgf⟩ := f.property
  exact ⟨g, hg, Subtype.ext hgf.symm⟩

theorem mem_ker_truncPullback_iff (k : ℕ) (g : (Fin n → ℂ) → ℂ) (hg : AnalyticAt ℂ g 0) :
    ofAnalyticAt g hg ∈ RingHom.ker (truncPullback n k) ↔
      (g ∘ trunc n k) =ᶠ[𝓝 0] (0 : (Fin n → ℂ) → ℂ) := by
  rw [RingHom.mem_ker]
  change AnalyticPullback.pullback (trunc n k) _ _ (ofAnalyticAt g hg) = 0 ↔ _
  rw [AnalyticPullback.pullback_ofAnalyticAt, AnalyticPullback.ofAnalyticAt_eq_zero_iff]

/-- Fewer kept coordinates kill more germs. -/
theorem ker_truncPullback_mono {k k' : ℕ} (hk : k' ≤ k) :
    RingHom.ker (truncPullback n k) ≤ RingHom.ker (truncPullback n k') := by
  intro f hf
  obtain ⟨g, hg, rfl⟩ := exists_ofAnalyticAt f
  rw [mem_ker_truncPullback_iff] at hf ⊢
  have hT : Tendsto (trunc n k') (𝓝 (0 : Fin n → ℂ)) (𝓝 0) := by
    have h := (trunc n k').continuous.tendsto (0 : Fin n → ℂ)
    rwa [map_zero] at h
  have h2 := hf.comp_tendsto hT
  have hfun : (g ∘ trunc n k) ∘ trunc n k' = g ∘ trunc n k' := by
    funext x
    simp only [Function.comp_apply, trunc_comp_of_le hk]
  rw [hfun] at h2
  exact h2

/-- A coordinate function is not eventually zero at the origin. -/
theorem coordinate_fun_not_eventually_zero (j : Fin n) :
    ¬ (fun z : Fin n → ℂ => z j) =ᶠ[𝓝 0] (0 : (Fin n → ℂ) → ℂ) := by
  intro h
  have : Nonempty (Fin n) := ⟨j⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h
  have hy : dist (fun _ : Fin n => ((ε / 2 : ℝ) : ℂ)) 0 < ε := by
    rw [dist_zero_right, pi_norm_const, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    linarith
  have h0 := hball hy
  simp only [Pi.zero_apply, Complex.ofReal_eq_zero] at h0
  linarith

theorem coordinate_mem_ker_truncPullback {k : ℕ} (j : Fin n) (hj : k ≤ (j : ℕ)) :
    coordinate n j ∈ RingHom.ker (truncPullback n k) := by
  refine (mem_ker_truncPullback_iff k (fun z : Fin n → ℂ => z j)
    ((ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt 0)).mpr ?_
  refine Filter.Eventually.of_forall fun x => ?_
  simp [trunc_apply, Nat.not_lt.mpr hj]

theorem coordinate_not_mem_ker_truncPullback {k : ℕ} (j : Fin n) (hj : (j : ℕ) < k) :
    coordinate n j ∉ RingHom.ker (truncPullback n k) := by
  refine fun hmem => (mem_ker_truncPullback_iff k (fun z : Fin n → ℂ => z j)
    ((ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).analyticAt 0)).not.mpr ?_ hmem
  have hfun : ((fun z : Fin n → ℂ => z j) ∘ trunc n k) = fun z => z j := by
    funext x
    simp [trunc_apply, hj]
  rw [hfun]
  exact coordinate_fun_not_eventually_zero j

/-- The truncation kernels as points of the prime spectrum (the germ ring is a domain). -/
def truncPrime (n k : ℕ) : PrimeSpectrum (GermRing n) :=
  letI := ConvergentGermSCVBridge.germRing_isDomain n
  ⟨RingHom.ker (truncPullback n k), RingHom.ker_isPrime _⟩

/-- The chain `ker π_n < ker π_{n-1} < … < ker π_0` of primes. -/
def truncChain (n : ℕ) : Fin (n + 1) → PrimeSpectrum (GermRing n) :=
  fun i => truncPrime n (n - i)

theorem truncChain_strictMono (n : ℕ) : StrictMono (truncChain n) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  rw [← PrimeSpectrum.asIdeal_lt_asIdeal, IsConcreteLE.lt_iff_le_and_exists]
  have hi := i.isLt
  refine ⟨ker_truncPullback_mono (by simp only [Fin.val_succ, Fin.val_castSucc]; omega), ?_⟩
  refine ⟨coordinate n ⟨n - i - 1, by omega⟩, ?_, ?_⟩
  · exact coordinate_mem_ker_truncPullback _ (by simp only [Fin.val_succ]; omega)
  · exact coordinate_not_mem_ker_truncPullback _ (by simp only [Fin.val_castSucc]; omega)

/-- **Lower bound.** -/
theorem le_ringKrullDim_germRing (n : ℕ) : (n : WithBot ℕ∞) ≤ ringKrullDim (GermRing n) :=
  Order.LTSeries.length_le_krullDim (LTSeries.mk n (truncChain n) (truncChain_strictMono n))

/-- Jets of the germ ring have length at most `C(N+n, n)`. -/
theorem germJet_length_le (n N : ℕ) :
    Module.length (GermRing n) (GermRing n ⧸ vanishingIdeal n ^ (N + 1)) ≤
      ((N + n).choose n : ℕ∞) := by
  have hI : analyticJetIdeal (⊥ : Ideal (Poly n)) N = vanishingIdeal n ^ (N + 1) := by
    simp [analyticJetIdeal, Ideal.map_bot]
  have h := ConvergentResidualJetLength.analyticJet_length_le_finrank (⊥ : Ideal (Poly n)) N
  rw [hI, ConvergentGermJetDimensions.germJet_finrank] at h
  exact h

/-- **Upper bound.** Noetherianity is the accepted SCV theorem
`ConvergentGermSCVBridge.germRing_isNoetherianRing`, passed as an instance argument here
because its import closure is not in the local Mathlib mirror (see `GermKrullDimSCV.lean`). -/
theorem ringKrullDim_germRing_le (n : ℕ) [IsNoetherianRing (GermRing n)] :
    ringKrullDim (GermRing n) ≤ (n : WithBot ℕ∞) := by
  apply GrowthDimension.ringKrullDim_le_of_shifted_bound (C := 1)
  intro N
  rw [ConvergentGermLocalRing.maximalIdeal_eq_vanishingIdeal]
  refine (germJet_length_le n N).trans ?_
  rw [one_mul]
  exact ENat.natCast_le_natCast.mpr (Nat.choose_add_le_add_one_pow N n)

/-- **The Krull dimension of the actual `n`-variable convergent germ ring is `n`.** -/
theorem ringKrullDim_germRing (n : ℕ) [IsNoetherianRing (GermRing n)] : ringKrullDim (GermRing n) = (n : WithBot ℕ∞) :=
  le_antisymm (ringKrullDim_germRing_le n) (le_ringKrullDim_germRing n)

/-- A supplied surjection onto the 62-variable germ ring has a 62-dimensional quotient. -/
theorem ringKrullDim_quotient_ker_of_surjective {m d : ℕ} [IsNoetherianRing (GermRing d)] (ρ : GermRing m →ₐ[ℂ] GermRing d)
    (hρ : Function.Surjective ρ) :
    ringKrullDim (GermRing m ⧸ RingHom.ker ρ.toRingHom) = (d : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hρ)]
  exact ringKrullDim_germRing d

end GermKrullDim

#print axioms GermKrullDim.le_ringKrullDim_germRing
#print axioms GermKrullDim.ringKrullDim_germRing_le
#print axioms GermKrullDim.ringKrullDim_germRing
#print axioms GermKrullDim.ringKrullDim_quotient_ker_of_surjective
