module

public import TCFrame
public import TCMetric
public import TCStable
public import TCSharp

@[expose] public section

/-!
# A7 tight codes: consumer

The exact native endpoints, on the accepted compact `Glennie.Albert` (`Glennie.jordan`,
`Glennie.trace` with `trace 1 = 3`, `Glennie.inner x y = trace (jordan x y)`, unit `1`,
`Glennie.Frame`). A pure point is exactly `jordan p p = p ∧ trace p = 1`. The only hypotheses below
are purity and the distinct-pair overlap bound; nonnegative overlaps, Gram positivity and rank, row
sums, the partition premises and frame unit sums are all derived.

1. Code bound: any family of native pure points with distinct overlaps `≤ 1/3` has `≤ 39` members
   (the empty family included); the bound is attained by the accepted literal code.
2. Equality case and converse: for 39 pure points, the bound holds iff they split into thirteen actual
   native frames with cross-frame overlaps `1/3`; distinct points have zero overlap iff same frame.
3. Native chordal metric `ρ(p, q) = sqrt (⟨p - q, p - q⟩ / 2) = sqrt (1 - ⟨p, q⟩)`; overlap `≤ 1/3`
   iff `ρ ≥ sqrt (2/3)`.
4. Local stability: in the product topology of the 27 native upper coordinates, the labelled relation
   `i = j ∨ ⟨P i, P j⟩ = 0` is locally constant on the tight locus.

Not claimed here: good-phase accumulation, stabilizers or quotient dimension, the contradiction
with Cohn–Kumar–Minton Conjecture 8.4 (arXiv:1308.3188v4, p. 50), A5 charts, A6 exhaustion, the
full A7 endpoint. Attributions are in the module docstrings (CKM §2.1 p. 5 metric, Prop. 2.5 p. 8
bound, Thm 8.3 p. 49 construction; McCrimmon Thms 8.1.2/8.1.4 Peirce).
-/

noncomputable section

namespace CKM.NativeTightCodeConsumer

open Glennie CKM.NativeTightCode Topology

/-- Purity is exactly native idempotency plus trace one. -/
example (p : Albert) : IsPure p ↔ jordan p p = p ∧ trace p = 1 := Iff.rfl

/-- The overlap bound is exactly the distinct-pair native trace pairing bound. -/
example {N : ℕ} (P : Fin N → Albert) :
    OverlapBound P ↔ ∀ i j, i ≠ j → inner (P i) (P j) ≤ (1 / 3 : ℝ) := Iff.rfl

/-- The chordal distance is built from the native pairing. -/
example (p q : Albert) : chordalDist p q = Real.sqrt (inner (p - q) (p - q) / 2) := rfl

/-- The coordinates are the accepted native upper coordinates. -/
example (P : Fin 39 → Albert) (i : Fin 39) :
    codeCoords P i = NativePolynomial.upperCoordinates (P i) := rfl

/-- Derived, not assumed: overlaps of pure points are nonnegative. -/
example {p q : Albert} (hp : IsPure p) (hq : IsPure q) : 0 ≤ inner p q := overlap_nonneg hp.1 hq.1

/-- Bare zero overlap is irreflexive: every pure point has self-overlap `1`. -/
example {p : Albert} (hp : IsPure p) : inner p p ≠ 0 := by
  rw [inner_self_of_pure hp]; exact one_ne_zero

/-! ## 1. Code bound -/

theorem code_bound {N : ℕ} (P : Fin N → Albert) (hpure : ∀ i, IsPure (P i))
    (hov : ∀ i j, i ≠ j → inner (P i) (P j) ≤ (1 / 3 : ℝ)) : N ≤ 39 :=
  card_le_39 P hpure hov

example (P : Fin 0 → Albert) : 0 ≤ 39 := code_bound P (fun i => i.elim0) (fun i => i.elim0)

theorem code_bound_sharp :
    ∃ P : Fin 39 → Albert, (∀ i, IsPure (P i)) ∧ ∀ i j, i ≠ j → inner (P i) (P j) ≤ (1 / 3 : ℝ) :=
  exists_tight_code

/-! ## 2. Equality case and converse -/

theorem tight_code_iff_frames (P : Fin 39 → Albert) (hpure : ∀ i, IsPure (P i)) :
    (∀ i j, i ≠ j → inner (P i) (P j) ≤ (1 / 3 : ℝ)) ↔
      ∃ e : Fin 39 ≃ Fin 13 × Fin 3,
        (∀ h, Frame fun a => P (e.symm (h, a))) ∧
        (∀ i j, (e i).1 ≠ (e j).1 → inner (P i) (P j) = 1 / 3) :=
  overlapBound_iff_frames P hpure

theorem tight_code_frames (P : Fin 39 → Albert) (hpure : ∀ i, IsPure (P i))
    (hov : ∀ i j, i ≠ j → inner (P i) (P j) ≤ (1 / 3 : ℝ)) :
    ∃ e : Fin 39 ≃ Fin 13 × Fin 3,
      (∀ h, Frame fun a => P (e.symm (h, a))) ∧
      (∀ i j, (e i).1 ≠ (e j).1 → inner (P i) (P j) = 1 / 3) ∧
      (∀ i j, i ≠ j → (inner (P i) (P j) = 0 ↔ (e i).1 = (e j).1)) :=
  tight_frame_decomposition P hpure hov

/-! ## 3. Native chordal metric -/

theorem chordal_formula {p q : Albert} (hp : IsPure p) (hq : IsPure q) :
    Real.sqrt (inner (p - q) (p - q) / 2) = Real.sqrt (1 - inner p q) :=
  chordalDist_eq hp hq

theorem overlap_iff_distance {p q : Albert} (hp : IsPure p) (hq : IsPure q) :
    inner p q ≤ 1 / 3 ↔ Real.sqrt (2 / 3) ≤ Real.sqrt (inner (p - q) (p - q) / 2) :=
  overlap_le_iff_chordalDist hp hq

theorem code_bound_distance {N : ℕ} (P : Fin N → Albert) (hpure : ∀ i, IsPure (P i))
    (hd : ∀ i j, i ≠ j → Real.sqrt (2 / 3) ≤ chordalDist (P i) (P j)) : N ≤ 39 :=
  card_le_39_of_chordalDist P hpure hd

/-! ## 4. Local stability of the labelled partition -/

theorem partition_locally_constant :
    IsLocallyConstant fun C : tightLocus => fun i j : Fin 39 =>
      i = j ∨ inner (codePoint C.1 i) (codePoint C.1 j) = 0 :=
  isLocallyConstant_zeroRel

theorem partition_relative_nhds {C : Fin 39 → Fin 27 → ℝ} (hC : C ∈ tightLocus) :
    ∀ᶠ C' in 𝓝[tightLocus] C, ∀ i j,
      (i = j ∨ inner (codePoint C' i) (codePoint C' j) = 0) ↔
        (i = j ∨ inner (codePoint C i) (codePoint C j) = 0) :=
  zeroRel_eventually_eq hC

theorem partition_native_nhds (P : Fin 39 → Albert) (hpure : ∀ i, IsPure (P i))
    (hov : ∀ i j, i ≠ j → inner (P i) (P j) ≤ (1 / 3 : ℝ)) :
    ∃ U : Set (Fin 39 → Fin 27 → ℝ), IsOpen U ∧
      (fun i => NativePolynomial.upperCoordinates (P i)) ∈ U ∧
      ∀ Q : Fin 39 → Albert, (∀ i, IsPure (Q i)) →
        (∀ i j, i ≠ j → inner (Q i) (Q j) ≤ (1 / 3 : ℝ)) →
        (fun i => NativePolynomial.upperCoordinates (Q i)) ∈ U →
        ∀ i j, (i = j ∨ inner (Q i) (Q j) = 0) ↔ (i = j ∨ inner (P i) (P j) = 0) :=
  zero_pairs_locally_constant P hpure hov

#print axioms code_bound
#print axioms code_bound_sharp
#print axioms tight_code_iff_frames
#print axioms tight_code_frames
#print axioms chordal_formula
#print axioms overlap_iff_distance
#print axioms code_bound_distance
#print axioms partition_locally_constant
#print axioms partition_relative_nhds
#print axioms partition_native_nhds

end CKM.NativeTightCodeConsumer
