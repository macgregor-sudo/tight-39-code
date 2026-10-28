module

public import TCDefs
public import NativeCoordinateTracePairing
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

/-!
# A7: Gram trace inequality and Gram rank 

`gram_trace_sq_le` is the Cauchy–Schwarz step `(tr H)² ≤ 26 tr(H²)` for the Gram matrix of traceless
native vectors, proved without spectral theory: on the 26-dimensional traceless subspace the native
pairing is a positively weighted sum of 26 coordinate products (`inner_coordinates`,
`octDot_coordinates`; for traceless `x`, `Σ dᵢ² = (d₀ - d₁)²/2 + (d₀ + d₁ - 2d₂)²/6`). With
`A i k` the k-th such coordinate of `q i`, weights `w k > 0` and `M k l = Σ i, A i k * A i l`:
`Σ i ⟨q i, q i⟩ = Σ k w k M k k`, `Σ i j ⟨q i, q j⟩² = Σ k l w k w l (M k l)² ≥ Σ k (w k M k k)²`,
and `(Σ k w k M k k)² ≤ 26 Σ k (w k M k k)²`. Any equivalent exact proof is fine (for example the
pinned spectral theorem plus `rank ≤ 26`).
`rank_gram_le`: `G = U B Uᵀ` with `U i k = upperCoordinates (P i) k`, so `rank G ≤ 27`.
-/

noncomputable section

namespace CKM.NativeTightCode

open Glennie

/-- Generic weighted Gram inequality: for vectors `A i ∈ ℝⁿ` and the positively weighted pairing
`B(u, v) = Σ k, w k * u k * v k`, `(Σ i B(A i, A i))² ≤ n · Σ i j B(A i, A j)²`.
Proof: with `M k l = Σ i A i k * A i l`, the left side is `(Σ k w k M k k)²`, the right double sum
is `Σ k l w k w l (M k l)² ≥ Σ k (w k M k k)²`, and the Cauchy–Schwarz inequality
(`sq_sum_le_card_mul_sum_sq`) closes it. -/
theorem gram_weighted_trace_sq_le {N n : ℕ} (A : Fin N → Fin n → ℝ) (w : Fin n → ℝ)
    (hw : ∀ k, 0 ≤ w k) :
    (∑ i, ∑ k, w k * A i k * A i k) ^ 2 ≤
      (n : ℝ) * ∑ i, ∑ j, (∑ k, w k * A i k * A j k) ^ 2 := by
  let M : Fin n → Fin n → ℝ := fun k l => ∑ i, A i k * A i l
  have h1 : ∑ i, ∑ k, w k * A i k * A i k = ∑ k, w k * M k k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [M, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i, ∑ j, (∑ k, w k * A i k * A j k) ^ 2 =
      ∑ k, ∑ l, w k * w l * M k l ^ 2 := by
    calc ∑ i, ∑ j, (∑ k, w k * A i k * A j k) ^ 2
        = ∑ i, ∑ j, ∑ k, ∑ l, w k * w l * (A i k * A i l) * (A j k * A j l) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [sq, Finset.sum_mul_sum]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
      _ = ∑ i, ∑ k, ∑ j, ∑ l, w k * w l * (A i k * A i l) * (A j k * A j l) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ k, ∑ l, ∑ j, w k * w l * (A i k * A i l) * (A j k * A j l) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ l, ∑ j, w k * w l * (A i k * A i l) * (A j k * A j l) :=
          Finset.sum_comm
      _ = ∑ k, ∑ l, ∑ i, ∑ j, w k * w l * (A i k * A i l) * (A j k * A j l) :=
          Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ k, ∑ l, w k * w l * M k l ^ 2 := by
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          symm
          simp only [M]
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  have h3 : ∑ k, (w k * M k k) ^ 2 ≤ ∑ k, ∑ l, w k * w l * M k l ^ 2 := by
    refine Finset.sum_le_sum fun k _ => ?_
    have hs := Finset.single_le_sum (f := fun l => w k * w l * M k l ^ 2)
      (fun l _ => mul_nonneg (mul_nonneg (hw k) (hw l)) (sq_nonneg _)) (Finset.mem_univ k)
    calc (w k * M k k) ^ 2 = w k * w k * M k k ^ 2 := by ring
      _ ≤ _ := hs
  have h4 : (∑ k, w k * M k k) ^ 2 ≤ (n : ℝ) * ∑ k, (w k * M k k) ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
      (f := fun k => w k * M k k)
  rw [h1, h2]
  calc (∑ k, w k * M k k) ^ 2 ≤ (n : ℝ) * ∑ k, (w k * M k k) ^ 2 := h4
    _ ≤ (n : ℝ) * ∑ k, ∑ l, w k * w l * M k l ^ 2 := by gcongr

/-- Orthogonal linear coordinates on the traceless native subspace: `d₀ - d₁`, `d₀ + d₁ - 2d₂`,
then the 24 real octonion coordinates of `o01`, `o02`, `o12`. -/
def gramTracelessCoord (x : Albert) : Fin 26 → ℝ :=
  ![x.d0 - x.d1, x.d0 + x.d1 - 2 * x.d2,
    x.o01.1.re, x.o01.1.imI, x.o01.1.imJ, x.o01.1.imK,
    x.o01.2.re, x.o01.2.imI, x.o01.2.imJ, x.o01.2.imK,
    x.o02.1.re, x.o02.1.imI, x.o02.1.imJ, x.o02.1.imK,
    x.o02.2.re, x.o02.2.imI, x.o02.2.imJ, x.o02.2.imK,
    x.o12.1.re, x.o12.1.imI, x.o12.1.imJ, x.o12.1.imK,
    x.o12.2.re, x.o12.2.imI, x.o12.2.imJ, x.o12.2.imK]

/-- The positive weights of the native pairing in `gramTracelessCoord`. -/
def gramTracelessWeight : Fin 26 → ℝ :=
  ![1 / 2, 1 / 6, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]

theorem gramTracelessWeight_nonneg (k : Fin 26) : 0 ≤ gramTracelessWeight k := by
  fin_cases k <;> norm_num [gramTracelessWeight]

/-- On traceless vectors the native pairing is the weighted coordinate sum
(`Σ dᵢ d'ᵢ = (d₀-d₁)(d₀'-d₁')/2 + (d₀+d₁-2d₂)(d₀'+d₁'-2d₂')/6 + (tr x)(tr x')/3`). -/
theorem gram_inner_eq_weighted (x y : Albert) (hx : trace x = 0) (hy : trace y = 0) :
    Glennie.inner x y =
      ∑ k, gramTracelessWeight k * gramTracelessCoord x k * gramTracelessCoord y k := by
  have hy' := hy
  simp only [Glennie.trace] at hx hy'
  rw [Glennie.inner_coordinates, Glennie.octDot_coordinates, Glennie.octDot_coordinates,
    Glennie.octDot_coordinates]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, gramTracelessWeight, gramTracelessCoord,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  linear_combination (1 / 3 * (y.d0 + y.d1 + y.d2)) * hx

/-- `(tr H)² ≤ 26 · tr(H²)` for the Gram matrix of traceless native vectors. -/
theorem gram_trace_sq_le {N : ℕ} (q : Fin N → Albert) (hq : ∀ i, trace (q i) = 0) :
    (∑ i, inner (q i) (q i)) ^ 2 ≤ 26 * ∑ i, ∑ j, (inner (q i) (q j)) ^ 2 := by
  have key := gram_weighted_trace_sq_le (fun i => gramTracelessCoord (q i)) gramTracelessWeight
    gramTracelessWeight_nonneg
  have hij : ∀ i j, Glennie.inner (q i) (q j) =
      ∑ k, gramTracelessWeight k * gramTracelessCoord (q i) k * gramTracelessCoord (q j) k :=
    fun i j => gram_inner_eq_weighted _ _ (hq i) (hq j)
  simp only [hij]
  push_cast at key
  exact key

/-- The native Gram matrix of any family has rank at most `27`. -/
theorem rank_gram_le {N : ℕ} (P : Fin N → Albert) : (gram P).rank ≤ 27 := by
  let gU : Matrix (Fin N) (Fin 27) ℝ :=
    Matrix.of fun i k => NativePolynomial.upperCoordinates (P i) k
  let gX : Matrix (Fin 27) (Fin N) ℝ := Matrix.of fun k j =>
    (NativePolynomial.IntegralStructureConstants.coordinateTraceWeight k : ℝ) *
      NativePolynomial.upperCoordinates (P j) k
  have hG : CKM.NativeTightCode.gram P = gU * gX := by
    ext i j
    simp only [CKM.NativeTightCode.gram, gU, gX, Matrix.of_apply, Matrix.mul_apply]
    rw [show Glennie.inner (P i) (P j) = Glennie.trace (Glennie.jordan (P i) (P j)) from rfl,
      ← NativePolynomial.CoordinateMaps.coordinatePairing_upperCoordinates_eq_native_trace]
    simp only [NativePolynomial.CoordinateMaps.coordinatePairing]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hG]
  exact (Matrix.rank_mul_le_left gU gX).trans (Matrix.rank_le_width gU)

#print axioms gram_trace_sq_le
#print axioms rank_gram_le

end CKM.NativeTightCode
