-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.QuietDecay.Lift.Recentre
import AVRegularity.CycleComparison.Residual.Jets.Lift
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public noncomputable section

section
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! The Schur test for the mass-conjugated Schur sums: sums, and left or right products with an
envelope matrix whose plain row and column sums are at most `Θ`. -/

section
variable {ι : Type*} [Fintype ι]

/-- The mass-conjugation weight `√(π u / π v)`. -/
def massW (π : ι → ℝ) (v u : ι) : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt (π u / π v))

omit [Fintype ι] in
theorem massW_mul (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (v w u : ι) :
    massW π v u = massW π v w * massW π w u := by
  unfold massW
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← Real.sqrt_mul (div_nonneg (hπ w).le (hπ v).le)]
  congr 2
  field_simp [(hπ w).ne']

theorem rowSum_le_schurSums (π : ι → ℝ) (N : ι → ι → ℝ≥0∞) (v : ι) :
    ∑ u, massW π v u * N v u ≤ schurSums π N :=
  (le_iSup (fun v => ∑ u, massW π v u * N v u) v).trans (le_max_left _ _)

theorem colSum_le_schurSums (π : ι → ℝ) (N : ι → ι → ℝ≥0∞) (u : ι) :
    ∑ v, massW π v u * N v u ≤ schurSums π N :=
  (le_iSup (fun u => ∑ v, massW π v u * N v u) u).trans (le_max_right _ _)

theorem schurSums_le_of (π : ι → ℝ) (N : ι → ι → ℝ≥0∞) (B : ℝ≥0∞)
    (hr : ∀ v, ∑ u, massW π v u * N v u ≤ B) (hc : ∀ u, ∑ v, massW π v u * N v u ≤ B) :
    schurSums π N ≤ B :=
  max_le (iSup_le hr) (iSup_le hc)

theorem schurSums_add_le (π : ι → ℝ) (N M : ι → ι → ℝ≥0∞) :
    schurSums π (fun v u => N v u + M v u) ≤ schurSums π N + schurSums π M := by
  refine schurSums_le_of π _ _ (fun v => ?_) (fun u => ?_)
  · simp_rw [mul_add, Finset.sum_add_distrib]
    exact add_le_add (rowSum_le_schurSums π N v) (rowSum_le_schurSums π M v)
  · simp_rw [mul_add, Finset.sum_add_distrib]
    exact add_le_add (colSum_le_schurSums π N u) (colSum_le_schurSums π M u)

theorem schurSums_mono' (π : ι → ℝ) {N M : ι → ι → ℝ≥0∞} (h : ∀ v u, N v u ≤ M v u) :
    schurSums π N ≤ schurSums π M :=
  schurSums_le_of π _ _ (fun v => (Finset.sum_le_sum fun u _ => by gcongr; exact h v u).trans
    (rowSum_le_schurSums π M v)) (fun u => (Finset.sum_le_sum fun v _ => by gcongr; exact h v u).trans
    (colSum_le_schurSums π M u))

theorem schurSums_const_mul (π : ι → ℝ) (c : ℝ≥0∞) (N : ι → ι → ℝ≥0∞) :
    schurSums π (fun v u => c * N v u) ≤ c * schurSums π N :=
  schurSums_le_of π _ _ (fun v => by
      rw [show ∑ u, massW π v u * (c * N v u) = c * ∑ u, massW π v u * N v u by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by ring]
      exact mul_le_mul_of_nonneg_left (rowSum_le_schurSums π N v) zero_le)
    (fun u => by
      rw [show ∑ v, massW π v u * (c * N v u) = c * ∑ v, massW π v u * N v u by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring]
      exact mul_le_mul_of_nonneg_left (colSum_le_schurSums π N u) zero_le)

/-- The Schur test for a left product with an envelope matrix. -/
theorem schurSums_left_mul_le (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (B N : ι → ι → ℝ≥0∞)
    (b : ι → ι → ℝ≥0∞) (Θ : ℝ≥0∞) (hB : ∀ v w, massW π v w * B v w ≤ b v w)
    (hrow : ∀ v, ∑ w, b v w ≤ Θ) (hcol : ∀ w, ∑ v, b v w ≤ Θ) :
    schurSums π (fun v u => ∑ w, B v w * N w u) ≤ Θ * schurSums π N := by
  refine schurSums_le_of π _ _ (fun v => ?_) (fun u => ?_)
  · calc ∑ u, massW π v u * ∑ w, B v w * N w u
        = ∑ w, (massW π v w * B v w) * ∑ u, massW π w u * N w u := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun u _ => ?_
          rw [massW_mul π hπ v w u]
          ring
      _ ≤ ∑ w, b v w * schurSums π N :=
          Finset.sum_le_sum fun w _ => mul_le_mul' (hB v w) (rowSum_le_schurSums π N w)
      _ = (∑ w, b v w) * schurSums π N := by rw [Finset.sum_mul]
      _ ≤ Θ * schurSums π N := mul_le_mul_of_nonneg_right (hrow v) zero_le
  · calc ∑ v, massW π v u * ∑ w, B v w * N w u
        = ∑ w, (∑ v, massW π v w * B v w) * (massW π w u * N w u) := by
          simp_rw [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => ?_
          rw [massW_mul π hπ v w u]
          ring
      _ ≤ ∑ w, Θ * (massW π w u * N w u) :=
          Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_right
            ((Finset.sum_le_sum fun v _ => hB v w).trans (hcol w)) zero_le
      _ = Θ * ∑ w, massW π w u * N w u := by rw [Finset.mul_sum]
      _ ≤ Θ * schurSums π N := mul_le_mul_of_nonneg_left (colSum_le_schurSums π N u) zero_le

/-- The Schur test for a right product with an envelope matrix. -/
theorem schurSums_right_mul_le (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (N B : ι → ι → ℝ≥0∞)
    (b : ι → ι → ℝ≥0∞) (Θ : ℝ≥0∞) (hB : ∀ w u, massW π w u * B w u ≤ b w u)
    (hrow : ∀ w, ∑ u, b w u ≤ Θ) (hcol : ∀ u, ∑ w, b w u ≤ Θ) :
    schurSums π (fun v u => ∑ w, N v w * B w u) ≤ Θ * schurSums π N := by
  refine schurSums_le_of π _ _ (fun v => ?_) (fun u => ?_)
  · calc ∑ u, massW π v u * ∑ w, N v w * B w u
        = ∑ w, (massW π v w * N v w) * ∑ u, massW π w u * B w u := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun u _ => ?_
          rw [massW_mul π hπ v w u]
          ring
      _ ≤ ∑ w, (massW π v w * N v w) * Θ :=
          Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left
            ((Finset.sum_le_sum fun u _ => hB w u).trans (hrow w)) zero_le
      _ = Θ * ∑ w, massW π v w * N v w := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ Θ * schurSums π N := mul_le_mul_of_nonneg_left (rowSum_le_schurSums π N v) zero_le
  · calc ∑ v, massW π v u * ∑ w, N v w * B w u
        = ∑ w, (massW π w u * B w u) * ∑ v, massW π v w * N v w := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => ?_
          rw [massW_mul π hπ v w u]
          ring
      _ ≤ ∑ w, b w u * schurSums π N :=
          Finset.sum_le_sum fun w _ => mul_le_mul' (hB w u) (colSum_le_schurSums π N w)
      _ = (∑ w, b w u) * schurSums π N := by rw [Finset.sum_mul]
      _ ≤ Θ * schurSums π N := mul_le_mul_of_nonneg_right (hcol u) zero_le
end

/-! The amplitude recursion of the triangular lift system, in Schur sums: if the amplitude matrix of
the level `(hh, n)` is bounded by its entrance trace, the amplitudes of the lower degrees of the same
grade, and the left and right envelope products of the amplitudes of the previous grade, then its
Schur sum is bounded by `C Σ_{b ≤ hh} Θ^{hh-b} I_b`. -/

section
variable {ι : Type*} [Fintype ι]

/-- The amplitude recursion hypothesis. -/
structure AmpRec (π : ι → ℝ) (N H : ℕ) (K Θ : ℝ≥0∞) (I : ℕ → ℝ≥0∞)
    (A T : ℕ → ℕ → ι → ι → ℝ≥0∞) (B B' b : ι → ι → ℝ≥0∞) : Prop where
  mass_pos : ∀ v, 0 < π v
  trace : ∀ hh, hh ≤ H → ∀ n, schurSums π (T hh n) ≤ I hh
  envL : ∀ v w, massW π v w * B v w ≤ b v w
  envR : ∀ w u, massW π w u * B' w u ≤ b w u
  row : ∀ v, ∑ w, b v w ≤ Θ
  col : ∀ w, ∑ v, b v w ≤ Θ
  bound : ∀ hh, hh ≤ H → ∀ n, n ≤ N → ∀ v u,
    A hh n v u ≤ K * (T hh n v u + ∑ n' ∈ Finset.range n, A hh n' v u +
      (if hh = 0 then 0 else ∑ n' ∈ Finset.range (N + 1),
        (∑ w, B v w * A (hh - 1) n' w u + ∑ w, A (hh - 1) n' v w * B' w u)))

/-- The Schur sums of the amplitudes of one grade, summed over the degrees `≤ n`. -/
def gradeSum (π : ι → ℝ) (A : ℕ → ℕ → ι → ι → ℝ≥0∞) (hh n : ℕ) : ℝ≥0∞ :=
  ∑ n' ∈ Finset.range (n + 1), schurSums π (A hh n')

theorem schurSums_sum_le (π : ι → ℝ) (s : Finset ℕ) (N : ℕ → ι → ι → ℝ≥0∞) :
    schurSums π (fun v u => ∑ n ∈ s, N n v u) ≤ ∑ n ∈ s, schurSums π (N n) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact schurSums_le_of π _ _ (fun v => by simp) (fun u => by simp)
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (schurSums_add_le π _ _).trans (add_le_add le_rfl ih)

/-- The level bound: Schur sum of one level by the trace and the lower data. -/
theorem schur_level_le {π : ι → ℝ} {N H : ℕ} {K Θ : ℝ≥0∞} {I : ℕ → ℝ≥0∞}
    {A T : ℕ → ℕ → ι → ι → ℝ≥0∞} {B B' b : ι → ι → ℝ≥0∞}
    (R : AmpRec π N H K Θ I A T B B' b) (hh : ℕ) (hhH : hh ≤ H) (n : ℕ) (hn : n ≤ N) :
    schurSums π (A hh n) ≤ K * (I hh + ∑ n' ∈ Finset.range n, schurSums π (A hh n') +
      (if hh = 0 then 0 else 2 * Θ * gradeSum π A (hh - 1) N)) := by
  have hle := schurSums_mono' π (R.bound hh hhH n hn)
  refine hle.trans ((schurSums_const_mul π K _).trans (mul_le_mul_of_nonneg_left ?_ zero_le))
  refine (schurSums_add_le π _ _).trans (add_le_add ((schurSums_add_le π _ _).trans
    (add_le_add (R.trace hh hhH n) (schurSums_sum_le π _ _))) ?_)
  split_ifs with h0
  · exact (schurSums_le_of π _ 0 (fun v => by simp) (fun u => by simp))
  · refine (schurSums_sum_le π _ _).trans ?_
    unfold gradeSum
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n' _ => ?_
    refine (schurSums_add_le π _ _).trans ?_
    rw [two_mul, add_mul]
    exact add_le_add
      (schurSums_left_mul_le π R.mass_pos B (A (hh - 1) n') b Θ R.envL R.row R.col)
      (schurSums_right_mul_le π R.mass_pos (A (hh - 1) n') B' b Θ R.envR R.row R.col)

/-- Within one grade: the degree sums grow by the factor `1 + K` per degree. -/
theorem gradeSum_le {π : ι → ℝ} {N H : ℕ} {K Θ : ℝ≥0∞} {I : ℕ → ℝ≥0∞}
    {A T : ℕ → ℕ → ι → ι → ℝ≥0∞} {B B' b : ι → ι → ℝ≥0∞}
    (R : AmpRec π N H K Θ I A T B B' b) (hh : ℕ) (hhH : hh ≤ H) :
    ∀ n, n ≤ N → gradeSum π A hh n + (I hh + (if hh = 0 then 0 else 2 * Θ * gradeSum π A (hh - 1) N)) ≤
      (1 + K) ^ (n + 1) * (I hh + (if hh = 0 then 0 else 2 * Θ * gradeSum π A (hh - 1) N)) := by
  set M := I hh + (if hh = 0 then 0 else 2 * Θ * gradeSum π A (hh - 1) N)
  intro n
  induction n with
  | zero =>
      intro _
      have h0 := schur_level_le R hh hhH 0 (Nat.zero_le _)
      simp only [Finset.range_zero, Finset.sum_empty, add_zero] at h0
      simp only [gradeSum, zero_add, Finset.range_one, Finset.sum_singleton, pow_one]
      calc schurSums π (A hh 0) + M ≤ K * M + M := by
            gcongr
        _ = (1 + K) * M := by ring
  | succ n ih =>
      intro hn
      have h1 := schur_level_le R hh hhH (n + 1) hn
      have hS : ∑ n' ∈ Finset.range (n + 1), schurSums π (A hh n') = gradeSum π A hh n := rfl
      rw [hS] at h1
      have ih' := ih (by omega)
      have e : gradeSum π A hh (n + 1) = gradeSum π A hh n + schurSums π (A hh (n + 1)) := by
        unfold gradeSum; rw [Finset.sum_range_succ]
      rw [e]
      calc gradeSum π A hh n + schurSums π (A hh (n + 1)) + M
          ≤ gradeSum π A hh n + K * (I hh + gradeSum π A hh n +
              (if hh = 0 then 0 else 2 * Θ * gradeSum π A (hh - 1) N)) + M := by gcongr
        _ = (1 + K) * (gradeSum π A hh n + M) := by simp only [M]; ring
        _ ≤ (1 + K) * ((1 + K) ^ (n + 1) * M) := by gcongr
        _ = (1 + K) ^ (n + 1 + 1) * M := by ring

/-- **The amplitude recursion closes**: every level is bounded by `C Σ_{b ≤ hh} Θ^{hh-b} I_b`. -/
theorem schur_amplitude_le {π : ι → ℝ} {N H : ℕ} {K Θ : ℝ≥0∞} {I : ℕ → ℝ≥0∞}
    {A T : ℕ → ℕ → ι → ι → ℝ≥0∞} {B B' b : ι → ι → ℝ≥0∞}
    (R : AmpRec π N H K Θ I A T B B' b) :
    ∀ hh, hh ≤ H → gradeSum π A hh N ≤
      (1 + K) ^ (N + 1) * (2 * (1 + K) ^ (N + 1)) ^ hh *
        ∑ b' ∈ Finset.range (hh + 1), Θ ^ (hh - b') * I b' := by
  set c := (1 + K) ^ (N + 1)
  have hc1 : 1 ≤ c := one_le_pow₀ (le_add_right le_rfl)
  intro hh
  induction hh with
  | zero =>
      intro hH
      have h := gradeSum_le R 0 hH N le_rfl
      simp only [ite_true, add_zero] at h
      simp only [pow_zero, mul_one, zero_add, Finset.range_one, Finset.sum_singleton,
        Nat.sub_self]
      exact le_self_add.trans (h.trans (le_of_eq (by ring)))
  | succ hh ih =>
      intro hH
      have h := gradeSum_le R (hh + 1) hH N le_rfl
      simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel] at h
      have ih' := ih (by omega)
      calc gradeSum π A (hh + 1) N ≤ c * (I (hh + 1) + 2 * Θ * gradeSum π A hh N) :=
            le_trans le_self_add h
        _ ≤ c * (I (hh + 1) + 2 * Θ * (c * (2 * c) ^ hh *
              ∑ b' ∈ Finset.range (hh + 1), Θ ^ (hh - b') * I b')) := by gcongr
        _ ≤ c * (2 * c) ^ (hh + 1) * ∑ b' ∈ Finset.range (hh + 1 + 1),
              Θ ^ (hh + 1 - b') * I b' := by
            rw [Finset.sum_range_succ (f := fun b' => Θ ^ (hh + 1 - b') * I b'), Nat.sub_self,
              pow_zero, one_mul]
            have hθ : ∑ b' ∈ Finset.range (hh + 1), Θ ^ (hh + 1 - b') * I b' =
                Θ * ∑ b' ∈ Finset.range (hh + 1), Θ ^ (hh - b') * I b' := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun b' hb' => ?_
              have : hh + 1 - b' = (hh - b') + 1 := by
                have := Finset.mem_range.1 hb'; omega
              rw [this, pow_succ]; ring
            rw [hθ]
            have h2c : 1 ≤ 2 * c := le_trans hc1 (by
              calc c = 1 * c := (one_mul c).symm
                _ ≤ 2 * c := by gcongr; norm_num)
            have hpow : 1 ≤ (2 * c) ^ (hh + 1) := one_le_pow₀ h2c
            calc c * (I (hh + 1) + 2 * Θ * (c * (2 * c) ^ hh *
                  ∑ b' ∈ Finset.range (hh + 1), Θ ^ (hh - b') * I b'))
                = c * I (hh + 1) + c * (2 * c) ^ (hh + 1) *
                    (Θ * ∑ b' ∈ Finset.range (hh + 1), Θ ^ (hh - b') * I b') := by ring
              _ ≤ c * (2 * c) ^ (hh + 1) * I (hh + 1) + c * (2 * c) ^ (hh + 1) *
                    (Θ * ∑ b' ∈ Finset.range (hh + 1), Θ ^ (hh - b') * I b') := by
                  gcongr
                  exact le_mul_of_one_le_right zero_le hpow
              _ = c * (2 * c) ^ (hh + 1) * (Θ * ∑ b' ∈ Finset.range (hh + 1),
                    Θ ^ (hh - b') * I b' + I (hh + 1)) := by ring
end

end AVRegularity.QuietDecay
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! The edge envelope of the amplitude recursion: the pointwise edge jets of the quiet sources
(slow orders `≤ r`, at the fast point `0`) are bounded uniformly on the window by `envB`, and
`massW π v w · envB v w ≤ (Σ_{i≤r} max (C_j i 0) 0) b_{vw}` by the scaled jet envelope (`λ ≤ 1`). -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- The uniform edge envelope on the times `I` through the slow order `r`. -/
def envB (edge : ConstituentEdges D h) (I : Set ℝ) (r : ℕ) (v w : ι) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range (r + 1), ∑ d : Finset.Icc 2 D, ((edge v w d).map fun γ =>
    ENNReal.ofReal ‖γ.map‖ * ∑ α, jetSup I i 0 (γ.coeff α)).sum

theorem norm_iteratedFDeriv_slice_le_jetSup {I : Set ℝ} {f : ℝ → Vec 2 → Vec 2 → Vec 2} {σ : ℝ}
    (hσ : σ ∈ I) (i : ℕ) (X : Vec 2) :
    ‖iteratedFDeriv ℝ i (fun Y => f σ Y 0) X‖ₑ ≤ jetSup I i 0 f := by
  have e : (fun Y => iteratedFDeriv ℝ 0 (f σ Y) 0) =
      (continuousMultilinearCurryFin0 ℝ (Vec 2) (Vec 2)).symm ∘ fun Y => f σ Y 0 := by
    funext Y
    ext
    simp
  have h1 : ‖iteratedFDeriv ℝ i (fun Y => iteratedFDeriv ℝ 0 (f σ Y) 0) X‖ =
      ‖iteratedFDeriv ℝ i (fun Y => f σ Y 0) X‖ := by
    rw [e]
    exact LinearIsometryEquiv.norm_iteratedFDeriv_comp_left _ _ _ _
  unfold jetSup
  refine le_trans ?_ (le_iSup₂_of_le σ hσ (le_iSup_of_le X (le_iSup_of_le 0 le_rfl)))
  rw [← ofReal_norm, ← ofReal_norm, h1]

omit [Fintype ι] in
/-- The pointwise edge sum of the quiet sources is at most the envelope. -/
theorem edgeSum_le_envB (edge : ConstituentEdges D h) {I : Set ℝ} {σ : ℝ} (hσ : σ ∈ I) (X : Vec 2)
    (v w : ι) (r : ℕ) :
    ∑ d : Finset.Icc 2 D, ((edge v w d).map fun γ => ‖γ.map‖ₑ *
      ∑ α : DerivativeWord2 (d.1 - 1), ∑ i ∈ Finset.range (r + 1),
        ‖iteratedFDeriv ℝ i (fun Y => γ.coeff α σ Y 0) X‖ₑ).sum ≤ envB edge I r v w := by
  unfold envB
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun d _ => ?_
  have hl : ∀ L : List (Constituent d.1 (h w) (h v)),
      (L.map fun γ => ‖γ.map‖ₑ * ∑ α : DerivativeWord2 (d.1 - 1), ∑ i ∈ Finset.range (r + 1),
        ‖iteratedFDeriv ℝ i (fun Y => γ.coeff α σ Y 0) X‖ₑ).sum ≤
      ∑ i ∈ Finset.range (r + 1), (L.map fun γ =>
        ENNReal.ofReal ‖γ.map‖ * ∑ α, jetSup I i 0 (γ.coeff α)).sum := by
    intro L
    induction L with
    | nil => simp
    | cons γ L ih =>
        simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
        refine add_le_add ?_ ih
        rw [← ofReal_norm]
        calc ENNReal.ofReal ‖γ.map‖ * ∑ α : DerivativeWord2 (d.1 - 1), ∑ i ∈ Finset.range (r + 1),
              ‖iteratedFDeriv ℝ i (fun Y => γ.coeff α σ Y 0) X‖ₑ
            = ∑ i ∈ Finset.range (r + 1), ∑ α : DerivativeWord2 (d.1 - 1), ENNReal.ofReal ‖γ.map‖ *
              ‖iteratedFDeriv ℝ i (fun Y => γ.coeff α σ Y 0) X‖ₑ := by
              rw [Finset.mul_sum]; simp_rw [Finset.mul_sum]; exact Finset.sum_comm
          _ ≤ ∑ i ∈ Finset.range (r + 1), ENNReal.ofReal ‖γ.map‖ *
              ∑ α : DerivativeWord2 (d.1 - 1), jetSup I i 0 (γ.coeff α) := by
              refine Finset.sum_le_sum fun i _ => ?_
              rw [Finset.mul_sum]
              exact Finset.sum_le_sum fun α _ => mul_le_mul_of_nonneg_left
                (norm_iteratedFDeriv_slice_le_jetSup hσ i X) zero_le
  exact hl _

/-- The envelope constant. -/
def envC (Cj : ℕ → ℕ → ℝ) (r : ℕ) : ℝ := ∑ i ∈ Finset.range (r + 1), max (Cj i 0) 0

theorem envC_nonneg (Cj : ℕ → ℕ → ℝ) (r : ℕ) : 0 ≤ envC Cj r :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

/-- **The weighted envelope is majorized by the edge matrix.** -/
theorem massW_envB_le {π : ι → ℝ} {edge : ConstituentEdges D h} {I : Set ℝ} {lam : ℝ}
    {Cj : ℕ → ℕ → ℝ} {Ks Ls : ℕ} {b : ι → ι → ℝ} {Θ : ℝ}
    (henv : IsScaledJetEnvelope π edge I lam Cj Ks Ls b Θ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    {r : ℕ} (hr : r ≤ Ks) (v w : ι) :
    massW π v w * envB edge I r v w ≤ ENNReal.ofReal (envC Cj r * b v w) := by
  unfold envB envC
  rw [Finset.mul_sum, Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun i _ =>
    mul_nonneg (le_max_right _ _) (henv.nonneg v w)]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ Ks := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hr
  refine (henv.jets v w i hi' 0 (Nat.zero_le _)).trans (ENNReal.ofReal_le_ofReal ?_)
  have hb := henv.nonneg v w
  have hl : lam ^ i ≤ 1 := pow_le_one₀ hlam0 hlam1
  have hl0 : 0 ≤ lam ^ i := pow_nonneg hlam0 i
  rcases le_total 0 (Cj i 0) with hc | hc
  · rw [max_eq_left hc]
    calc Cj i 0 * lam ^ i * b v w ≤ Cj i 0 * 1 * b v w := by gcongr
      _ = Cj i 0 * b v w := by ring
  · rw [max_eq_right hc]
    have : Cj i 0 * lam ^ i ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hl0
    nlinarith
end

/-! The entrance traces of the amplitude recursion: the sum, over degrees, words and orders, of the
mixed cell jets of the coefficient blocks at the entrance time, whose Schur sums are bounded by the
quiet entrance traces `I_hh` (`λ ≤ 1`). -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- The trace of the block `(v, u)` of the level `(hh, n)` at the time `s`, orders `(P, F)`. -/
def traceT (Cc : ℕ → ℕ → LiftCoeff ι h) (s : ℝ) (P F hh n : ℕ) (v u : ι) : ℝ≥0∞ :=
  ∑ m ∈ Finset.range (n + 1), ∑ p ∈ Finset.range (P + 1), ∑ q ∈ Finset.range (F + 1),
    ∑ α : DerivativeWord2 m, mixedCellL2Jet {s} p q (fun t X z => Cc hh n m α t X z v u)

/-- **The Schur sums of the traces.** -/
theorem schurSums_traceT_le {π : ι → ℝ} {Cc : ℕ → ℕ → LiftCoeff ι h} {s lam : ℝ}
    {N H Kt Lt : ℕ} {I : ℕ → ℝ} (htr : HasQuietEntranceTrace π Cc s lam N H Kt Lt I)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) {P F hh n : ℕ} (hP : P ≤ Kt) (hF : F ≤ Lt) (hhH : hh ≤ H)
    (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    schurSums π (traceT Cc s P F hh n) ≤
      ((n + 1) * (P + 1) * (F + 1) : ℝ≥0∞) * ENNReal.ofReal (I hh) := by
  unfold traceT
  refine (schurSums_sum_le π _ _).trans ?_
  have hm : ∀ m ∈ Finset.range (n + 1), schurSums π (fun v u => ∑ p ∈ Finset.range (P + 1),
      ∑ q ∈ Finset.range (F + 1), ∑ α : DerivativeWord2 m,
        mixedCellL2Jet {s} p q (fun t X z => Cc hh n m α t X z v u)) ≤
      ((P + 1) * (F + 1) : ℝ≥0∞) * ENNReal.ofReal (I hh) := by
    intro m hm
    refine (schurSums_sum_le π _ _).trans ?_
    have hp : ∀ p ∈ Finset.range (P + 1), schurSums π (fun v u => ∑ q ∈ Finset.range (F + 1),
        ∑ α : DerivativeWord2 m, mixedCellL2Jet {s} p q (fun t X z => Cc hh n m α t X z v u)) ≤
        ((F + 1) : ℝ≥0∞) * ENNReal.ofReal (I hh) := by
      intro p hp
      refine (schurSums_sum_le π _ _).trans ?_
      have hq : ∀ q ∈ Finset.range (F + 1), schurSums π (fun v u => ∑ α : DerivativeWord2 m,
          mixedCellL2Jet {s} p q (fun t X z => Cc hh n m α t X z v u)) ≤ ENNReal.ofReal (I hh) := by
        intro q hq
        have h1 := htr.2 hh hhH n hn1 hnN m (by have := Finset.mem_range.1 hm; omega) p
          (by have := Finset.mem_range.1 hp; omega) q (by have := Finset.mem_range.1 hq; omega)
        refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
        have hI := htr.1 hh hhH
        have := pow_le_one₀ hlam0 hlam1 (n := p)
        nlinarith [pow_nonneg hlam0 p]
      refine (Finset.sum_le_sum hq).trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast; ring
    refine (Finset.sum_le_sum hp).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast; ring
  refine (Finset.sum_le_sum hm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast; ring
end

end AVRegularity.QuietDecay
end

section
open MeasureTheory Set
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! The Duhamel time integral of the decay recursion: with the engine weight `e^{-π²(τ-σ)}` and a
source decaying at the rate `π²/2`, `∫_s^τ e^{-π²(τ-σ)} e^{-(π²/2)(σ-s)} dσ ≤ (2/π²) e^{-(π²/2)(τ-s)}`. -/

/-- `∫_s^τ e^{k(σ-τ)} dσ ≤ 1/k`. -/
theorem lintegral_exp_growth_le {k : ℝ} (hk : 0 < k) (s τ : ℝ) (hsτ : s ≤ τ) :
    ∫⁻ σ in Icc s τ, ENNReal.ofReal (Real.exp (k * (σ - τ))) ≤ ENNReal.ofReal (1 / k) := by
  have hcont : Continuous fun σ : ℝ => Real.exp (k * (σ - τ)) := by fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc)
    (Filter.Eventually.of_forall fun σ => (Real.exp_pos _).le)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hsτ]
  have hderiv : ∀ σ ∈ uIcc s τ, HasDerivAt (fun σ => Real.exp (k * (σ - τ)) / k)
      (Real.exp (k * (σ - τ))) σ := by
    intro σ _
    have h1 : HasDerivAt (fun σ => k * (σ - τ)) k σ := by
      simpa using ((hasDerivAt_id σ).sub_const τ).const_mul k
    have h2 := (h1.exp).div_const k
    convert h2 using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  simp only [sub_self, mul_zero, Real.exp_zero]
  have : 0 < Real.exp (k * (s - τ)) / k := div_pos (Real.exp_pos _) hk
  linarith

/-- **The Duhamel integral of the decay recursion.** -/
theorem lintegral_wt_decay_le (s τ : ℝ) (hsτ : s ≤ τ) :
    ∫⁻ σ in Icc s τ, wt τ σ * ENNReal.ofReal (Real.exp (-(Real.pi ^ 2 / 2 * (σ - s)))) ≤
      ENNReal.ofReal (2 / Real.pi ^ 2 * Real.exp (-(Real.pi ^ 2 / 2 * (τ - s)))) := by
  have hk : 0 < Real.pi ^ 2 / 2 := by positivity
  have e : ∀ σ, wt τ σ * ENNReal.ofReal (Real.exp (-(Real.pi ^ 2 / 2 * (σ - s)))) =
      ENNReal.ofReal (Real.exp (-(Real.pi ^ 2 / 2 * (τ - s)))) *
        ENNReal.ofReal (Real.exp (Real.pi ^ 2 / 2 * (σ - τ))) := by
    intro σ
    rw [wt, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  simp_rw [e]
  rw [lintegral_const_mul _ (by fun_prop)]
  calc ENNReal.ofReal (Real.exp (-(Real.pi ^ 2 / 2 * (τ - s)))) *
        ∫⁻ σ in Icc s τ, ENNReal.ofReal (Real.exp (Real.pi ^ 2 / 2 * (σ - τ)))
      ≤ ENNReal.ofReal (Real.exp (-(Real.pi ^ 2 / 2 * (τ - s)))) *
          ENNReal.ofReal (1 / (Real.pi ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left (lintegral_exp_growth_le hk s τ hsτ) zero_le
    _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 1
        field_simp

/-! One level of the decay recursion: if the squared cell norm of a word at the time `τ` is bounded
by the engine form `K (e^{-π²(τ-s)} I₀ + ∫_s^τ e^{-π²(τ-σ)} I(σ) dσ)` with entrance data
`I₀ ≤ T²` and a source `I(σ) ≤ S² e^{-(π²/2)(σ-s)}`, then the norm itself is at most
`√K (T + S) e^{-(π²/4)(τ-s)}`. -/

/-- The decay factor `e^{-(π²/4)(τ-s)}` of the norms. -/
def decayF (s τ : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(Real.pi ^ 2 / 4 * (τ - s))))

theorem decayF_sq (s τ : ℝ) :
    decayF s τ ^ 2 = ENNReal.ofReal (Real.exp (-(Real.pi ^ 2 / 2 * (τ - s)))) := by
  rw [decayF, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem wt_le_decayF_sq {s τ : ℝ} (hsτ : s ≤ τ) : wt τ s ≤ decayF s τ ^ 2 := by
  rw [decayF_sq, wt]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have : 0 ≤ τ - s := by linarith
  have hp : 0 ≤ Real.pi ^ 2 := by positivity
  nlinarith

/-- **One level of the decay recursion (squared form).** -/
theorem level_sq_decay {J K I₀ T S : ℝ≥0∞} {Isrc : ℝ → ℝ≥0∞} {s τ : ℝ} (hsτ : s ≤ τ)
    (hE : J ≤ K * (wt τ s * I₀ + ∫⁻ σ in Icc s τ, wt τ σ * Isrc σ))
    (hI₀ : I₀ ≤ T ^ 2)
    (hsrc : ∀ σ ∈ Icc s τ, Isrc σ ≤ S ^ 2 * ENNReal.ofReal (Real.exp (-(Real.pi ^ 2 / 2 * (σ - s))))) :
    J ≤ K * (T + S) ^ 2 * decayF s τ ^ 2 := by
  have hint : ∫⁻ σ in Icc s τ, wt τ σ * Isrc σ ≤ S ^ 2 * decayF s τ ^ 2 := by
    calc ∫⁻ σ in Icc s τ, wt τ σ * Isrc σ
        ≤ ∫⁻ σ in Icc s τ, S ^ 2 * (wt τ σ *
            ENNReal.ofReal (Real.exp (-(Real.pi ^ 2 / 2 * (σ - s))))) := by
          refine setLIntegral_mono_ae ?_ ?_
          · exact (((wt_measurable τ).mul (by fun_prop)).const_mul _).aemeasurable
          · refine Filter.Eventually.of_forall fun σ hσ => ?_
            calc wt τ σ * Isrc σ ≤ wt τ σ * (S ^ 2 *
                  ENNReal.ofReal (Real.exp (-(Real.pi ^ 2 / 2 * (σ - s))))) :=
                  mul_le_mul_of_nonneg_left (hsrc σ hσ) zero_le
              _ = _ := by ring
      _ = S ^ 2 * ∫⁻ σ in Icc s τ, wt τ σ *
            ENNReal.ofReal (Real.exp (-(Real.pi ^ 2 / 2 * (σ - s)))) :=
          lintegral_const_mul _ ((wt_measurable τ).mul (by fun_prop))
      _ ≤ S ^ 2 * ENNReal.ofReal (2 / Real.pi ^ 2 *
            Real.exp (-(Real.pi ^ 2 / 2 * (τ - s)))) :=
          mul_le_mul_of_nonneg_left (lintegral_wt_decay_le s τ hsτ) zero_le
      _ ≤ S ^ 2 * decayF s τ ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          rw [decayF_sq]
          refine ENNReal.ofReal_le_ofReal ?_
          have h2 : 2 / Real.pi ^ 2 ≤ 1 := by
            rw [div_le_one (by positivity)]
            nlinarith [Real.pi_gt_three]
          have he := (Real.exp_pos (-(Real.pi ^ 2 / 2 * (τ - s)))).le
          nlinarith
  calc J ≤ K * (wt τ s * I₀ + ∫⁻ σ in Icc s τ, wt τ σ * Isrc σ) := hE
    _ ≤ K * (decayF s τ ^ 2 * T ^ 2 + S ^ 2 * decayF s τ ^ 2) := by
        gcongr
        exact wt_le_decayF_sq hsτ
    _ = K * (T ^ 2 + S ^ 2) * decayF s τ ^ 2 := by ring
    _ ≤ K * (T + S) ^ 2 * decayF s τ ^ 2 := by
        gcongr
        rw [add_sq]
        calc T ^ 2 + S ^ 2 = T ^ 2 + 0 + S ^ 2 := by rw [add_zero]
          _ ≤ T ^ 2 + 2 * T * S + S ^ 2 := by gcongr; exact zero_le

/-- The norm form: `(∫ ‖w‖²)^{1/2} ≤ √K (T + S) e^{-(π²/4)(τ-s)}`. -/
theorem level_decay {J K T S : ℝ≥0∞} {s τ : ℝ} (h : J ≤ K * (T + S) ^ 2 * decayF s τ ^ 2) :
    J ^ (1 / 2 : ℝ) ≤ K ^ (1 / 2 : ℝ) * (T + S) * decayF s τ := by
  have e : K * (T + S) ^ 2 * decayF s τ ^ 2 = (K ^ (1 / 2 : ℝ) * (T + S) * decayF s τ) ^ (2 : ℝ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ← ENNReal.rpow_mul]
    norm_num
  rw [e] at h
  calc J ^ (1 / 2 : ℝ) ≤ ((K ^ (1 / 2 : ℝ) * (T + S) * decayF s τ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = _ := by rw [← ENNReal.rpow_mul]; norm_num

/-! The ranks, orders and decay amplitudes of the levels of the lift recursion on a quiet interval.
The level `(hh, n)`, `1 ≤ n ≤ N`, has the rank `hh N + (n - 1)`; the quiet source of a level only
uses levels of smaller rank. The rank `r` carries the slow and fast orders
`K₀ + D((H+1)N - 1 - r)` and `J₀ + 2 + D((H+1)N - 1 - r)`, so one source step (cost `≤ D`) stays
within the orders of the lower levels. The amplitude of a level is the supremum over the interval
of `e^{(π²/4)(τ-s)}` times its block jet. -/

section
/-- The rank of the level `(hh, n)`. -/
def rankOf (N hh n : ℕ) : ℕ := hh * N + (n - 1)

/-- The order reserve of the rank `r`. -/
def resv (D H N r : ℕ) : ℕ := D * ((H + 1) * N - 1 - r)

theorem rankOf_lt_of_lower_deg {N hh n n' : ℕ} (h1 : 1 ≤ n') (h : n' < n) :
    rankOf N hh n' < rankOf N hh n := by
  unfold rankOf; omega

theorem rankOf_lt_of_lower_grade {N hh n n' : ℕ} (hn : 1 ≤ n) (hn'1 : 1 ≤ n') (hn' : n' ≤ N)
    (hh1 : 1 ≤ hh) :
    rankOf N (hh - 1) n' < rankOf N hh n := by
  unfold rankOf
  obtain ⟨k, rfl⟩ : ∃ k, hh = k + 1 := ⟨hh - 1, by omega⟩
  simp only [Nat.add_sub_cancel, add_mul, one_mul]
  omega

theorem rankOf_le {N H hh n : ℕ} (hhH : hh ≤ H) (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    rankOf N hh n ≤ (H + 1) * N - 1 := by
  unfold rankOf
  have : hh * N ≤ H * N := Nat.mul_le_mul_right _ hhH
  have : (H + 1) * N = H * N + N := by ring
  omega

/-- A lower rank has a reserve larger by at least `D`. -/
theorem resv_add_le {D H N r r' : ℕ} (hr : r' < r) (hrM : r ≤ (H + 1) * N - 1) :
    resv D H N r + D ≤ resv D H N r' := by
  unfold resv
  have h1 : (H + 1) * N - 1 - r + 1 ≤ (H + 1) * N - 1 - r' := by omega
  calc D * ((H + 1) * N - 1 - r) + D = D * ((H + 1) * N - 1 - r + 1) := by ring
    _ ≤ D * ((H + 1) * N - 1 - r') := Nat.mul_le_mul_left _ h1

theorem resv_le {D H N r : ℕ} : resv D H N r + D ≤ D * (H + 1) * N ∨ N = 0 := by
  rcases Nat.eq_zero_or_pos N with h | h
  · exact Or.inr h
  left
  unfold resv
  have h1 : (H + 1) * N - 1 - r + 1 ≤ (H + 1) * N := by
    have : 1 ≤ (H + 1) * N := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  calc D * ((H + 1) * N - 1 - r) + D = D * ((H + 1) * N - 1 - r + 1) := by ring
    _ ≤ D * ((H + 1) * N) := Nat.mul_le_mul_left _ h1
    _ = D * (H + 1) * N := by ring

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem blkJ_mono (Cc : ℕ → ℕ → LiftCoeff ι h) (p n' : ℕ) (σ : ℝ) (w u' : ι) {S S' F F' : ℕ}
    (hS : S ≤ S') (hF : F ≤ F') : blkJ Cc p n' σ w u' S F ≤ blkJ Cc p n' σ w u' S' F' := by
  unfold blkJ
  refine iSup_le fun m => iSup_le fun α => iSup_le fun l => iSup_le fun mm => iSup_le fun X =>
    iSup_le fun η => ?_
  exact vecJ_le_blkJ Cc p n' σ w u' S' F' (Nat.lt_succ_iff.1 m.2) α l.1 mm.1 (l.2.trans hS)
    (mm.2.trans hF) X η.1 η.2

/-- The growth factor `e^{(π²/4)(τ-s)}`. -/
def growF (s τ : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (Real.pi ^ 2 / 4 * (τ - s)))

theorem growF_mul_decayF (s τ : ℝ) : growF s τ * decayF s τ = 1 := by
  rw [growF, decayF, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  simp

/-- The amplitude of the level `(hh, n)` on `[s, s + T]` at the orders `(S, F)`. -/
def ampOf (Cc : ℕ → ℕ → LiftCoeff ι h) (s T : ℝ) (hh n : ℕ) (v u : ι) (S F : ℕ) : ℝ≥0∞ :=
  ⨆ τ ∈ Icc s (s + T), growF s τ * blkJ Cc hh n τ v u S F

theorem blkJ_le_ampOf (Cc : ℕ → ℕ → LiftCoeff ι h) {s T τ : ℝ} (hτ : τ ∈ Icc s (s + T))
    (hh n : ℕ) (v u : ι) (S F : ℕ) :
    blkJ Cc hh n τ v u S F ≤ ampOf Cc s T hh n v u S F * decayF s τ := by
  calc blkJ Cc hh n τ v u S F = growF s τ * blkJ Cc hh n τ v u S F * decayF s τ := by
        rw [mul_comm (growF s τ), mul_assoc, growF_mul_decayF, mul_one]
    _ ≤ ampOf Cc s T hh n v u S F * decayF s τ := by
        gcongr
        exact le_iSup₂_of_le τ hτ le_rfl

/-- An amplitude bound from bounds at every time. -/
theorem ampOf_le (Cc : ℕ → ℕ → LiftCoeff ι h) {s T : ℝ} (hh n : ℕ) (v u : ι) (S F : ℕ)
    {A : ℝ≥0∞} (hA : ∀ τ ∈ Icc s (s + T), blkJ Cc hh n τ v u S F ≤ A * decayF s τ) :
    ampOf Cc s T hh n v u S F ≤ A := by
  refine iSup₂_le fun τ hτ => ?_
  calc growF s τ * blkJ Cc hh n τ v u S F ≤ growF s τ * (A * decayF s τ) := by gcongr; exact hA τ hτ
    _ = A * (growF s τ * decayF s τ) := by ring
    _ = A := by rw [growF_mul_decayF, mul_one]
end

end AVRegularity.QuietDecay
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! Box smoothness and periodicity of the coefficient blocks, from the lift recursion. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem blockF_box {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h} {sX sZ N H : ℕ}
    {t₀ t₁ : ℝ} (hseq : IsLiftSequenceFrom Q sX sZ t₀ t₁ N H Cc) {hh n : ℕ} (hhH : hh ≤ H)
    {P F : ℕ} (hP : P ≤ sX) (hF : F ≤ sZ) {m : ℕ} (α : DerivativeWord2 m) (v u : ι) (x : h u)
    {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    IsBoxSmooth P F (blockF Cc hh n α v u x t) ∧
      ∀ X, AVenhance.IsZ2Periodic (blockF Cc hh n α v u x t X) := by
  obtain ⟨h1, h2⟩ := hseq.2.2.2.2.2.1 hh hhH n m α v u t ht
  refine ⟨(h1.clm_comp (ContinuousLinearMap.apply ℝ (h v) x)).mono hP hF, fun X nn z => ?_⟩
  simp only [blockF, h2 X nn z]
end

/-! The entrance data of the engine for one coefficient block, by the mixed cell jets of the
coefficients at the entrance time. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The squared cell integral of a word is the square of the vector jet. -/
theorem lintegral_sq_eq_vecJ_sq {F : Vec 2 → Vec 2 → E} {sX sZ : ℕ} (hF : IsBoxSmooth sX sZ F)
    (l m : List (Fin 2)) (hl : l.length ≤ sX) (hm : m.length ≤ sZ) (X : Vec 2) :
    ∫⁻ z in AVenhance.unitCube, ‖fastDerivs m (slowDerivs l F X) z‖ₑ ^ 2 = vecJ F X l m ^ 2 := by
  have hB : IsBoxSmooth (sX - l.length + l.length) sZ F := by
    rwa [Nat.sub_add_cancel hl]
  have hcd : ContDiff ℝ (sZ : ℕ∞) (slowDerivs l F X) := by
    have := (isBoxSmooth_slowIter l _ _ hB).1 X
    rwa [slowIter_eq_slowDerivs] at this
  have hc : Continuous (fastDerivs m (slowDerivs l F X)) := by
    have : ContDiff ℝ ((0 + m.length : ℕ) : ℕ∞) (slowDerivs l F X) :=
      hcd.of_le (by exact_mod_cast (by omega))
    exact (contDiff_fastDerivsE (k := 0) _ this).continuous
  unfold vecJ
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hc.aestronglyMeasurable,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- **The entrance data of one block.** For a unit input vector, the initial mixed data of the
block at the time `s` through the slow order `P` and the fast word `m'` is at most the square of the
sum of the mixed cell jets of the coefficient at `s` through `(P, |m'|)`. -/
theorem mixInit_blockF_le {Cc : ℕ → ℕ → LiftCoeff ι h} {hh n m : ℕ} (α : DerivativeWord2 m)
    (v u : ι) (x : h u) (hx : ‖x‖ ≤ 1) (s : ℝ) {sX sZ : ℕ}
    (hbox : IsBoxSmooth sX sZ (fun X z => Cc hh n m α s X z v u)) {P : ℕ} (hP : P + 1 ≤ sX)
    (m' : List (Fin 2)) (hm' : m'.length ≤ sZ) :
    mixInit (fun X z => Cc hh n m α s X z v u x) P m' ≤
      (∑ p ∈ Finset.range (P + 1),
        mixedCellL2Jet {s} p m'.length (fun t X z => Cc hh n m α t X z v u)) ^ 2 := by
  unfold mixInit
  refine iSup_le fun l => iSup_le fun X => ?_
  have hfx : IsBoxSmooth sX sZ (fun X z => Cc hh n m α s X z v u x) :=
    hbox.clm_comp (ContinuousLinearMap.apply ℝ (h v) x)
  rw [lintegral_sq_eq_vecJ_sq hfx l.1 m' (by have := l.2; omega) hm' X]
  have h1 := vecJ_apply_le_mixedCellL2Jet (f := fun t X z => Cc hh n m α t X z v u)
    (I := {s}) (τ := s) rfl hbox l.1 m' (by have := l.2; omega) hm' X x hx
  refine pow_le_pow_left₀ zero_le (h1.trans ?_) 2
  exact Finset.single_le_sum (f := fun p => mixedCellL2Jet {s} p m'.length
    (fun t X z => Cc hh n m α t X z v u)) (fun _ _ => zero_le) (Finset.mem_range.2 (by
      have := l.2; omega))
end

/-! The engine step of one level in amplitude form: on a quiet window `[s, s + T]`, if the entrance
data of the blocks of the level are at most `T₀²` and their sources at most
`S² e^{-(π²/2)(σ-s)}`, then the block jet of the level at every time `τ` of the window is at most
`√(engK Γ P) (T₀ + S) e^{-(π²/4)(τ-s)}`. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem mixInit_mono {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (φ : Vec 2 → Vec 2 → E') {n n' : ℕ} (hn : n ≤ n') (m : List (Fin 2)) :
    mixInit φ n m ≤ mixInit φ n' m := by
  unfold mixInit
  exact iSup_le fun l => iSup_le fun X => le_iSup_of_le ⟨l.1, l.2.trans hn⟩ (le_iSup_of_le X le_rfl)

/-- **The engine step of one level.** -/
theorem level_step {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h} {sX sZ N H : ℕ}
    {t₀ t₁ : ℝ} (hseq : IsLiftSequenceFrom Q sX sZ t₀ t₁ N H Cc) {hh n : ℕ} (hhH : hh ≤ H)
    (hn1 : 1 ≤ n) (hnN : n ≤ N) {s T : ℝ} (hT : 0 ≤ T) (hJ : Icc s (s + T) ⊆ Icc t₀ t₁)
    (hv0 : ∀ t ∈ Icc s (s + T), ∀ z, Q.v t z = 0) {Γ : ℝ} {P F : ℕ}
    (hG : MetricData s (s + T) (liftMetric Q) Γ P) (v u : ι)
    (hB : ∀ m, m ≤ n → ∀ (α : DerivativeWord2 m) (x : h u), ∀ t ∈ Icc s (s + T),
      IsBoxSmooth (P + 1) F (blockF Cc hh n α v u x t) ∧
        ∀ X, AVenhance.IsZ2Periodic (blockF Cc hh n α v u x t X))
    (hS : ∀ m, m ≤ n → ∀ (α : DerivativeWord2 m) (x : h u), ∀ t ∈ Icc s (s + T),
      IsBoxSmooth (P + 1) F (blockSrc Q Cc hh n α v u x t) ∧
        ∀ X, AVenhance.IsZ2Periodic (blockSrc Q Cc hh n α v u x t X))
    (hSm : ∀ m, m ≤ n → ∀ (α : DerivativeWord2 m) (x : h u) (X : Vec 2),
      AEStronglyMeasurable (fun p : ℝ × Vec 2 => blockSrc Q Cc hh n α v u x p.1 X p.2)
        (winMeasure (Icc s (s + T))))
    {T₀ S : ℝ≥0∞}
    (htr : ∀ m, m ≤ n → ∀ (α : DerivativeWord2 m) (x : h u), ‖x‖ ≤ 1 →
      ∀ m' : List (Fin 2), m'.length ≤ F → mixInit (blockF Cc hh n α v u x s) P m' ≤ T₀ ^ 2)
    (hsrc : ∀ m, m ≤ n → ∀ (α : DerivativeWord2 m) (x : h u), ‖x‖ ≤ 1 →
      ∀ m' : List (Fin 2), m'.length ≤ F → ∀ σ ∈ Icc s (s + T),
        mixInit (blockSrc Q Cc hh n α v u x σ) P m' ≤
          S ^ 2 * ENNReal.ofReal (Real.exp (-(Real.pi ^ 2 / 2 * (σ - s))))) :
    ∀ τ ∈ Icc s (s + T), blkJ Cc hh n τ v u P F ≤
      engK Γ P ^ (1 / 2 : ℝ) * (T₀ + S) * decayF s τ := by
  intro τ hτ
  have hsT : s ≤ s + T := by linarith
  have hsym : LiftSymm (Cc hh n) := fun m α σ => hseq.2.2.2.2.1 hh hhH n m α σ
  unfold blkJ
  refine iSup_le fun m => iSup_le fun α => iSup_le fun l => iSup_le fun mm => iSup_le fun X =>
    iSup_le fun η => ?_
  have hm : (m : ℕ) ≤ n := Nat.lt_succ_iff.1 m.2
  have hE := block_engine_sharp (Q := Q) (x := η.1) hseq hhH hn1 hnN hsym hm hsT hJ hv0 hG
    (hB m hm α η.1) (hS m hm α η.1) (hSm m hm α η.1) l.1 l.2 mm.1 mm.2 X hτ
  have hbox := (hB m hm α η.1 τ hτ).1
  rw [lintegral_sq_eq_vecJ_sq hbox l.1 mm.1 (by have := l.2; omega) (by have := mm.2; omega) X]
    at hE
  have hE' : vecJ (blockF Cc hh n α v u η.1 τ) X l.1 mm.1 ^ 2 ≤ engK Γ P *
      (wt τ s * mixInit (blockF Cc hh n α v u η.1 s) P mm.1 +
        ∫⁻ σ in Icc s τ, wt τ σ * mixInit (blockSrc Q Cc hh n α v u η.1 σ) P mm.1) := by
    refine hE.trans ?_
    gcongr
    · exact engK_mono Γ l.2
    · exact mixInit_mono _ l.2 _
    · exact mixInit_mono _ l.2 _
  have hsq := level_sq_decay hτ.1 hE' (htr m hm α η.1 η.2 mm.1 mm.2)
    (fun σ hσ => hsrc m hm α η.1 η.2 mm.1 mm.2 σ ⟨hσ.1, hσ.2.trans hτ.2⟩)
  have h2 := level_decay hsq
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at h2
  norm_num at h2
  exact h2
end

/-! The target sums of the decay statement by the block jets: at one time, the sum over the degrees
of the mixed Schur jets of a grade is at most `28 · 2^N (N+1)` times the sum over the degrees of the
Schur sums of any majorant of the block jets (slow order `p`, fast order `q + 2`). -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

theorem card_derivativeWord2 (m : ℕ) : Fintype.card (DerivativeWord2 m) = 2 ^ m := by
  simp [DerivativeWord2]

/-- **The target sums by the block jets.** -/
theorem target_le_blk (π : ι → ℝ) (Cc : ℕ → ℕ → LiftCoeff ι h) (hh N : ℕ) (τ : ℝ) {sX sZ p q : ℕ}
    (hp : p + 1 ≤ sX) (hq : q + 2 ≤ sZ)
    (hbox : ∀ n, 1 ≤ n → n ≤ N → ∀ m, m ≤ n → ∀ α v u,
      IsBoxSmooth sX sZ (fun X z => Cc hh n m α τ X z v u) ∧
        ∀ X, AVenhance.IsZ2Periodic (fun z => Cc hh n m α τ X z v u))
    (A : ℕ → ι → ι → ℝ≥0∞) (hA : ∀ n, 1 ≤ n → n ≤ N → ∀ v u, blkJ Cc hh n τ v u p (q + 2) ≤ A n v u) :
    ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.range (n + 1), schurMixedCellL2Jet π {τ} p q (Cc hh n m) ≤
      28 * 2 ^ N * (N + 1) * ∑ n ∈ Finset.range (N + 1), schurSums π (A n) := by
  have hone : ∀ n, 1 ≤ n → n ≤ N → ∀ m, m ≤ n →
      schurMixedCellL2Jet π {τ} p q (Cc hh n m) ≤ 2 ^ N * 28 * schurSums π (A n) := by
    intro n hn1 hnN m hm
    unfold schurMixedCellL2Jet
    refine le_trans (schurSums_mono' π (N := fun v u => ∑ α : DerivativeWord2 m,
        mixedCellL2Jet {τ} p q (fun t X z => Cc hh n m α t X z v u))
      (M := fun v u => 2 ^ N * 28 * A n v u) fun v u => ?_) (schurSums_const_mul π _ _)
    have hα : ∀ α : DerivativeWord2 m,
        mixedCellL2Jet {τ} p q (fun t X z => Cc hh n m α t X z v u) ≤ 28 * A n v u := by
      intro α
      obtain ⟨hb, hper⟩ := hbox n hn1 hnN m hm α v u
      refine (mixedCellL2Jet_singleton_le (f := fun t X z => Cc hh n m α t X z v u) hb hper hp hq
        (B := A n v u) fun X l mm hl hmm η hη => ?_)
      exact (vecJ_le_blkJ Cc hh n τ v u p (q + 2) hm α l mm hl.le hmm X η hη).trans
        (hA n hn1 hnN v u)
    calc ∑ α : DerivativeWord2 m, mixedCellL2Jet {τ} p q (fun t X z => Cc hh n m α t X z v u)
        ≤ ∑ _α : DerivativeWord2 m, 28 * A n v u := Finset.sum_le_sum fun α _ => hα α
      _ = 2 ^ m * (28 * A n v u) := by
          rw [Finset.sum_const, Finset.card_univ, AVRegularity.QuietDecay.card_derivativeWord2, nsmul_eq_mul]
          push_cast; ring
      _ ≤ 2 ^ N * (28 * A n v u) := by
          gcongr
          · norm_num
          · omega
      _ = 2 ^ N * 28 * A n v u := by ring
  calc ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.range (n + 1), schurMixedCellL2Jet π {τ} p q (Cc hh n m)
      ≤ ∑ n ∈ Finset.Icc 1 N, ∑ _m ∈ Finset.range (N + 1), 2 ^ N * 28 * schurSums π (A n) := by
        refine Finset.sum_le_sum fun n hn => ?_
        obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.1 hn
        calc ∑ m ∈ Finset.range (n + 1), schurMixedCellL2Jet π {τ} p q (Cc hh n m)
            ≤ ∑ _m ∈ Finset.range (n + 1), 2 ^ N * 28 * schurSums π (A n) :=
              Finset.sum_le_sum fun m hm => hone n hn1 hnN m (by
                have := Finset.mem_range.1 hm; omega)
          _ ≤ ∑ _m ∈ Finset.range (N + 1), 2 ^ N * 28 * schurSums π (A n) :=
              Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))
    _ = (N + 1) * (2 ^ N * 28) * ∑ n ∈ Finset.Icc 1 N, schurSums π (A n) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.mul_sum]
        push_cast
        refine Finset.sum_congr rfl fun n _ => by ring
    _ ≤ (N + 1) * (2 ^ N * 28) * ∑ n ∈ Finset.range (N + 1), schurSums π (A n) := by
        gcongr
        intro n hn
        have := Finset.mem_Icc.1 hn
        exact Finset.mem_range.2 (by omega)
    _ = 28 * 2 ^ N * (N + 1) * ∑ n ∈ Finset.range (N + 1), schurSums π (A n) := by ring
end

/-! The amplitude of one level: from vector-jet bounds of the block sources decaying like
`Sg e^{-(π²/4)(σ-s)}` and entrance data `≤ T₀²`, the amplitude of the level is at most
`√(engK Γ P) (T₀ + Sg)`. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

/-- **The amplitude of one level.** -/
theorem ampOf_level_le {Q : LiftOperatorData ι h D} {Cc : ℕ → ℕ → LiftCoeff ι h} {sX sZ N H : ℕ}
    {t₀ t₁ : ℝ} (hseq : IsLiftSequenceFrom Q sX sZ t₀ t₁ N H Cc) {hh n : ℕ} (hhH : hh ≤ H)
    (hn1 : 1 ≤ n) (hnN : n ≤ N) {s T : ℝ} (hT : 0 ≤ T) (hJ : Icc s (s + T) ⊆ Icc t₀ t₁)
    (hv0 : ∀ t ∈ Icc s (s + T), ∀ z, Q.v t z = 0) {Γ : ℝ} {P F : ℕ}
    (hG : MetricData s (s + T) (liftMetric Q) Γ P) (v u : ι)
    (hB : ∀ m, m ≤ n → ∀ (α : DerivativeWord2 m) (x : h u), ∀ t ∈ Icc s (s + T),
      IsBoxSmooth (P + 1) F (blockF Cc hh n α v u x t) ∧
        ∀ X, AVenhance.IsZ2Periodic (blockF Cc hh n α v u x t X))
    (hS : ∀ m, m ≤ n → ∀ (α : DerivativeWord2 m) (x : h u), ∀ t ∈ Icc s (s + T),
      IsBoxSmooth (P + 1) F (blockSrc Q Cc hh n α v u x t) ∧
        ∀ X, AVenhance.IsZ2Periodic (blockSrc Q Cc hh n α v u x t X))
    (hSm : ∀ m, m ≤ n → ∀ (α : DerivativeWord2 m) (x : h u) (X : Vec 2),
      AEStronglyMeasurable (fun p : ℝ × Vec 2 => blockSrc Q Cc hh n α v u x p.1 X p.2)
        (winMeasure (Icc s (s + T))))
    {T₀ Sg : ℝ≥0∞}
    (htr : ∀ m, m ≤ n → ∀ (α : DerivativeWord2 m) (x : h u), ‖x‖ ≤ 1 →
      ∀ m' : List (Fin 2), m'.length ≤ F → mixInit (blockF Cc hh n α v u x s) P m' ≤ T₀ ^ 2)
    (hsrc : ∀ σ ∈ Icc s (s + T), ∀ m, m ≤ n → ∀ (α : DerivativeWord2 m) (x : h u), ‖x‖ ≤ 1 →
      ∀ (X : Vec 2) (l m' : List (Fin 2)), l.length ≤ P → m'.length ≤ F →
        vecJ (blockSrc Q Cc hh n α v u x σ) X l m' ≤ Sg * decayF s σ) :
    ampOf Cc s T hh n v u P F ≤ engK Γ P ^ (1 / 2 : ℝ) * (T₀ + Sg) := by
  refine ampOf_le Cc hh n v u P F fun τ hτ => ?_
  refine level_step hseq hhH hn1 hnN hT hJ hv0 hG v u hB hS hSm htr ?_ τ hτ
  intro m hm α x hx m' hm' σ hσ
  unfold mixInit
  refine iSup_le fun l => iSup_le fun X => ?_
  have hbox := (hS m hm α x σ hσ).1
  rw [lintegral_sq_eq_vecJ_sq hbox l.1 m' (by have := l.2; omega) hm' X, ← decayF_sq]
  calc vecJ (blockSrc Q Cc hh n α v u x σ) X l.1 m' ^ 2 ≤ (Sg * decayF s σ) ^ 2 :=
        pow_le_pow_left₀ zero_le (hsrc σ hσ m hm α x hx X l.1 m' l.2 hm') 2
    _ = Sg ^ 2 * decayF s σ ^ 2 := mul_pow _ _ _
end

end AVRegularity.QuietDecay
end
