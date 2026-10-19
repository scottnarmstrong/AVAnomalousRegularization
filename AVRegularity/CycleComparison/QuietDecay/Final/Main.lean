-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.QuietDecay.Assembly.LevelAmp
import AVRegularity.CycleComparison.QuietDecay.SrcReg.Main
import AVRegularity.CycleComparison.QuietDecay.Combine.Main
import AVRegularity.CycleComparison.QuietDecay.Partition.Main
public import AVRegularity.CycleComparison.QuietDecay.Combine.Unif
public import AVRegularity.CycleComparison.QuietDecay.Statement
import Mathlib.Data.Int.Star

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! The real form of the closed amplitude bound: the `ℝ≥0∞` expression of `decay_close_ennreal`
is at most `ofReal (finalC · Σ_b Θ^{hh-b} I_b · e^{-(π²/4)(τ-s)})`, with a constant `finalC`
depending only on the orders, the level constant and the envelope constant. -/

/-- The final constant. -/
def finalC (N H cT : ℕ) (K cE : ℝ) : ℝ :=
  28 * 2 ^ N * (N + 1) * ((1 + K) ^ (N + 1) * (2 * (1 + K) ^ (N + 1)) ^ H) * max 1 cE ^ H * cT

theorem finalC_nonneg (N H cT : ℕ) {K : ℝ} (hK : 0 ≤ K) (cE : ℝ) : 0 ≤ finalC N H cT K cE := by
  unfold finalC
  have : 0 ≤ max 1 cE := le_trans zero_le_one (le_max_left _ _)
  positivity

/-- **The real form.** -/
theorem close_real {N H cT hh : ℕ} (hhH : hh ≤ H) {K cE Θ : ℝ} (hK : 0 ≤ K) (hcE : 0 ≤ cE)
    (hΘ : 0 ≤ Θ) {I : ℕ → ℝ} (hI : ∀ b, b ≤ hh → 0 ≤ I b) (s τ : ℝ) :
    28 * 2 ^ N * (N + 1) * decayF s τ *
        ((1 + ENNReal.ofReal K) ^ (N + 1) * (2 * (1 + ENNReal.ofReal K) ^ (N + 1)) ^ hh *
          ∑ b' ∈ Finset.range (hh + 1), ENNReal.ofReal (cE * Θ) ^ (hh - b') *
            (((cT : ℕ) : ℝ≥0∞) * ENNReal.ofReal (I b'))) ≤
      ENNReal.ofReal (finalC N H cT K cE * (∑ b ∈ Finset.range (hh + 1), Θ ^ (hh - b) * I b) *
        Real.exp (-(Real.pi ^ 2 / 4 * (τ - s)))) := by
  set d := Real.exp (-(Real.pi ^ 2 / 4 * (τ - s)))
  have hd : 0 ≤ d := (Real.exp_pos _).le
  have hM1 : 1 ≤ max 1 cE := le_max_left _ _
  -- the sum
  have hsum : ∑ b' ∈ Finset.range (hh + 1), ENNReal.ofReal (cE * Θ) ^ (hh - b') *
      (((cT : ℕ) : ℝ≥0∞) * ENNReal.ofReal (I b')) =
      ENNReal.ofReal (∑ b' ∈ Finset.range (hh + 1), (cE * Θ) ^ (hh - b') * (cT * I b')) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun b' hb' => by
      have := hI b' (by have := Finset.mem_range.1 hb'; omega)
      positivity]
    refine Finset.sum_congr rfl fun b' hb' => ?_
    have := hI b' (by have := Finset.mem_range.1 hb'; omega)
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  have h1K : (1 + ENNReal.ofReal K) = ENNReal.ofReal (1 + K) := by
    rw [ENNReal.ofReal_add zero_le_one hK, ENNReal.ofReal_one]
  have hc : (28 * 2 ^ N * (N + 1) : ℝ≥0∞) = ENNReal.ofReal (28 * 2 ^ N * (N + 1)) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_add (by positivity) zero_le_one]
    norm_num
  have h2 : (2 * ENNReal.ofReal (1 + K) ^ (N + 1)) = ENNReal.ofReal (2 * (1 + K) ^ (N + 1)) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (by positivity)]; norm_num
  rw [hsum, h1K, hc, h2, decayF, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- the real inequality
  have hS : ∑ b' ∈ Finset.range (hh + 1), (cE * Θ) ^ (hh - b') * (cT * I b') ≤
      max 1 cE ^ H * cT * ∑ b ∈ Finset.range (hh + 1), Θ ^ (hh - b) * I b := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b' hb' => ?_
    have hIb := hI b' (by have := Finset.mem_range.1 hb'; omega)
    have hk : cE ^ (hh - b') ≤ max 1 cE ^ H :=
      (pow_le_pow_left₀ hcE (le_max_right _ _) _).trans (pow_le_pow_right₀ hM1 (by omega))
    rw [mul_pow]
    have : 0 ≤ Θ ^ (hh - b') * (cT * I b') := by positivity
    calc cE ^ (hh - b') * Θ ^ (hh - b') * (cT * I b') = cE ^ (hh - b') * (Θ ^ (hh - b') * (cT * I b')) := by ring
      _ ≤ max 1 cE ^ H * (Θ ^ (hh - b') * (cT * I b')) := mul_le_mul_of_nonneg_right hk this
      _ = _ := by ring
  have hP : (2 * (1 + K) ^ (N + 1)) ^ hh ≤ (2 * (1 + K) ^ (N + 1)) ^ H :=
    pow_le_pow_right₀ (by
      have : (1 : ℝ) ≤ (1 + K) ^ (N + 1) := one_le_pow₀ (by linarith)
      linarith) hhH
  have hA0 : 0 ≤ ∑ b ∈ Finset.range (hh + 1), Θ ^ (hh - b) * I b :=
    Finset.sum_nonneg fun b hb => mul_nonneg (pow_nonneg hΘ _) (hI b (by
      have := Finset.mem_range.1 hb; omega))
  unfold finalC
  have hc0 : (0 : ℝ) ≤ 28 * 2 ^ N * (N + 1) := by positivity
  have hp0 : (0 : ℝ) ≤ (1 + K) ^ (N + 1) := by positivity
  calc 28 * 2 ^ N * (N + 1) * d * ((1 + K) ^ (N + 1) * (2 * (1 + K) ^ (N + 1)) ^ hh *
        ∑ b' ∈ Finset.range (hh + 1), (cE * Θ) ^ (hh - b') * (cT * I b'))
      ≤ 28 * 2 ^ N * (N + 1) * d * ((1 + K) ^ (N + 1) * (2 * (1 + K) ^ (N + 1)) ^ H *
        (max 1 cE ^ H * cT * ∑ b ∈ Finset.range (hh + 1), Θ ^ (hh - b) * I b)) := by
        have hs0 : 0 ≤ ∑ b' ∈ Finset.range (hh + 1), (cE * Θ) ^ (hh - b') * (cT * I b') :=
          Finset.sum_nonneg fun b' hb' => by
            have := hI b' (by have := Finset.mem_range.1 hb'; omega)
            positivity
        refine mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left hP hp0) hS hs0
          (by positivity)) (by positivity)
    _ = _ := by ring

end AVRegularity.QuietDecay
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! The orders and amplitudes of the levels in the final assembly, with reserve
`R = D(H+1)N` and target fast order `J₀ = max k₀ (L₀+2)`: the level `(hh, n)` of rank `r` carries
the slow order `K₀ + resv r` and the fast order `J₀ + 2 + resv r`. -/

/-- The slow order of the level `(hh, n)`. -/
def ordS (K₀ D H N hh n : ℕ) : ℕ := K₀ + resv D H N (rankOf N hh n)

/-- The fast order of the level `(hh, n)`. -/
def ordF (J₀ D H N hh n : ℕ) : ℕ := J₀ + 2 + resv D H N (rankOf N hh n)

theorem resv_le_R {D H N r : ℕ} (hN : 1 ≤ N) : resv D H N r + D ≤ D * (H + 1) * N := by
  rcases (resv_le (D := D) (H := H) (N := N) (r := r)) with h | h
  · exact h
  · omega

theorem ordS_le {K₀ D H N hh n : ℕ} (hN : 1 ≤ N) :
    ordS K₀ D H N hh n + D ≤ K₀ + D * (H + 1) * N := by
  unfold ordS; have := resv_le_R (D := D) (H := H) (r := rankOf N hh n) hN; omega

theorem ordF_le {J₀ D H N hh n : ℕ} (hN : 1 ≤ N) :
    ordF J₀ D H N hh n + D ≤ J₀ + 2 + D * (H + 1) * N := by
  unfold ordF; have := resv_le_R (D := D) (H := H) (r := rankOf N hh n) hN; omega

/-- Lower levels of the same grade carry at least `D` more orders. -/
theorem ord_lower_deg {K₀ J₀ D H N hh n n' : ℕ} (hhH : hh ≤ H) (hn' : 1 ≤ n') (hlt : n' < n)
    (hnN : n ≤ N) :
    ordS K₀ D H N hh n + D ≤ ordS K₀ D H N hh n' ∧ ordF J₀ D H N hh n + D ≤ ordF J₀ D H N hh n' := by
  have h1 := resv_add_le (D := D) (rankOf_lt_of_lower_deg (N := N) (hh := hh) hn' hlt)
    (rankOf_le hhH (by omega) hnN)
  unfold ordS ordF; omega

/-- Levels of the previous grade carry at least `D` more orders. -/
theorem ord_lower_grade {K₀ J₀ D H N hh n n' : ℕ} (hhH : hh ≤ H) (hh1 : 1 ≤ hh) (hn1 : 1 ≤ n)
    (hnN : n ≤ N) (hn'1 : 1 ≤ n') (hn' : n' ≤ N) :
    ordS K₀ D H N hh n + D ≤ ordS K₀ D H N (hh - 1) n' ∧
      ordF J₀ D H N hh n + D ≤ ordF J₀ D H N (hh - 1) n' := by
  have h1 := resv_add_le (D := D) (rankOf_lt_of_lower_grade (N := N) hn1 hn'1 hn' hh1)
    (rankOf_le hhH hn1 hnN)
  unfold ordS ordF; omega

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

/-- The amplitudes of the levels (zero outside `1 ≤ n ≤ N`). -/
def ampQ (Cc : ℕ → ℕ → LiftCoeff ι h) (s T : ℝ) (K₀ J₀ D H N hh n : ℕ) (v u : ι) : ℝ≥0∞ :=
  if 1 ≤ n ∧ n ≤ N then
    ampOf Cc s T hh n v u (ordS K₀ D H N hh n) (ordF J₀ D H N hh n)
  else 0

theorem blkJ_le_ampQ (Cc : ℕ → ℕ → LiftCoeff ι h) {s T σ : ℝ} (hσ : σ ∈ Icc s (s + T))
    {K₀ J₀ D H N hh n : ℕ} (hn1 : 1 ≤ n) (hnN : n ≤ N) (v u : ι) {S F : ℕ}
    (hS : S ≤ ordS K₀ D H N hh n) (hF : F ≤ ordF J₀ D H N hh n) :
    blkJ Cc hh n σ v u S F ≤ ampQ Cc s T K₀ J₀ D H N hh n v u * decayF s σ := by
  unfold ampQ
  simp only [hn1, hnN, and_self, ↓reduceIte]
  exact (blkJ_mono Cc hh n σ v u hS hF).trans (blkJ_le_ampOf Cc hσ hh n v u _ _)

end AVRegularity.QuietDecay
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! Small facts for the final assembly: monotonicity of the metric data in the bound, of
`metricΓ`, finiteness of the engine constant, and the entrance data of a block below the trace. -/

section
theorem MetricData.mono_Γ {a b : ℝ} {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {Γ Γ' : ℝ} {P : ℕ}
    (hG : MetricData a b G Γ P) (hΓ : Γ ≤ Γ') : MetricData a b G Γ' P :=
  ⟨hG.Gm, hG.Gs, hG.Ge, hG.Γ0.trans hΓ, hG.Gsmooth,
    fun t ht w hw Y j k => (hG.Gder t ht w hw Y j k).trans hΓ⟩

theorem metricΓ_mono (CG : ℕ → ℝ) {P P' : ℕ} (h : P ≤ P') : metricΓ CG P ≤ metricΓ CG P' :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
    fun _ _ _ => le_max_right _ _

theorem engK_ne_top (Γ : ℝ) : ∀ n, engK Γ n ≠ ⊤
  | 0 => by simp [engK]
  | n + 1 => by
      simp only [engK]
      exact ENNReal.add_ne_top.2 ⟨engK_ne_top Γ n, ENNReal.mul_ne_top (by norm_num)
        (ENNReal.add_ne_top.2 ⟨by norm_num, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (engK_ne_top Γ n)⟩)⟩

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

omit [Fintype ι] in
theorem sum_p_le_traceT (Cc : ℕ → ℕ → LiftCoeff ι h) (s : ℝ) {P P' F hh n m q : ℕ} (hm : m ≤ n)
    (hP : P ≤ P') (hq : q ≤ F) (α : DerivativeWord2 m) (v u : ι) :
    ∑ p ∈ Finset.range (P + 1), mixedCellL2Jet {s} p q (fun t X z => Cc hh n m α t X z v u) ≤
      traceT Cc s P' F hh n v u := by
  unfold traceT
  refine le_trans ?_ (Finset.single_le_sum (f := fun m => ∑ p ∈ Finset.range (P' + 1),
    ∑ q ∈ Finset.range (F + 1), ∑ α : DerivativeWord2 m,
      mixedCellL2Jet {s} p q (fun t X z => Cc hh n m α t X z v u)) (fun _ _ => zero_le)
    (Finset.mem_range.2 (by omega : m < n + 1)))
  refine le_trans (Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega :
    P + 1 ≤ P' + 1))) (Finset.sum_le_sum fun p _ => ?_)
  refine le_trans ?_ (Finset.single_le_sum (f := fun q =>
    ∑ α : DerivativeWord2 m, mixedCellL2Jet {s} p q (fun t X z => Cc hh n m α t X z v u))
    (fun _ _ => zero_le) (Finset.mem_range.2 (by omega : q < F + 1)))
  exact Finset.single_le_sum (f := fun α =>
    mixedCellL2Jet {s} p q (fun t X z => Cc hh n m α t X z v u)) (fun _ _ => zero_le)
    (Finset.mem_univ α)
end

/-! Closing the amplitude recursion: from the recursion of the level amplitudes (`ampQ_rec`), the
entrance traces and the edge envelope, the Schur recursion (`schur_amplitude_le`) bounds the grade
sums, and the target sums at the time `τ` follow (`target_le_blk`), in `ℝ≥0∞`. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- The traces of the levels (zero outside `1 ≤ n ≤ N`). -/
def traceQ (Cc : ℕ → ℕ → LiftCoeff ι h) (s : ℝ) (P F N hh n : ℕ) (v u : ι) : ℝ≥0∞ :=
  if 1 ≤ n ∧ n ≤ N then traceT Cc s P F hh n v u else 0

/-- **The closed amplitude bound, in `ℝ≥0∞`.** -/
theorem decay_close_ennreal {π : ι → ℝ} (hπ : ∀ v, 0 < π v) {Cc : ℕ → ℕ → LiftCoeff ι h}
    {s T lam : ℝ} {N H K₀ J₀ D Pt Ft : ℕ} {I : ℕ → ℝ}
    (htr : HasQuietEntranceTrace π Cc s lam N H Pt Ft I) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    {Pt' Ft' : ℕ} (hPt : Pt' ≤ Pt) (hFt : Ft' ≤ Ft)
    {b : ι → ι → ℝ≥0∞} {Θ : ℝ≥0∞} (hrow : ∀ v, ∑ u, b v u ≤ Θ) (hcol : ∀ u, ∑ v, b v u ≤ Θ)
    (EB : ι → ι → ℝ≥0∞) (henv : ∀ v w, massW π v w * EB v w ≤ b v w) {Kc : ℝ≥0∞}
    (hrec : ∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ N → ∀ v u,
      ampQ Cc s T K₀ J₀ D H N hh n v u ≤ Kc *
        (traceT Cc s Pt' Ft' hh n v u
          + ∑ n' ∈ Finset.range n, ampQ Cc s T K₀ J₀ D H N hh n' v u
          + (if hh = 0 then 0 else ∑ n' ∈ Finset.range (N + 1),
              (∑ w, EB v w * ampQ Cc s T K₀ J₀ D H N (hh - 1) n' w u
                + ∑ w, ampQ Cc s T K₀ J₀ D H N (hh - 1) n' v w * EB w u))))
    {sX sZ : ℕ} {τ : ℝ} (hτ : τ ∈ Icc s (s + T)) {hh : ℕ} (hhH : hh ≤ H)
    (hbox : ∀ n, 1 ≤ n → n ≤ N → ∀ m, m ≤ n → ∀ α v u,
      IsBoxSmooth sX sZ (fun X z => Cc hh n m α τ X z v u) ∧
        ∀ X, AVenhance.IsZ2Periodic (fun z => Cc hh n m α τ X z v u))
    {p q : ℕ} (hp : p ≤ K₀) (hq : q ≤ J₀) (hpX : p + 1 ≤ sX) (hqZ : q + 2 ≤ sZ) :
    ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.range (n + 1), schurMixedCellL2Jet π {τ} p q (Cc hh n m) ≤
      28 * 2 ^ N * (N + 1) * decayF s τ *
        ((1 + Kc) ^ (N + 1) * (2 * (1 + Kc) ^ (N + 1)) ^ hh *
          ∑ b' ∈ Finset.range (hh + 1), Θ ^ (hh - b') *
            ((((N + 1) * (Pt' + 1) * (Ft' + 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (I b'))) := by
  set A := ampQ Cc s T K₀ J₀ D H N with hA
  have R : AmpRec π N H Kc Θ
      (fun b' => (((N + 1) * (Pt' + 1) * (Ft' + 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (I b')) A
      (traceQ Cc s Pt' Ft' N) EB EB b := by
    refine ⟨hπ, fun hh' hh'H n => ?_, henv, henv, hrow, hcol, fun hh' hh'H n hn v u => ?_⟩
    · unfold traceQ
      by_cases hn : 1 ≤ n ∧ n ≤ N
      · simp only [hn, and_self, ↓reduceIte]
        refine (schurSums_traceT_le htr hlam0 hlam1 hPt hFt hh'H hn.1 hn.2).trans ?_
        gcongr
        push_cast
        gcongr
        exact_mod_cast hn.2
      · simp only [hn, ↓reduceIte]
        exact (schurSums_le_of π _ 0 (fun v => by simp) (fun u => by simp)).trans zero_le
    · by_cases hn1 : 1 ≤ n
      · have := hrec hh' hh'H n hn1 hn v u
        simp only [traceQ, hn1, hn, and_self, ↓reduceIte]
        exact this
      · have h0 : A hh' n v u = 0 := by
          simp only [hA, ampQ, hn1, false_and, ↓reduceIte]
        rw [h0]; exact zero_le
  have hgrade := schur_amplitude_le R hh hhH
  have htar := target_le_blk π Cc hh N τ hpX hqZ (fun n hn1 hnN m hm α v u => hbox n hn1 hnN m hm α v u)
    (fun n v u => A hh n v u * decayF s τ)
    (fun n hn1 hnN v u => blkJ_le_ampQ Cc hτ hn1 hnN v u (by unfold ordS; omega)
      (by unfold ordF; omega))
  refine htar.trans ?_
  have hs : ∑ n ∈ Finset.range (N + 1), schurSums π (fun v u => A hh n v u * decayF s τ) ≤
      decayF s τ * gradeSum π A hh N := by
    unfold gradeSum
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    have := schurSums_const_mul π (decayF s τ) (A hh n)
    simp only [mul_comm (decayF s τ)] at this ⊢
    exact this
  calc 28 * 2 ^ N * (N + 1) * ∑ n ∈ Finset.range (N + 1),
        schurSums π (fun v u => A hh n v u * decayF s τ)
      ≤ 28 * 2 ^ N * (N + 1) * (decayF s τ * gradeSum π A hh N) := by gcongr
    _ ≤ 28 * 2 ^ N * (N + 1) * (decayF s τ * ((1 + Kc) ^ (N + 1) * (2 * (1 + Kc) ^ (N + 1)) ^ hh *
          ∑ b' ∈ Finset.range (hh + 1), Θ ^ (hh - b') *
            ((((N + 1) * (Pt' + 1) * (Ft' + 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (I b')))) := by
        gcongr
    _ = _ := by ring
end

/-! The recursion of the level amplitudes on a quiet interval, given the block source bound
(`hsrcB`, by the lower block jets and the edge envelope), the vanishing source of the first level
`(0, 1)` and the regularity of the block sources. The amplitude of every level is at most
`K (T + Σ_{lower degrees} A + [hh ≥ 1] Σ_{previous grade} (B A + A B))`, the shape of `AmpRec`. -/

section
theorem slowDerivs_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∀ l : List (Fin 2), slowDerivs l (fun _ _ => (0 : E)) = fun _ _ => 0 := by
  intro l
  induction l with
  | nil => rfl
  | cons i l ih =>
      rw [slowDerivs_cons]
      have : AVRegularity.slowPartial i (fun _ _ => (0 : E)) = fun _ _ => 0 := by
        funext X z; simp [AVRegularity.slowPartial]
      rw [this, ih]

theorem fastDerivs_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∀ m : List (Fin 2), fastDerivs m (fun _ => (0 : E)) = fun _ => 0 := by
  intro m
  induction m with
  | nil => rfl
  | cons i m ih =>
      rw [fastDerivs_cons]
      have : (fun z => fderiv ℝ (fun _ : Vec 2 => (0 : E)) z (basisVec i)) = fun _ => 0 := by
        funext z; simp
      rw [this, ih]

theorem vecJ_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (X : Vec 2)
    (l m : List (Fin 2)) : vecJ (fun _ _ => (0 : E)) X l m = 0 := by
  unfold vecJ
  rw [slowDerivs_zero]
  simp only
  rw [fastDerivs_zero]
  simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

/-- The level constant. -/
def levelK (CG : ℕ → ℝ) (P : ℕ) (Csrc : ℝ) : ℝ≥0∞ :=
  engK (metricΓ CG P) P ^ (1 / 2 : ℝ) * (1 + ENNReal.ofReal Csrc)

/-- **The recursion of the level amplitudes.** -/
theorem ampQ_rec {N H K₀ k₀ L₀ : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}
    {Q : LiftOperatorData ι h D} {π : ι → ℝ} {t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2}
    {V : ℝ → ℝ → ℝ} {qs qf : ℕ} {b : ι → ι → ℝ} {Θ : ℝ}
    (hset : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V
      H N (K₀ + D * (H + 1) * N) (k₀ + D * (H + 1) * N) (L₀ + D * (H + 1) * N)
      qs qf CG Cw Cj b Θ)
    {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequenceFrom Q (K₀ + D * (H + 1) * N + D + 2)
      (max (k₀ + D * (H + 1) * N + 1) (L₀ + D * (H + 1) * N + 2)) t₀ t₁ N H Cc)
    {s T : ℝ} (hT : 0 ≤ T) (hs : t₀ ≤ s) (hsT : s + T ≤ t₁)
    (hv0 : ∀ t ∈ Icc s (s + T), ∀ z, Q.v t z = 0)
    {Csrc : ℝ} (EB : ι → ι → ℝ≥0∞)
    (hsrcB : ∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ N → ¬(hh = 0 ∧ n = 1) →
      ∀ σ ∈ Icc s (s + T), ∀ m, m ≤ n → ∀ (α : DerivativeWord2 m) (v u : ι) (x : h u), ‖x‖ ≤ 1 →
      ∀ (X : Vec 2) (l m' : List (Fin 2)), l.length ≤ ordS K₀ D H N hh n →
        m'.length ≤ ordF (max k₀ (L₀ + 2)) D H N hh n →
        vecJ (blockSrc Q Cc hh n α v u x σ) X l m' ≤ ENNReal.ofReal Csrc *
          (∑ n' ∈ Finset.Ico 1 n, blkJ Cc hh n' σ v u (ordS K₀ D H N hh n + D)
              (ordF (max k₀ (L₀ + 2)) D H N hh n + D)
            + (if hh = 0 then 0 else ∑ n' ∈ Finset.Icc 1 N,
              (∑ w, EB v w * blkJ Cc (hh - 1) n' σ w u (ordS K₀ D H N hh n + D)
                  (ordF (max k₀ (L₀ + 2)) D H N hh n + D)
                + ∑ w, blkJ Cc (hh - 1) n' σ v w (ordS K₀ D H N hh n + D)
                  (ordF (max k₀ (L₀ + 2)) D H N hh n + D) * EB w u))))
    (hzero : ∀ σ ∈ Icc s (s + T), ∀ m (α : DerivativeWord2 m) (v u : ι) (x : h u),
      blockSrc Q Cc 0 1 α v u x σ = fun _ _ => 0)
    (hreg : ∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ N → ∀ m, m ≤ n → ∀ (α : DerivativeWord2 m)
      (v u : ι) (x : h u),
      (∀ t ∈ Icc s (s + T), IsBoxSmooth (ordS K₀ D H N hh n + 1)
        (ordF (max k₀ (L₀ + 2)) D H N hh n) (blockSrc Q Cc hh n α v u x t) ∧
        ∀ X, AVenhance.IsZ2Periodic (blockSrc Q Cc hh n α v u x t X)) ∧
      ∀ X, AEStronglyMeasurable (fun p : ℝ × Vec 2 => blockSrc Q Cc hh n α v u x p.1 X p.2)
        (winMeasure (Icc s (s + T))))
    {hh n : ℕ} (hhH : hh ≤ H) (hn1 : 1 ≤ n) (hnN : n ≤ N) (v u : ι) :
    ampQ Cc s T K₀ (max k₀ (L₀ + 2)) D H N hh n v u ≤
      levelK CG (K₀ + D * (H + 1) * N) Csrc *
        (traceT Cc s (K₀ + D * (H + 1) * N) (max k₀ (L₀ + 2) + D * (H + 1) * N) hh n v u
          + ∑ n' ∈ Finset.range n, ampQ Cc s T K₀ (max k₀ (L₀ + 2)) D H N hh n' v u
          + (if hh = 0 then 0 else ∑ n' ∈ Finset.range (N + 1),
              (∑ w, EB v w * ampQ Cc s T K₀ (max k₀ (L₀ + 2)) D H N (hh - 1) n' w u
                + ∑ w, ampQ Cc s T K₀ (max k₀ (L₀ + 2)) D H N (hh - 1) n' v w * EB w u))) := by
  set R := D * (H + 1) * N with hR
  set J₀ := max k₀ (L₀ + 2) with hJ₀
  set P := ordS K₀ D H N hh n with hP
  set F := ordF J₀ D H N hh n with hF
  set A := ampQ Cc s T K₀ J₀ D H N with hA
  have hN1 : 1 ≤ N := hset.N_ge
  have hD2 : 2 ≤ D := hset.D_ge
  have hPle : P + D ≤ K₀ + R := ordS_le hN1
  have hFle : F + D ≤ J₀ + 2 + R := ordF_le hN1
  have hJw : Icc s (s + T) ⊆ Icc t₀ t₁ := fun t ht => ⟨hs.trans ht.1, ht.2.trans hsT⟩
  have hsJ : s ∈ Icc t₀ t₁ := hJw ⟨le_rfl, by linarith⟩
  have hqs : qs = K₀ + R + 4 * (H + 1) * (N + D) ^ 2 := hset.qs_eq
  have hFsZ : F ≤ max (k₀ + R + 1) (L₀ + R + 2) := by
    have : J₀ + R ≤ max (k₀ + R + 1) (L₀ + R + 2) := by
      rw [hJ₀]; rcases le_total k₀ (L₀ + 2) with hk | hk
      · rw [max_eq_right hk]; exact le_max_of_le_right (by omega)
      · rw [max_eq_left hk]; exact le_max_of_le_left (by omega)
    omega
  -- the metric data
  have hG : MetricData s (s + T) (liftMetric Q) (metricΓ CG (K₀ + R)) P :=
    (metricData_of_setting hset hJw (P := P) (by rw [hqs]; omega)).mono_Γ
      (metricΓ_mono CG (by omega))
  -- the lower sum
  set Lsum : ℝ≥0∞ := ∑ n' ∈ Finset.range n, A hh n' v u
      + (if hh = 0 then 0 else ∑ n' ∈ Finset.range (N + 1),
          (∑ w, EB v w * A (hh - 1) n' w u + ∑ w, A (hh - 1) n' v w * EB w u)) with hLsum
  have hamp : A hh n v u = ampOf Cc s T hh n v u P F := by
    simp only [hA, ampQ, hn1, hnN, and_self, ↓reduceIte]; rfl
  rw [hamp]
  have hlev := ampOf_level_le (T₀ := traceT Cc s (K₀ + R) (J₀ + R) hh n v u)
    (Sg := ENNReal.ofReal Csrc * Lsum) hseq hhH hn1 hnN hT hJw hv0 hG v u
    (fun m hm α x t ht => blockF_box hseq hhH (by omega) hFsZ α v u x (hJw ht))
    (fun m hm α x => (hreg hh hhH n hn1 hnN m hm α v u x).1)
    (fun m hm α x => (hreg hh hhH n hn1 hnN m hm α v u x).2) ?_ ?_
  · refine hlev.trans ?_
    unfold levelK
    have hK : engK (metricΓ CG (K₀ + R)) P ^ (1 / 2 : ℝ) ≤
        engK (metricΓ CG (K₀ + R)) (K₀ + R) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow (engK_mono _ (by omega)) (by norm_num)
    calc engK (metricΓ CG (K₀ + R)) P ^ (1 / 2 : ℝ) *
          (traceT Cc s (K₀ + R) (J₀ + R) hh n v u + ENNReal.ofReal Csrc * Lsum)
        ≤ engK (metricΓ CG (K₀ + R)) (K₀ + R) ^ (1 / 2 : ℝ) * ((1 + ENNReal.ofReal Csrc) *
            (traceT Cc s (K₀ + R) (J₀ + R) hh n v u + Lsum)) := by
          gcongr
          calc traceT Cc s (K₀ + R) (J₀ + R) hh n v u + ENNReal.ofReal Csrc * Lsum
              ≤ (1 + ENNReal.ofReal Csrc) * traceT Cc s (K₀ + R) (J₀ + R) hh n v u +
                  (1 + ENNReal.ofReal Csrc) * Lsum := by
                gcongr
                · exact le_mul_of_one_le_left zero_le le_self_add
                · exact le_add_self
            _ = _ := by ring
      _ = _ := by rw [hLsum]; ring
  · -- entrance data
    intro m hm α x hx m' hm'
    have hbox := (hseq.2.2.2.2.2.1 hh hhH n m α v u s hsJ).1
    refine (mixInit_blockF_le α v u x hx s hbox (P := P) (by omega) m' (by omega)).trans ?_
    exact pow_le_pow_left₀ zero_le (sum_p_le_traceT Cc s hm (by omega) (by omega) α v u) 2
  · -- source data
    intro σ hσ m hm α x hx X l m' hl hm'
    by_cases h01 : hh = 0 ∧ n = 1
    · obtain ⟨rfl, rfl⟩ := h01
      rw [hzero σ hσ m α v u x, vecJ_zero]
      exact zero_le
    refine (hsrcB hh hhH n hn1 hnN h01 σ hσ m hm α v u x hx X l m' hl hm').trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    rw [hLsum, add_mul]
    refine add_le_add ?_ ?_
    · rw [Finset.sum_mul]
      refine le_trans (Finset.sum_le_sum fun n' hn' => ?_)
        (Finset.sum_le_sum_of_subset_of_nonneg (fun n' hn' => Finset.mem_range.2
          (Finset.mem_Ico.1 hn').2) fun _ _ _ => zero_le)
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hn'
      have ho := ord_lower_deg (K₀ := K₀) (J₀ := J₀) (D := D) hhH h1 h2 hnN
      exact blkJ_le_ampQ Cc hσ h1 (by omega) v u ho.1 ho.2
    · by_cases h0 : hh = 0
      · simp [h0]
      simp only [h0, ↓reduceIte]
      rw [Finset.sum_mul]
      refine le_trans (Finset.sum_le_sum fun n' hn' => ?_)
        (Finset.sum_le_sum_of_subset_of_nonneg (fun n' hn' => Finset.mem_range.2
          (by have := (Finset.mem_Icc.1 hn').2; omega)) fun _ _ _ => zero_le)
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn'
      have ho := ord_lower_grade (K₀ := K₀) (J₀ := J₀) (D := D) hhH (by omega) hn1 hnN h1 h2
      rw [add_mul, Finset.sum_mul, Finset.sum_mul]
      refine add_le_add (Finset.sum_le_sum fun w _ => ?_) (Finset.sum_le_sum fun w _ => ?_)
      · rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (blkJ_le_ampQ Cc hσ h1 h2 w u ho.1 ho.2) zero_le
      · calc blkJ Cc (hh - 1) n' σ v w (P + D) (F + D) * EB w u
            ≤ A (hh - 1) n' v w * decayF s σ * EB w u :=
              mul_le_mul_of_nonneg_right (blkJ_le_ampQ Cc hσ h1 h2 v w ho.1 ho.2) zero_le
          _ = A (hh - 1) n' v w * EB w u * decayF s σ := by ring
end

/-! The core of the quiet-gap decay for fixed data, as a conditional statement: given the block
source bound, the vanishing source of the first level and the regularity of the block sources on
the quiet interval, the target sums at every time of the interval are at most
`finalC · Σ_b Θ^{hh-b} I_b · e^{-(π²/4)(τ-s)}`. -/

section
theorem levelK_ne_top (CG : ℕ → ℝ) (P : ℕ) (Csrc : ℝ) : levelK CG P Csrc ≠ ⊤ := by
  unfold levelK
  refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (engK_ne_top _ _)) ?_
  exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

/-- **The core of the decay bound** (conditional on the source bound and source regularity). -/
theorem decayU_core {N H K₀ k₀ L₀ : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}
    {Q : LiftOperatorData ι h D} {π : ι → ℝ} {t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2}
    {V : ℝ → ℝ → ℝ} {qs qf : ℕ} {b : ι → ι → ℝ} {Θ : ℝ}
    (hset : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V
      H N (K₀ + D * (H + 1) * N) (k₀ + D * (H + 1) * N) (L₀ + D * (H + 1) * N)
      qs qf CG Cw Cj b Θ)
    {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequenceFrom Q (K₀ + D * (H + 1) * N + D + 2)
      (max (k₀ + D * (H + 1) * N + 1) (L₀ + D * (H + 1) * N + 2)) t₀ t₁ N H Cc)
    {s T : ℝ} (hT : 0 < T) (hs : t₀ ≤ s) (hsT : s + T ≤ t₁)
    (hq : IsQuietOn Q.edge (fun τ z => Real.sqrt Q.η • Q.v τ z) (Icc s (s + T)))
    {I : ℕ → ℝ}
    (htr : HasQuietEntranceTrace π Cc s lam N H (K₀ + D * (H + 1) * N)
      (max k₀ (L₀ + 2) + D * (H + 1) * N) I)
    {Csrc : ℝ} {rE : ℕ} (hrE : rE ≤ qs)
    (hsrcB : ∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ N → ¬(hh = 0 ∧ n = 1) →
      ∀ σ ∈ Icc s (s + T), ∀ m, m ≤ n → ∀ (α : DerivativeWord2 m) (v u : ι) (x : h u), ‖x‖ ≤ 1 →
      ∀ (X : Vec 2) (l m' : List (Fin 2)), l.length ≤ ordS K₀ D H N hh n →
        m'.length ≤ ordF (max k₀ (L₀ + 2)) D H N hh n →
        vecJ (blockSrc Q Cc hh n α v u x σ) X l m' ≤ ENNReal.ofReal Csrc *
          (∑ n' ∈ Finset.Ico 1 n, blkJ Cc hh n' σ v u (ordS K₀ D H N hh n + D)
              (ordF (max k₀ (L₀ + 2)) D H N hh n + D)
            + (if hh = 0 then 0 else ∑ n' ∈ Finset.Icc 1 N,
              (∑ w, envB Q.edge (Icc t₀ t₁) rE v w * blkJ Cc (hh - 1) n' σ w u
                  (ordS K₀ D H N hh n + D) (ordF (max k₀ (L₀ + 2)) D H N hh n + D)
                + ∑ w, blkJ Cc (hh - 1) n' σ v w (ordS K₀ D H N hh n + D)
                  (ordF (max k₀ (L₀ + 2)) D H N hh n + D) * envB Q.edge (Icc t₀ t₁) rE w u))))
    (hzero : ∀ σ ∈ Icc s (s + T), ∀ m (α : DerivativeWord2 m) (v u : ι) (x : h u),
      blockSrc Q Cc 0 1 α v u x σ = fun _ _ => 0)
    (hreg : ∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ N → ∀ m, m ≤ n → ∀ (α : DerivativeWord2 m)
      (v u : ι) (x : h u),
      (∀ t ∈ Icc s (s + T), IsBoxSmooth (ordS K₀ D H N hh n + 1)
        (ordF (max k₀ (L₀ + 2)) D H N hh n) (blockSrc Q Cc hh n α v u x t) ∧
        ∀ X, AVenhance.IsZ2Periodic (blockSrc Q Cc hh n α v u x t X)) ∧
      ∀ X, AEStronglyMeasurable (fun p : ℝ × Vec 2 => blockSrc Q Cc hh n α v u x p.1 X p.2)
        (winMeasure (Icc s (s + T))))
    {hh : ℕ} (hhH : hh ≤ H) {τ : ℝ} (hτ : τ ∈ Icc s (s + T)) {p q : ℕ} (hp : p ≤ K₀)
    (hq' : q ≤ max k₀ (L₀ + 2)) :
    ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.range (n + 1), schurMixedCellL2Jet π {τ} p q (Cc hh n m) ≤
      ENNReal.ofReal (finalC N H ((N + 1) * (K₀ + D * (H + 1) * N + 1) *
          (max k₀ (L₀ + 2) + D * (H + 1) * N + 1))
          (levelK CG (K₀ + D * (H + 1) * N) Csrc).toReal (envC Cj rE) *
        (∑ b ∈ Finset.range (hh + 1), Θ ^ (hh - b) * I b) *
        Real.exp (-(Real.pi ^ 2 / 4 * (τ - s)))) := by
  set R := D * (H + 1) * N with hR
  set J₀ := max k₀ (L₀ + 2) with hJ₀
  have hN1 : 1 ≤ N := hset.N_ge
  have hD2 : 2 ≤ D := hset.D_ge
  have hR2 : 2 ≤ R := by
    have : D ≤ D * (H + 1) * N := by
      calc D = D * 1 * 1 := by ring
        _ ≤ D * (H + 1) * N := by gcongr; omega
    omega
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨v₀⟩⟩
  · have h0 : ∀ (N' : ι → ι → ℝ≥0∞), schurSums π N' = 0 := fun N' => by simp [schurSums]
    simp only [schurMixedCellL2Jet, h0, Finset.sum_const_zero]
    exact zero_le
  have hlam0 : 0 ≤ lam := by rw [hset.lam_eq]; exact div_nonneg hset.ρ_pos.le hset.E_pos.le
  have hΘ : 0 ≤ Θ := le_trans (Finset.sum_nonneg fun u _ => hset.envelope.nonneg v₀ u)
    (hset.envelope.row_sum v₀)
  have hv0 := v_eq_zero_of_quiet hset hq
  have hJw : Icc s (s + T) ⊆ Icc t₀ t₁ := fun t ht => ⟨hs.trans ht.1, ht.2.trans hsT⟩
  have hrec := fun hh' (hh'H : hh' ≤ H) n (hn1 : 1 ≤ n) (hnN : n ≤ N) v u =>
    ampQ_rec hset hseq hT.le hs hsT hv0 (envB Q.edge (Icc t₀ t₁) rE) hsrcB hzero hreg hh'H hn1 hnN v u
  set Kc := levelK CG (K₀ + R) Csrc with hKc
  have hKc' : Kc = ENNReal.ofReal Kc.toReal := (ENNReal.ofReal_toReal (levelK_ne_top _ _ _)).symm
  have hcE := envC_nonneg Cj rE
  have hclose := decay_close_ennreal (Kc := Kc) hset.mass_pos htr hlam0 hset.lam_le le_rfl le_rfl
    (b := fun v w => ENNReal.ofReal (envC Cj rE * b v w)) (Θ := ENNReal.ofReal (envC Cj rE * Θ))
    (fun v => by
      rw [← ENNReal.ofReal_sum_of_nonneg fun u _ => mul_nonneg hcE (hset.envelope.nonneg v u),
        ← Finset.mul_sum]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hset.envelope.row_sum v) hcE))
    (fun u => by
      rw [← ENNReal.ofReal_sum_of_nonneg fun v _ => mul_nonneg hcE (hset.envelope.nonneg v u),
        ← Finset.mul_sum]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hset.envelope.col_sum u) hcE))
    (envB Q.edge (Icc t₀ t₁) rE)
    (fun v w => massW_envB_le hset.envelope hlam0 hset.lam_le hrE v w)
    hrec hτ hhH
    (fun n _ _ m _ α v u => hseq.2.2.2.2.2.1 hh hhH n m α v u τ (hJw hτ))
    (D := D) (K₀ := K₀) hp hq' (by omega)
    (by
      have : J₀ + R ≤ max (k₀ + R + 1) (L₀ + R + 2) := by
        rw [hJ₀]; rcases le_total k₀ (L₀ + 2) with hk | hk
        · rw [max_eq_right hk]; exact le_max_of_le_right (by omega)
        · rw [max_eq_left hk]; exact le_max_of_le_left (by omega)
      omega)
  refine hclose.trans ?_
  have hc2 := close_real (N := N) (cT := (N + 1) * (K₀ + R + 1) * (J₀ + R + 1)) (K := Kc.toReal)
    hhH ENNReal.toReal_nonneg hcE hΘ (fun b' hb' => htr.1 b' (hb'.trans hhH)) s τ
  rw [← hKc'] at hc2
  exact hc2
end

end AVRegularity.QuietDecay
end
end

section
@[expose] public noncomputable section
section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! The regularity premises of `decayU_core`: box smoothness at the level orders, periodicity and
measurability of the block sources on the quiet interval, and the vanishing source of `(0, 1)`. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

variable {N H K₀ k₀ L₀ : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}
    {Q : LiftOperatorData ι h D} {π : ι → ℝ} {t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2}
    {V : ℝ → ℝ → ℝ} {qs qf : ℕ} {b : ι → ι → ℝ} {Θ : ℝ} {Cc : ℕ → ℕ → LiftCoeff ι h}

theorem R_ge_D (hN : 1 ≤ N) : D ≤ D * (H + 1) * N := by
  calc D = D * 1 * 1 := by ring
    _ ≤ D * (H + 1) * N := by gcongr; omega

theorem final_hDsZ (hN : 1 ≤ N) :
    D ≤ max (k₀ + D * (H + 1) * N + 1) (L₀ + D * (H + 1) * N + 2) := by
  have := R_ge_D (D := D) (H := H) hN
  exact le_max_of_le_left (by omega)

/-- The regularity premise of `decayU_core`. -/
theorem final_hreg
    (hset : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V
      H N (K₀ + D * (H + 1) * N) (k₀ + D * (H + 1) * N) (L₀ + D * (H + 1) * N)
      qs qf CG Cw Cj b Θ)
    (hseq : IsLiftSequenceFrom Q (K₀ + D * (H + 1) * N + D + 2)
      (max (k₀ + D * (H + 1) * N + 1) (L₀ + D * (H + 1) * N + 2)) t₀ t₁ N H Cc)
    {s T : ℝ} (hs : t₀ ≤ s) (hsT : s + T ≤ t₁)
    (hq : IsQuietOn Q.edge (fun τ z => Real.sqrt Q.η • Q.v τ z) (Icc s (s + T))) :
    ∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ N → ∀ m, m ≤ n → ∀ (α : DerivativeWord2 m)
      (v u : ι) (x : h u),
      (∀ t ∈ Icc s (s + T), IsBoxSmooth (ordS K₀ D H N hh n + 1)
        (ordF (max k₀ (L₀ + 2)) D H N hh n) (blockSrc Q Cc hh n α v u x t) ∧
        ∀ X, AVenhance.IsZ2Periodic (blockSrc Q Cc hh n α v u x t X)) ∧
      ∀ X, AEStronglyMeasurable (fun p : ℝ × Vec 2 => blockSrc Q Cc hh n α v u x p.1 X p.2)
        (winMeasure (Icc s (s + T))) := by
  intro hh hhH n hn1 hnN m hm α v u x
  have hN1 : 1 ≤ N := hset.N_ge
  have hD2 : 2 ≤ D := hset.D_ge
  have hDsZ := final_hDsZ (D := D) (H := H) (k₀ := k₀) (L₀ := L₀) hN1
  have hJw : Icc s (s + T) ⊆ Icc t₀ t₁ := fun t ht => ⟨hs.trans ht.1, ht.2.trans hsT⟩
  refine ⟨fun t ht => ?_, fun X => sreg_blockSrc_aesm hset hDsZ hseq measurableSet_Icc
    ordConnected_Icc hJw hq hhH hn1 hnN α v u x X⟩
  by_cases h01 : hh = 0 ∧ n = 1
  · obtain ⟨rfl, rfl⟩ := h01
    exact sreg_blockSrc_box_zero hset hDsZ hseq hJw hq _ _ α v u x ht
  -- a level of positive rank carries a reserve `≥ D` below the top
  have hr : 1 ≤ rankOf N hh n := by
    unfold rankOf
    by_contra hc
    rw [not_le] at hc
    have : hh * N = 0 := by omega
    rcases Nat.mul_eq_zero.1 this with h0 | h0
    · exact h01 ⟨h0, by omega⟩
    · omega
  have hres := resv_add_le (D := D) (H := H) (N := N) (r' := 0) (r := rankOf N hh n) (by omega)
    (rankOf_le hhH hn1 hnN)
  have hres0 := resv_le_R (D := D) (H := H) (r := 0) hN1
  have hqs : qs = K₀ + D * (H + 1) * N + 4 * (H + 1) * (N + D) ^ 2 := hset.qs_eq
  have hRD := R_ge_D (D := D) (H := H) hN1
  have hF : ordF (max k₀ (L₀ + 2)) D H N hh n + D ≤
      max (k₀ + D * (H + 1) * N + 1) (L₀ + D * (H + 1) * N + 2) := by
    unfold ordF
    rcases le_total k₀ (L₀ + 2) with hk | hk
    · rw [max_eq_right hk]; exact le_max_of_le_right (by omega)
    · rw [max_eq_left hk]; exact le_max_of_le_left (by omega)
  refine sreg_blockSrc_box hset hDsZ hseq hJw hq (by unfold ordS; omega) hF
    (by unfold ordS; rw [hqs]; nlinarith) hhH hn1 hnN α v u x ht

/-- The vanishing source of the first level. -/
theorem final_hzero
    (hset : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V
      H N (K₀ + D * (H + 1) * N) (k₀ + D * (H + 1) * N) (L₀ + D * (H + 1) * N)
      qs qf CG Cw Cj b Θ)
    (hseq : IsLiftSequenceFrom Q (K₀ + D * (H + 1) * N + D + 2)
      (max (k₀ + D * (H + 1) * N + 1) (L₀ + D * (H + 1) * N + 2)) t₀ t₁ N H Cc)
    {s T : ℝ} (hs : t₀ ≤ s) (hsT : s + T ≤ t₁)
    (hq : IsQuietOn Q.edge (fun τ z => Real.sqrt Q.η • Q.v τ z) (Icc s (s + T))) :
    ∀ σ ∈ Icc s (s + T), ∀ m (α : DerivativeWord2 m) (v u : ι) (x : h u),
      blockSrc Q Cc 0 1 α v u x σ = fun _ _ => 0 := fun _ hσ _ α v u x =>
  sreg_blockSrc_zero hset (final_hDsZ hset.N_ge) hseq
    (fun _ ht => ⟨hs.trans ht.1, ht.2.trans hsT⟩) hq α v u x hσ
end

/-! **The quiet-gap decay of the lift recursion** (`DecayStatementU` without the slow scale
factor) and **the statement `Statement`** of
`Providers.cycle_residual_partition_differentiated` from it.
The source bound of `decayU_core` is `blockSrc_vecJ_le` at the level orders, with the pointwise
edge sums raised to the uniform envelope `envB` and the source constants summed over the finitely
many level orders; regularity and the zero first source are `final_hreg`, `final_hzero`. -/

section
universe u v

/-- The uniform source constant. -/
def srcConstU (N D H K₀ J₀ : ℕ) (CG : ℕ → ℝ) : ℝ :=
  ∑ p ∈ Finset.range (K₀ + D * (H + 1) * N + 1), ∑ q ∈ Finset.range (J₀ + D * (H + 1) * N + 3),
    srcConst p q N D CG

theorem srcConst_le_srcConstU {N D H K₀ J₀ p q : ℕ} (CG : ℕ → ℝ) (hp : p ≤ K₀ + D * (H + 1) * N)
    (hq : q ≤ J₀ + D * (H + 1) * N + 2) : srcConst p q N D CG ≤ srcConstU N D H K₀ J₀ CG := by
  unfold srcConstU
  refine le_trans ?_ (Finset.single_le_sum (f := fun p => ∑ q ∈ Finset.range
    (J₀ + D * (H + 1) * N + 3), srcConst p q N D CG)
    (fun p _ => Finset.sum_nonneg fun q _ => srcConst_nonneg p q N D CG)
    (Finset.mem_range.2 (show p < K₀ + D * (H + 1) * N + 1 by omega)))
  exact Finset.single_le_sum (f := fun q => srcConst p q N D CG)
    (fun q _ => srcConst_nonneg p q N D CG)
    (Finset.mem_range.2 (show q < J₀ + D * (H + 1) * N + 3 by omega))

theorem ordF_add_D_le {N D H k₀ L₀ hh n : ℕ} (hN1 : 1 ≤ N) (hD2 : 2 ≤ D) (hhH : hh ≤ H) (hn1 : 1 ≤ n)
    (hnN : n ≤ N) (h01 : ¬(hh = 0 ∧ n = 1)) :
    ordF (max k₀ (L₀ + 2)) D H N hh n + D ≤
      max (k₀ + D * (H + 1) * N + 1) (L₀ + D * (H + 1) * N + 2) := by
  have hr : 1 ≤ rankOf N hh n := by
    unfold rankOf
    by_contra hc
    rw [not_le] at hc
    have : hh * N = 0 := by omega
    rcases Nat.mul_eq_zero.1 this with h0 | h0
    · exact h01 ⟨h0, by omega⟩
    · omega
  have hres := resv_add_le (D := D) (H := H) (N := N) (r' := 0) (r := rankOf N hh n) (by omega)
    (rankOf_le hhH hn1 hnN)
  have hres0 := resv_le_R (D := D) (H := H) (r := 0) hN1
  unfold ordF
  rcases le_total k₀ (L₀ + 2) with hk | hk
  · rw [max_eq_right hk]; exact le_max_of_le_right (by omega)
  · rw [max_eq_left hk]; exact le_max_of_le_left (by omega)

/-- **The quiet-gap decay statement** (without the slow scale factor). -/
theorem decayStatementU (N D H K₀ k₀ L₀ : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    DecayStatementU.{u, v} N D H K₀ k₀ L₀ CG Cw Cj := by
  set R := D * (H + 1) * N with hR
  set J₀ := max k₀ (L₀ + 2) with hJ₀
  set Csrc := srcConstU N D H K₀ J₀ CG
  set rE := K₀ + R + N
  refine ⟨finalC N H ((N + 1) * (K₀ + R + 1) * (J₀ + R + 1))
      (levelK CG (K₀ + R) Csrc).toReal (envC Cj rE), Real.pi ^ 2 / 4,
    finalC_nonneg _ _ _ ENNReal.toReal_nonneg _, by positivity, ?_⟩
  intro ι _ h _ _ _ _ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf b Θ hset Cc hseq s T hT hs
    hsT hq I hI hh hhH τ hτ p hp q hq'
  classical
  have hN1 : 1 ≤ N := hset.N_ge
  have hD2 : 2 ≤ D := hset.D_ge
  have hqs : qs = K₀ + R + 4 * (H + 1) * (N + D) ^ 2 := hset.qs_eq
  have hJw : Icc s (s + T) ⊆ Icc t₀ t₁ := fun t ht => ⟨hs.trans ht.1, ht.2.trans hsT⟩
  have hDsZ := final_hDsZ (D := D) (H := H) (k₀ := k₀) (L₀ := L₀) hN1
  have hbig : N + 2 ≤ 4 * (H + 1) * (N + D) ^ 2 := by
    have h1 : N + 2 ≤ (N + D) ^ 2 := by nlinarith
    have h2 : (N + D) ^ 2 ≤ 4 * (H + 1) * (N + D) ^ 2 := Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have hrE : rE ≤ qs := by rw [hqs]; omega
  refine decayU_core hset hseq hT hs hsT hq hI hrE ?_ (final_hzero hset hseq hs hsT hq)
    (final_hreg hset hseq hs hsT hq) hhH hτ hp hq'
  intro hh' hh'H n hn1 hnN h01 σ hσ m hm α v u x hx X l m' hl hm'
  have hS := ordS_le (K₀ := K₀) (D := D) (H := H) (hh := hh') (n := n) hN1
  have hF := ordF_le (J₀ := J₀) (D := D) (H := H) (hh := hh') (n := n) hN1
  have hb := blockSrc_vecJ_le hDsZ hset hseq hJw hq hh'H hn1 hnN (p := ordS K₀ D H N hh' n)
    (q := ordF J₀ D H N hh' n) (by omega) (ordF_add_D_le hN1 hD2 hh'H hn1 hnN h01)
    (by rw [hqs]; omega) α hm v u x hx hσ X l m' hl hm'
  refine hb.trans ?_
  have hσ' : σ ∈ Icc t₀ t₁ := hJw hσ
  have henv : ∀ v w, edgeEnv Q σ X v w (ordS K₀ D H N hh' n + N) ≤ envB Q.edge (Icc t₀ t₁) rE v w :=
    fun v w => (edgeEnv_mono Q σ X v w (r' := rE) (by omega)).trans (by
      unfold edgeEnv; exact edgeSum_le_envB Q.edge hσ' X v w rE)
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal (srcConst_le_srcConstU CG (by omega) (by omega)))
    (add_le_add le_rfl ?_)
  split_ifs with h0
  · exact le_rfl
  · exact Finset.sum_le_sum fun n' _ => add_le_add
      (Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_right (henv v w) zero_le)
      (Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (henv w u) zero_le)

/-- **The statement of `Providers.cycle_residual_partition_differentiated`.** -/
theorem statement (Acl N D H kl Ll : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    Statement.{u, v} Acl N D H kl Ll CG Cw Cj :=
  statement_of_decayU Acl N D H kl Ll CG Cw Cj fun r =>
    decayStatementU N D H (Acl + 2 + r) (kl + r) (Ll + r) CG Cw Cj
end

end AVRegularity.QuietDecay
end
end
end
