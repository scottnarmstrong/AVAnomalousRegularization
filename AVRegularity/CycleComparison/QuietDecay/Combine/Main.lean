-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.QuietDecay.Combine.Unif

/-! **The combined source bound of one block at one quiet time.** The block source is recentred at
the slow point (`blockSrc_recentre`), the weights `c_S` are handled by the Leibniz rule, the quiet
source of each monomial test field is the sum of the five parts, and each part is bounded by its
part bound (A)-(E); all part terms are placed in the common sums of block jets of orders
`(p + D, q + D)`. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.QuietDecay

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

/-- **The combined source bound of one block at one quiet time.** -/
theorem blockSrc_vecJ_le {N K k L H : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ}
    (hDsZ : D ≤ max (k + 1) (L + 2)) {Q : LiftOperatorData ι h D} {π : ι → ℝ}
    {t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ} {qs qf : ℕ}
    {b : ι → ι → ℝ} {Θ : ℝ}
    (hset : IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ)
    {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequenceFrom Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc)
    {S : Set ℝ} (hS : S ⊆ Icc t₀ t₁)
    (hq : IsQuietOn Q.edge (fun t z => Real.sqrt Q.η • Q.v t z) S)
    {hh n : ℕ} (hhH : hh ≤ H) (hn1 : 1 ≤ n) (hnN : n ≤ N) {p q : ℕ} (hpK : p + 1 ≤ K)
    (hqF : q + D ≤ max (k + 1) (L + 2)) (hpq : p + N + 2 ≤ qs)
    {m : ℕ} (α : DerivativeWord2 m) (hm : m ≤ n) (v u : ι) (x : h u) (hx : ‖x‖ ≤ 1) {σ : ℝ}
    (hσ : σ ∈ S) (X : Vec 2) (l m' : List (Fin 2)) (hl : l.length ≤ p) (hm' : m'.length ≤ q) :
    vecJ (blockSrc Q Cc hh n α v u x σ) X l m' ≤ ENNReal.ofReal (srcConst p q N D CG) *
      ( ∑ n' ∈ Finset.Ico 1 n, blkJ Cc hh n' σ v u (p + D) (q + D)
        + (if hh = 0 then 0 else ∑ n' ∈ Finset.Icc 1 N,
            (∑ w, edgeEnv Q σ X v w (p + N) * blkJ Cc (hh - 1) n' σ w u (p + D) (q + D)
              + ∑ w, blkJ Cc (hh - 1) n' σ v w (p + D) (q + D) * edgeEnv Q σ X w u (p + N))) ) := by
  have H0 := comb_hyp_of_setting hset hseq hS hq hσ hhH X hpK hqF hpq
  have hΓ0 : 0 ≤ metricΓ CG (p + N + 1) := metricΓ_nonneg CG _
  have hdec : blockSrc Q Cc hh n α v u x σ = fun X' z => ∑ T : Finset (Fin (List.ofFn α).length),
      cS X (List.ofFn α) T X' •
        combF Q Cc σ hh n X (subWord (List.ofFn α) T) u x v X' z := by
    funext X' z
    exact blockSrc_recentre hDsZ hset hseq hS hq hhH hn1 hnN (by omega) α v u x hσ X X' z
  have hbox : ∀ T : Finset (Fin (List.ofFn α).length),
      IsBoxSmooth p q (combF Q Cc σ hh n X (subWord (List.ofFn α) T) u x v) := fun T =>
    comb_boxF H0 (subWord (List.ofFn α) T) u x v hnN
  have hcd : ∀ T : Finset (Fin (List.ofFn α).length),
      ContDiff ℝ (p : ℕ∞) (cS X (List.ofFn α) T) := fun T => contDiff_cS _ _ _ _
  have hboxBS : IsBoxSmooth p q (blockSrc Q Cc hh n α v u x σ) := by
    rw [hdec]
    exact IsBoxSmooth.sum _ fun T _ => (hbox T).smul_slow (hcd T)
  have hlen : (List.ofFn α).length = m := List.length_ofFn
  have hp0 : l.length ≤ p := hl
  have hq0 : m'.length ≤ q := hm'
  refine (comb_vecJ_le_ptJet hboxBS l m' hl hm' X).trans ?_
  set Bs := combBsum Q Cc σ hh n N p q X u v with hBs
  set Kc : ℝ≥0∞ := ENNReal.ofReal (srcK p q N D (metricΓ CG (p + N + 1))) with hKc
  have hbound : ptJet (blockSrc Q Cc hh n α v u x σ) X l.length m'.length ≤
      (Fintype.card (Finset (Fin (List.ofFn α).length)) : ℝ≥0∞) *
        (2 ^ l.length * ENNReal.ofReal (2 ^ p * (N.factorial : ℝ))) *
        (2 ^ (p + q) * (Kc * Bs)) := by
    rw [hdec]
    refine comb_smul_sum_le (fun T => cS X (List.ofFn α) T)
      (fun T => combF Q Cc σ hh n X (subWord (List.ofFn α) T) u x v) hp0 hq0 X hcd hbox
      (Cb := 2 ^ p * (N.factorial : ℝ)) (fun T i hi => ?_) (fun T i hi => ?_)
    · refine (comb_cS_iter_le X (List.ofFn α) T i).trans ?_
      rw [hlen]
      have h1 : (2 : ℝ) ^ i ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) (by omega)
      have h2 : (m.factorial : ℝ) ≤ N.factorial := by exact_mod_cast Nat.factorial_le (by omega)
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    · have hβ : (subWord (List.ofFn α) T).length ≤ N := by
        have := length_subWord_le (List.ofFn α) T
        rw [hlen] at this; omega
      refine (comb_ptJetF_unif H0 (subWord (List.ofFn α) T) u x hx v (p0 := l.length - i)
        (q0 := m'.length) (by omega) hq0 hΓ0 hβ hn1 hnN).trans ?_
      refine mul_le_mul' ?_ le_rfl
      exact pow_right_mono₀ one_le_two (by omega)
  refine hbound.trans ?_
  have hcard : (Fintype.card (Finset (Fin (List.ofFn α).length)) : ℝ≥0∞) = 2 ^ m := by
    rw [Fintype.card_finset, Fintype.card_fin, hlen]; simp
  rw [hcard]
  have hK0 := srcK_nonneg p q N D hΓ0
  have key : (2 : ℝ≥0∞) ^ m * (2 ^ l.length * ENNReal.ofReal (2 ^ p * (N.factorial : ℝ))) *
      (2 ^ (p + q) * Kc) ≤ ENNReal.ofReal (srcConst p q N D CG) := by
    have e : (2 : ℝ≥0∞) ^ m * (2 ^ l.length * ENNReal.ofReal (2 ^ p * (N.factorial : ℝ))) *
        (2 ^ (p + q) * Kc) = ENNReal.ofReal ((2 : ℝ) ^ m * (2 ^ l.length *
          (2 ^ p * (N.factorial : ℝ))) * (2 ^ (p + q) * srcK p q N D (metricΓ CG (p + N + 1)))) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_pow (by norm_num)]
      simp [hKc]
    rw [e]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold srcConst
    have h1 : (2 : ℝ) ^ m ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ l.length ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) hl
    have h4 : (4 : ℝ) ^ p = 2 ^ p * 2 ^ p := by
      rw [← mul_pow]; norm_num
    rw [h4]
    have hN : (0 : ℝ) ≤ N.factorial := by positivity
    calc (2 : ℝ) ^ m * (2 ^ l.length * (2 ^ p * (N.factorial : ℝ))) *
          (2 ^ (p + q) * srcK p q N D (metricΓ CG (p + N + 1)))
        ≤ 2 ^ N * (2 ^ p * (2 ^ p * (N.factorial : ℝ))) *
          (2 ^ (p + q) * srcK p q N D (metricΓ CG (p + N + 1))) := by
          gcongr
      _ = _ := by ring
  calc (2 : ℝ≥0∞) ^ m * (2 ^ l.length * ENNReal.ofReal (2 ^ p * (N.factorial : ℝ))) *
        (2 ^ (p + q) * (Kc * Bs))
      = ((2 : ℝ≥0∞) ^ m * (2 ^ l.length * ENNReal.ofReal (2 ^ p * (N.factorial : ℝ))) *
        (2 ^ (p + q) * Kc)) * Bs := by ring
    _ ≤ ENNReal.ofReal (srcConst p q N D CG) * Bs := mul_le_mul' key le_rfl

end AVRegularity.QuietDecay
