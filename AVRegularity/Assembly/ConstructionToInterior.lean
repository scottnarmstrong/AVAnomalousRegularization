-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Definitions.CsNormLe
public import AVRegularity.Statements.Definitions.IsHolderDivFreeVelocity
public import AVRegularity.Statements.Definitions.IsWeakSolutionOn
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
import AVRegularity.Statements.Construction.ExistsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Construction.OcBandSet
import AVRegularity.Construction.Scales.Times

/-! Conditional existential packaging of the construction-level theorem. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization AVenhance
open scoped Topology
noncomputable section

namespace AVRegularity.Assembly

private theorem exists_admissibleQ
    {α s : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) :
    ∃ q : ℝ, IsAdmissibleQ α s q := by
  have hαden : 0 < 2 * α := by positivity
  have hsden : 0 < α + s := by positivity
  have hq₂ : 1 < (2 - (1 + α)) / (2 * ((1 + α) - 1)) := by
    rw [show 2 - (1 + α) = 1 - α by ring,
      show (1 + α) - 1 = α by ring]
    apply (lt_div_iff₀ hαden).2
    nlinarith
  have hq₃ : 1 < (1 - s) / ((1 + α) - 1 + s) := by
    rw [show (1 + α) - 1 + s = α + s by ring]
    apply (lt_div_iff₀ hsden).2
    nlinarith
  have hq₁₆ : 1 < (17 : ℝ) / 16 := by norm_num
  let U : ℝ := min (17 / 16)
    (min ((2 - (1 + α)) / (2 * ((1 + α) - 1)))
      ((1 - s) / ((1 + α) - 1 + s)))
  have hU : 1 < U := by
    dsimp [U]
    exact lt_min hq₁₆ (lt_min hq₂ hq₃)
  let q : ℝ := (1 + U) / 2
  have hqlo : 1 < q := by dsimp [q]; linarith
  have hqhi : q < U := by dsimp [q]; linarith
  have hq16' : q < (17 : ℝ) / 16 := by
    exact lt_of_lt_of_le hqhi (min_le_left _ _)
  have hq2' : q < (2 - (1 + α)) / (2 * ((1 + α) - 1)) := by
    exact lt_of_lt_of_le hqhi (le_trans (min_le_right _ _) (min_le_left _ _))
  have hq3' : q < (1 - s) / ((1 + α) - 1 + s) := by
    exact lt_of_lt_of_le hqhi (le_trans (min_le_right _ _) (min_le_right _ _))
  exact ⟨q, hqlo, hq16', hq2', hq3'⟩

private theorem beta_sub_gamma_gt_two_sevenths
    {α s q : ℝ} (hα₀ : 0 < α) (hq : IsAdmissibleQ α s q) :
    2 / 7 < (1 + α) - ocGamma α q := by
  have hqden : 0 < q + 1 := by linarith [hq.1]
  have hqden' : q + 1 < (33 : ℝ) / 16 := by linarith [hq.2.1]
  have hratio : (32 : ℝ) / 33 < 2 * (1 + α) / (q + 1) := by
    calc
      (32 : ℝ) / 33 = 2 / (33 / 16) := by norm_num
      _ < 2 / (q + 1) := by
        apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 33 / 16) hqden).2
        nlinarith [hqden']
      _ ≤ 2 * (1 + α) / (q + 1) := by
        apply div_le_div_of_nonneg_right _ hqden.le
        nlinarith [hα₀]
  have hnum : (1 + α) - ocGamma α q = 2 * (1 + α) / (q + 1) := by
    unfold ocGamma
    field_simp [ne_of_gt hqden]
    ring
  rw [hnum]
  norm_num at hratio ⊢
  exact lt_trans (by norm_num) hratio

private theorem band_sequence_pos
    {α s q : ℝ} {Λ : ℕ} (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ)
    (p : ℝ) (M : ℕ) :
    0 < ocEpsilon q Λ (M + 1) ^ p := by
  exact Real.rpow_pos_of_pos (Scales.epsilon_basic (m := M + 1) hq.1 hΛ).1 p

private theorem band_sequence_gap
    {α s q : ℝ} {Λ : ℕ} (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ)
    (p : ℝ) (hp : 2 / 7 < p) (M : ℕ) :
    4 * ocEpsilon q Λ (M + 2) ^ p < ocEpsilon q Λ (M + 1) ^ p := by
  have heprev : 0 < ocEpsilon q Λ (M + 1) :=
    (Scales.epsilon_basic (m := M + 1) hq.1 hΛ).1
  have henext : 0 < ocEpsilon q Λ (M + 2) :=
    (Scales.epsilon_basic (m := M + 2) hq.1 hΛ).1
  have hratio := Scales.epsilon_ratio_lower hq.1 hΛ (m := M + 2) (by omega)
  have hratio128 : (128 : ℝ) ≤
      ocEpsilon q Λ (M + 1) / ocEpsilon q Λ (M + 2) := by
    have hΛr : (128 : ℝ) ≤ Λ := by exact_mod_cast hΛ
    have hratio' := hΛr.trans hratio
    simpa [Nat.add_sub_cancel] using hratio'
  have hscale : 128 * ocEpsilon q Λ (M + 2) ≤ ocEpsilon q Λ (M + 1) :=
    (le_div_iff₀ henext).1 hratio128
  have h128p : 4 < (128 : ℝ) ^ p := by
    have hpow := Real.rpow_lt_rpow_of_exponent_lt
      (by norm_num : (1 : ℝ) < 128) hp
    have hbase : (128 : ℝ) ^ ((2 : ℝ) / 7) = 4 := by
      calc
        (128 : ℝ) ^ ((2 : ℝ) / 7) = (2 ^ 7) ^ ((2 : ℝ) / 7) :=
          congrArg (fun x : ℝ => x ^ ((2 : ℝ) / 7))
            (by norm_num : (128 : ℝ) = 2 ^ 7)
        _ = ((2 : ℝ) ^ (7 : ℝ)) ^ ((2 : ℝ) / 7) := by
          exact congrArg (fun x : ℝ => x ^ ((2 : ℝ) / 7))
            (Real.rpow_natCast (2 : ℝ) 7).symm
        _ = 2 ^ ((7 : ℝ) * ((2 : ℝ) / 7)) :=
          (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) 7 ((2 : ℝ) / 7)).symm
        _ = 4 := by norm_num
    exact hbase ▸ hpow
  have henextp : 0 < ocEpsilon q Λ (M + 2) ^ p :=
    Real.rpow_pos_of_pos henext p
  have hscaledp :
      (128 : ℝ) ^ p * ocEpsilon q Λ (M + 2) ^ p ≤
        ocEpsilon q Λ (M + 1) ^ p := by
    calc
      (128 : ℝ) ^ p * ocEpsilon q Λ (M + 2) ^ p =
          (128 * ocEpsilon q Λ (M + 2)) ^ p := by
        rw [Real.mul_rpow (by norm_num) henext.le]
      _ ≤ ocEpsilon q Λ (M + 1) ^ p :=
        Real.rpow_le_rpow (by positivity) hscale (by linarith)
  calc
    4 * ocEpsilon q Λ (M + 2) ^ p <
        (128 : ℝ) ^ p * ocEpsilon q Λ (M + 2) ^ p :=
      mul_lt_mul_of_pos_right h128p henextp
    _ ≤ ocEpsilon q Λ (M + 1) ^ p := hscaledp

private theorem shifted_band_eq
    (α q : ℝ) (Λ : ℕ) (p : ℝ)
    (hp : p = (1 + α) - ocGamma α q) :
    (⋃ M : ℕ, Set.Icc
      (ocEpsilon q Λ (M + 1) ^ p / 2)
      (2 * ocEpsilon q Λ (M + 1) ^ p)) = ocBandSet α q Λ := by
  classical
  apply Set.ext
  intro κ
  constructor
  · intro hκ
    rcases Set.mem_iUnion.mp hκ with ⟨M, hκ⟩
    rw [ocBandSet]
    apply Set.mem_iUnion.mpr
    refine ⟨M + 1, ?_⟩
    apply Set.mem_iUnion.mpr
    refine ⟨by omega, ?_⟩
    simpa [hp] using hκ
  · intro hκ
    rw [ocBandSet] at hκ
    rcases Set.mem_iUnion.mp hκ with ⟨M, hκ⟩
    rcases Set.mem_iUnion.mp hκ with ⟨hM, hκ⟩
    obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : M ≠ 0)
    apply Set.mem_iUnion.mpr
    refine ⟨N, ?_⟩
    simpa [hp, Nat.succ_eq_add_one] using hκ

/-- The bands of the construction as `⋃_M [κ_M/2, 2κ_M]`, with `κ_M = ε_{M+1}^{β-γ} > 0` and
`4κ_{M+1} < κ_M`. -/
theorem exists_bandCenters_eq_ocBandSet {α s q : ℝ} (hα₀ : 0 < α) (hq : IsAdmissibleQ α s q)
    {Λ : ℕ} (hΛ : 128 ≤ Λ) :
    ∃ κc : ℕ → ℝ, (∀ M, 0 < κc M) ∧ (∀ M, 4 * κc (M + 1) < κc M) ∧
      (⋃ M : ℕ, Set.Icc (κc M / 2) (2 * κc M)) = ocBandSet α q Λ := by
  have hp : 2 / 7 < (1 + α) - ocGamma α q := beta_sub_gamma_gt_two_sevenths hα₀ hq
  exact ⟨fun M => ocEpsilon q Λ (M + 1) ^ ((1 + α) - ocGamma α q),
    fun M => band_sequence_pos hq hΛ _ M, fun M => band_sequence_gap hq hΛ _ hp M,
    shifted_band_eq α q Λ _ rfl⟩

/-- The existential form of Theorem A of the paper follows from its form for the velocity field
of the construction, which is the hypothesis `hB`. -/
theorem interior_regularity_of_construction
    (hB :
      ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
        (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ)
        (_hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ),
        ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
          (∃ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ) ∧
          ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
            ∃ b : ℝ → Vec 2 → Vec 2,
              (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
              IsHolderDivFreeVelocity α b ∧
              ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C : ℝ,
                ∀ a : ℝ,
                ∀ κ ∈ ocBandSet α q Λ,
                ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
                  (∃ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ) ∧
                  ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ →
                    ∃ Θ : ℝ → Vec 2 → ℝ,
                      ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2)
                        (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) ∧
                      ∀ t ∈ Set.Icc (a + t₀) (a + T),
                        IsZ2Periodic (Θ t) ∧
                        Θ t =ᵐ[volume.restrict unitCube] θ t ∧
                        CsNormLe s (Θ t) (C * Real.sqrt (l2NormSq f))) :
    ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
      (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2),
      ∃ b : ℝ → Vec 2 → Vec 2, IsHolderDivFreeVelocity α b ∧
        ∃ κc : ℕ → ℝ, (∀ M, 0 < κc M) ∧ (∀ M, 4 * κc (M + 1) < κc M) ∧
        ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C : ℝ,
          ∀ a : ℝ, ∀ κ ∈ ⋃ M : ℕ, Set.Icc (κc M / 2) (2 * κc M),
          ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
            (∃ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ) ∧
            ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ →
              ∃ Θ : ℝ → Vec 2 → ℝ,
                ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2)
                  (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) ∧
                ∀ t ∈ Set.Icc (a + t₀) (a + T),
                  IsZ2Periodic (Θ t) ∧
                  Θ t =ᵐ[volume.restrict unitCube] θ t ∧
                  CsNormLe s (Θ t) (C * Real.sqrt (l2NormSq f)) := by
  intro α s hα₀ hα₁ hs₀ hs₁
  obtain ⟨q, hq⟩ := exists_admissibleQ hα₀ hα₁ hs₀ hs₁
  obtain ⟨ζ, hζ⟩ := AVRegularity.exists_isFastProfile
  obtain ⟨Λ₀, hΛ₀, hForallΛ⟩ := hB α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨⟨Φ, hΦ⟩, hForallΦ⟩ := hForallΛ Λ₀ le_rfl
  obtain ⟨b, hbLimit, hbHolder, hForallTime⟩ := hForallΦ Φ hΦ
  let p : ℝ := (1 + α) - ocGamma α q
  let κc : ℕ → ℝ := fun M => ocEpsilon q Λ₀ (M + 1) ^ p
  have hp : 2 / 7 < p := by
    dsimp [p]
    exact beta_sub_gamma_gt_two_sevenths hα₀ hq
  have hp_pos : 0 < p := by linarith
  have hbands :
      (⋃ M : ℕ, Set.Icc (κc M / 2) (2 * κc M)) = ocBandSet α q Λ₀ := by
    simpa [κc] using shifted_band_eq α q Λ₀ p rfl
  refine ⟨b, hbHolder, κc, ?_, ?_, ?_⟩
  · intro M
    exact band_sequence_pos hq hΛ₀ p M
  · intro M
    simpa [κc] using band_sequence_gap hq hΛ₀ p hp M
  · intro t₀ T ht₀ ht₀T
    obtain ⟨C, hC⟩ := hForallTime t₀ T ht₀ ht₀T
    refine ⟨C, ?_⟩
    intro a κ hκ f hf
    have hκ' : κ ∈ ocBandSet α q Λ₀ := by
      rw [← hbands]
      exact hκ
    exact hC a κ hκ' f hf

end AVRegularity.Assembly
