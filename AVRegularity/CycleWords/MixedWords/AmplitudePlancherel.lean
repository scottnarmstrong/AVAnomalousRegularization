-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.Assembly.MixedWordsB1Transfer
import AVRegularity.Analysis.Convolution
public import AVRegularity.CycleWords.MixedWords.CompactDiscardOfParts
public import AVRegularity.CycleWords.MixedWords.SharpDecayLoop

@[expose] public section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Analysis
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # The moment amplitudes from the stage inequalities

`triangularGronwall_majorant_mono` at the top stage of every moment, at time `b - a`, gives
`A ≤ L^k (1 + ζ²τ)^k (D + (1+τ)^k E)`. With `ζ²τ ≤ C_z(1 + x)²` and `τ ≤ C_H S` this is
`C (1 + x)^{2M} (D + (1+S)^M E)`, which is the bound of `MomentAmplitudeStatement` with
`P = 2M`, `Q' = Q + M` (`momentAmplitude_of_wordStage`). -/

universe u v

theorem IsWordPiece.wordTheta_nonneg {K : ScalarConstants} {g₁ : ℝ} {ι : Type*} [Fintype ι]
    {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D Nw H J : ℕ}
    {π : ι → ℝ} {letters : Fin Nw → CycleLetter ι h D} {η S ηg ϖ : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2} {g : ℝ} {reg : BlockRegions}
    {a b : ℝ} (hB : IsWordPiece K g₁ H J π letters η S ηg ϖ G v g reg a b) :
    0 ≤ wordTheta ηg letters :=
  Finset.prod_nonneg fun i _ => mul_nonneg (hB.hlet i).theta_nonneg
    (by split_ifs <;> linarith [hB.hηg])

/-- The polynomial factors of `triangularGronwall_majorant_mono` at the top stage. -/
theorem stage_factors_le {L Cz x ζ τ CH S : ℝ} {k M : ℕ} (hL : 1 ≤ L)
    (hx : 0 ≤ x) (hτ : 0 ≤ τ) (hS : 0 ≤ S) (hζτ : ζ ^ 2 * τ ≤ Cz * (1 + x) ^ 2)
    (hζ2 : 0 ≤ ζ ^ 2 * τ) (hτS : τ ≤ CH * S) (hk : k ≤ M) :
    L ^ k * (1 + ζ ^ 2 * τ) ^ k ≤ L ^ M * (1 + Cz) ^ M * (1 + x) ^ (2 * M) ∧
      (1 + τ) ^ k ≤ (1 + |CH|) ^ M * (1 + S) ^ M := by
  have hx1 : 1 ≤ (1 + x) ^ 2 := one_le_pow₀ (by linarith)
  have hbase : 1 + ζ ^ 2 * τ ≤ (1 + Cz) * (1 + x) ^ 2 := by
    have : Cz * (1 + x) ^ 2 + 1 ≤ (1 + Cz) * (1 + x) ^ 2 := by nlinarith
    linarith
  have hb1 : 1 ≤ (1 + Cz) * (1 + x) ^ 2 := by nlinarith
  constructor
  · have h1 : L ^ k ≤ L ^ M := pow_le_pow_right₀ hL hk
    have h2 : (1 + ζ ^ 2 * τ) ^ k ≤ ((1 + Cz) * (1 + x) ^ 2) ^ M :=
      (pow_le_pow_left₀ (by linarith) hbase k).trans (pow_le_pow_right₀ hb1 hk)
    have h3 : ((1 + Cz) * (1 + x) ^ 2) ^ M = (1 + Cz) ^ M * (1 + x) ^ (2 * M) := by
      rw [mul_pow, ← pow_mul, mul_comm 2 M]
    calc L ^ k * (1 + ζ ^ 2 * τ) ^ k ≤ L ^ M * ((1 + Cz) * (1 + x) ^ 2) ^ M :=
          mul_le_mul h1 h2 (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)
      _ = _ := by rw [h3, mul_assoc]
  · have hτ' : 1 + τ ≤ (1 + |CH|) * (1 + S) := by
      have : CH * S ≤ |CH| * S := mul_le_mul_of_nonneg_right (le_abs_self CH) hS
      nlinarith [abs_nonneg CH]
    have hb2 : 1 ≤ (1 + |CH|) * (1 + S) := by nlinarith [abs_nonneg CH]
    calc (1 + τ) ^ k ≤ ((1 + |CH|) * (1 + S)) ^ M :=
          (pow_le_pow_left₀ (by linarith) hτ' k).trans (pow_le_pow_right₀ hb2 hk)
      _ = _ := mul_pow _ _ _

/-- The top stage, its fast seminorm and its error. -/
theorem stage_output3_real_le {A B Dd Dp Ec Λ T Λ' ζ e : ℝ} (hA : A ≤ Λ' * (Dd + T * Ec))
    (hB : B ≤ Λ' * (ζ * Dd + e * Dp + T * Ec)) (hΛ' : Λ' ≤ Λ) (hΛ1 : 1 ≤ Λ)
    (hT1 : 1 ≤ T) (hDd : 0 ≤ Dd) (hDp : 0 ≤ Dp) (hEc : 0 ≤ Ec) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (he : 0 ≤ e) (he1 : e ≤ 1) :
    A + B + Ec ≤ Λ * (3 * (Dd + Dp) + 3 * T * Ec) := by
  have h1 : ζ * Dd + e * Dp + T * Ec ≤ Dd + Dp + T * Ec := by
    have : ζ * Dd ≤ Dd := mul_le_of_le_one_left hDd hζ1
    have : e * Dp ≤ Dp := mul_le_of_le_one_left hDp he1
    linarith
  have hTE : 0 ≤ T * Ec := mul_nonneg (by linarith) hEc
  have h2 : Λ' * (Dd + T * Ec) ≤ Λ * (Dd + T * Ec) :=
    mul_le_mul_of_nonneg_right hΛ' (by positivity)
  have h3 : Λ' * (ζ * Dd + e * Dp + T * Ec) ≤ Λ * (Dd + Dp + T * Ec) :=
    mul_le_mul hΛ' h1 (by positivity) (by linarith)
  have h4 : Ec ≤ Λ * (T * Ec) := by
    have : Ec ≤ T * Ec := le_mul_of_one_le_left hEc hT1
    exact this.trans (le_mul_of_one_le_left hTE hΛ1)
  have h5 : Λ * (Dd + T * Ec) + Λ * (Dd + Dp + T * Ec) + Λ * (T * Ec) ≤
      Λ * (3 * (Dd + Dp) + 3 * T * Ec) := by
    have hΛ0 : 0 ≤ Λ := by linarith
    have : Dd + T * Ec + (Dd + Dp + T * Ec) + T * Ec ≤ 3 * (Dd + Dp) + 3 * T * Ec := by
      linarith
    calc Λ * (Dd + T * Ec) + Λ * (Dd + Dp + T * Ec) + Λ * (T * Ec)
        = Λ * (Dd + T * Ec + (Dd + Dp + T * Ec) + T * Ec) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hΛ0
  linarith

/-- The final constant comparison. -/
theorem stage_constant_le {K₀ T2 T3 err Y C : ℝ} (hK₀ : 0 ≤ K₀) (hT3 : 1 ≤ T3)
    (hY : T2 * err ≤ T3 * Y) (hY0 : 0 ≤ Y) (hC : K₀ * T3 ≤ C) :
    K₀ * (1 + T2 * err) ≤ C * (1 + Y) := by
  have h1 : K₀ * (1 + T2 * err) ≤ K₀ * (T3 * (1 + Y)) := by
    apply mul_le_mul_of_nonneg_left _ hK₀
    nlinarith
  have h2 : K₀ * (T3 * (1 + Y)) ≤ C * (1 + Y) := by
    have := mul_le_mul_of_nonneg_right hC (by linarith : (0 : ℝ) ≤ 1 + Y)
    linarith [show K₀ * (T3 * (1 + Y)) = K₀ * T3 * (1 + Y) by ring]
  linarith

/-- The `ENNReal` bookkeeping of the output. -/
theorem stage_output_ennreal_le {N X : ℝ≥0∞} {g A Ec Dd Λ T2 Cd err R : ℝ} (hg : 0 ≤ g)
    (hΛ : 0 ≤ Λ) (hT2 : 0 ≤ T2) (hCd : 0 ≤ Cd) (herr : 0 ≤ err) (hDd : 0 ≤ Dd) (hEc0 : 0 ≤ Ec)
    (hN : N ≤ ENNReal.ofReal (g * (A + Ec))) (hAE : A + Ec ≤ Λ * (Dd + T2 * Ec))
    (hD : ENNReal.ofReal Dd ≤ ENNReal.ofReal Cd * X)
    (hE : ENNReal.ofReal Ec ≤ ENNReal.ofReal (Cd * err) * X)
    (hR : g * Λ * (Cd * (1 + T2 * err)) ≤ R) :
    N ≤ ENNReal.ofReal R * X := by
  refine hN.trans ?_
  have h1 : ENNReal.ofReal (g * (A + Ec)) ≤ ENNReal.ofReal (g * Λ) *
      (ENNReal.ofReal Dd + ENNReal.ofReal T2 * ENNReal.ofReal Ec) := by
    rw [← ENNReal.ofReal_mul hT2, ← ENNReal.ofReal_add hDd (mul_nonneg hT2 hEc0),
      ← ENNReal.ofReal_mul (mul_nonneg hg hΛ)]
    apply ENNReal.ofReal_le_ofReal
    have := mul_le_mul_of_nonneg_left hAE hg
    linarith [show g * (Λ * (Dd + T2 * Ec)) = g * Λ * (Dd + T2 * Ec) by ring]
  refine h1.trans ?_
  have h2 : ENNReal.ofReal Dd + ENNReal.ofReal T2 * ENNReal.ofReal Ec ≤
      ENNReal.ofReal (Cd * (1 + T2 * err)) * X := by
    calc ENNReal.ofReal Dd + ENNReal.ofReal T2 * ENNReal.ofReal Ec
        ≤ ENNReal.ofReal Cd * X + ENNReal.ofReal T2 * (ENNReal.ofReal (Cd * err) * X) :=
          add_le_add hD (mul_le_mul' le_rfl hE)
      _ = (ENNReal.ofReal Cd + ENNReal.ofReal T2 * ENNReal.ofReal (Cd * err)) * X := by ring
      _ = ENNReal.ofReal (Cd * (1 + T2 * err)) * X := by
          rw [← ENNReal.ofReal_mul hT2, ← ENNReal.ofReal_add hCd (by positivity)]
          congr 2
          ring
  calc ENNReal.ofReal (g * Λ) * (ENNReal.ofReal Dd + ENNReal.ofReal T2 * ENNReal.ofReal Ec)
      ≤ ENNReal.ofReal (g * Λ) * (ENNReal.ofReal (Cd * (1 + T2 * err)) * X) :=
        mul_le_mul' le_rfl h2
    _ = ENNReal.ofReal (g * Λ * (Cd * (1 + T2 * err))) * X := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg hg hΛ)]
    _ ≤ ENNReal.ofReal R * X := mul_le_mul' (ENNReal.ofReal_le_ofReal hR) le_rfl

/-- Moving the polynomial duration factor into the error exponent. -/
theorem err_shift_le {Pe S Z CH c : ℝ} {Q M : ℕ} (hPe : 1 ≤ Pe) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (hc0 : 0 ≤ c) :
    c * ((1 + |CH|) ^ M * (1 + S) ^ M) * (Pe ^ Q * (1 + S) ^ Q * Z) ≤
      c * (1 + |CH|) ^ M * (Pe ^ (Q + M) * (1 + S) ^ (Q + M) * Z) := by
  have hp : Pe ^ Q ≤ Pe ^ (Q + M) := pow_le_pow_right₀ hPe (by omega)
  have hq : 0 ≤ (1 + S) ^ (Q + M) * Z := mul_nonneg (pow_nonneg (by linarith) _) hZ
  have hc : 0 ≤ c * (1 + |CH|) ^ M := by positivity
  calc c * ((1 + |CH|) ^ M * (1 + S) ^ M) * (Pe ^ Q * (1 + S) ^ Q * Z)
      = c * (1 + |CH|) ^ M * (Pe ^ Q * ((1 + S) ^ (Q + M) * Z)) := by rw [pow_add]; ring
    _ ≤ c * (1 + |CH|) ^ M * (Pe ^ (Q + M) * ((1 + S) ^ (Q + M) * Z)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp hq) hc
    _ = _ := by ring

/-- **`MomentAmplitudeStatement` from the stage inequalities `WordStageStatement`.** -/
theorem momentAmplitude_of_wordStage (hW : WordStageStatement.{u, v}) :
    MomentAmplitudeStatement.{u, v} := by
  intro K
  obtain ⟨g₁, hg₁, hWK⟩ := hW K
  refine ⟨g₁, hg₁, ?_⟩
  intro Nw D H m d Ks pos
  obtain ⟨M, out, Q, hout, hWo⟩ := hWK Nw D H m d Ks pos
  refine ⟨2 * M, Q + M, ?_⟩
  intro CH ρ hρ hρlo
  obtain ⟨Cz, Cd, Cout, Θ, c, cE, hCz, hCd, hCout, hΘ, hc, hcE, hWc⟩ := hWo CH ρ hρ hρlo
  have hL1 : 1 ≤ 1 + Θ * M * (2 + 2 / c) := by
    have : 0 ≤ Θ * M * (2 + 2 / c) := by positivity
    linarith
  set L : ℝ := 1 + Θ * M * (2 + 2 / c) with hLdef
  set K₀ : ℝ := Cout * L ^ M * (1 + Cz) ^ M * (6 * Cd) with hK₀def
  have hK₀ : 0 ≤ K₀ := by
    have : 0 ≤ L ^ M := pow_nonneg (by linarith) _
    positivity
  refine ⟨max 1 (K₀ * (3 * (1 + |CH|) ^ M)), cE, lt_of_lt_of_le one_pos (le_max_left _ _), hcE,
    ?_⟩
  intro ι _ h _ _ _ _ _ _ J π letters hletters η S ηg t₀ Sw ϖ a b Dq G v g reg pkg hB ht₀a hab
    hbS hCH hDq hq hJ X₀ κ hκ f u w hf hch θ hθ β hβ
  obtain ⟨A, Bf, Dd, Dp, Ec, ζ, hζ0, hζ1, hζτ, hDdm, hDpm, hEcm, hDd0, hDp0, hζDp, hEc0,
    hAin, hBin, hout'⟩ := hWc J π letters hletters η S ηg t₀ Sw ϖ a b Dq G v g reg pkg hB ht₀a hab
      hbS hCH hDq hq hJ X₀ κ hκ f u w hf hch θ hθ
  obtain ⟨hD, hDp', hE, hN⟩ := hout' β hβ
  have hkM : out β < M := hout β hβ
  have hτ : (0 : ℝ) ≤ b - a := sub_nonneg.2 hab
  have hGG := triangularGronwall_majorant_mono Dd Dp Ec hc hζ0 hζ1 hΘ hDdm hDpm hEcm hDd0 hDp0
    hζDp hEc0 A Bf hAin hBin (out β) hkM (b - a) ⟨hτ, le_rfl⟩
  have hG := hGG.1
  have hϖ0 : 0 ≤ ϖ := by rw [hB.hϖ]; exact Real.sqrt_nonneg _
  have hx : 0 ≤ Real.sqrt (vecDot θ θ) / ϖ := div_nonneg (Real.sqrt_nonneg _) hϖ0
  have hS0 : 0 ≤ S := zero_le_one.trans hB.hS
  obtain ⟨hf1, hf2⟩ := stage_factors_le (k := out β) (M := M) hL1 hx hτ hS0 hζτ
    (mul_nonneg (sq_nonneg ζ) hτ) hCH hkM.le
  set T : ℝ := (1 + |CH|) ^ M * (1 + S) ^ M with hTdef
  have hT1 : 1 ≤ T := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [abs_nonneg CH]))
    (one_le_pow₀ (by linarith))
  set Λ : ℝ := L ^ M * (1 + Cz) ^ M * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ (2 * M) with hΛdef
  have hΛ1 : 1 ≤ Λ := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ hL1) (one_le_pow₀ (by linarith))) (one_le_pow₀ (by linarith))
  have hΛ'0 : 0 ≤ L ^ out β * (1 + ζ ^ 2 * (b - a)) ^ out β :=
    mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by nlinarith [sq_nonneg ζ]) _)
  have hA' : A (out β) (b - a) ≤ L ^ out β * (1 + ζ ^ 2 * (b - a)) ^ out β *
      (Dd (out β) + T * Ec (out β)) := by
    refine hG.trans (mul_le_mul_of_nonneg_left ?_ hΛ'0)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hf2 (hEc0 (out β)))
  have hB' : Bf (out β) (b - a) ≤ L ^ out β * (1 + ζ ^ 2 * (b - a)) ^ out β *
      (ζ * Dd (out β) + Real.exp (-(c / 2) * (b - a)) * Dp (out β) + T * Ec (out β)) := by
    refine hGG.2.trans (mul_le_mul_of_nonneg_left ?_ hΛ'0)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hf2 (hEc0 (out β)))
  have hexp1 : Real.exp (-(c / 2) * (b - a)) ≤ 1 :=
    Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (by linarith [hc]) hτ)
  have hAE := stage_output3_real_le hA' hB' hf1 hΛ1 hT1 (hDd0 _) (hDp0 _) (hEc0 _) hζ0 hζ1
    (Real.exp_pos _).le hexp1
  set err : ℝ := peFactor η ^ Q * (1 + S) ^ Q * ((1 + (reg.joins : ℝ)) *
    Real.exp (-cE * reg.buffer) + Real.exp (-cE * Dq)) with herrdef
  have hstuff : 0 ≤ (1 + (reg.joins : ℝ)) * Real.exp (-cE * reg.buffer) + Real.exp (-cE * Dq) := by
    positivity
  have hPe : 1 ≤ peFactor η := AVRegularity.CycleWords.Assembly.one_le_peFactor η
  have herr0 : 0 ≤ err := by
    have : 0 ≤ peFactor η ^ Q := pow_nonneg (by linarith) _
    positivity
  have hE' : ENNReal.ofReal (Ec (out β)) ≤ ENNReal.ofReal (6 * Cd * err) *
      datumJets π ϖ (β.1 + β.2 + ∑ i, Ks i) (fun x => planeValue (f x)) θ := by
    refine hE.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    have h0 : 0 ≤ Cd * err := mul_nonneg hCd herr0
    calc Cd * peFactor η ^ Q * (1 + S) ^ Q * ((1 + (reg.joins : ℝ)) *
          Real.exp (-cE * reg.buffer) + Real.exp (-cE * Dq)) = Cd * err := by
          rw [herrdef]; ring
      _ ≤ 6 * Cd * err := by linarith only [h0]
  have hD3 : ENNReal.ofReal (3 * (Dd (out β) + Dp (out β))) ≤ ENNReal.ofReal (6 * Cd) *
      datumJets π ϖ (β.1 + β.2 + ∑ i, Ks i) (fun x => planeValue (f x)) θ := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (hDd0 _) (hDp0 _),
      show 6 * Cd = 3 * (Cd + Cd) by ring, ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_add hCd hCd, mul_assoc, add_mul]
    exact mul_le_mul' le_rfl (add_le_add hD hDp')
  set Y : ℝ := peFactor η ^ (Q + M) * (1 + S) ^ (Q + M) * ((1 + (reg.joins : ℝ)) *
    Real.exp (-cE * reg.buffer) + Real.exp (-cE * Dq)) with hYdef
  have hY0 : 0 ≤ Y := by
    have : 0 ≤ peFactor η ^ (Q + M) := pow_nonneg (by linarith) _
    positivity
  have hTY : 3 * T * err ≤ (3 * (1 + |CH|) ^ M) * Y := by
    rw [hTdef, herrdef, hYdef]
    exact err_shift_le hPe hS0 hstuff (by norm_num)
  have hT3 : 1 ≤ 3 * (1 + |CH|) ^ M := by
    have h1 : (1 : ℝ) ≤ 1 + |CH| := le_add_of_nonneg_right (abs_nonneg CH)
    have := one_le_pow₀ (n := M) h1
    linarith only [this]
  have hconst := stage_constant_le hK₀ hT3 hTY hY0 (le_max_right 1 (K₀ * (3 * (1 + |CH|) ^ M)))
  have hΘw := hB.wordTheta_nonneg
  have he := Real.exp_pos (blockGauge pkg.actual.lam η a b θ).re
  have hgoal := stage_output_ennreal_le (N := momentAmpNorm π ϖ β
      (fun x => planeValue (u (Fin.last Nw) x b)) θ)
    (g := Real.exp (blockGauge pkg.actual.lam η a b θ).re * Cout * wordTheta ηg letters)
    (by positivity) (by linarith) (by positivity) (by positivity) herr0
    (by have := hDd0 (out β); have := hDp0 (out β); positivity) (hEc0 _) hN hAE hD3 hE'
    (R := Real.exp (blockGauge pkg.actual.lam η a b θ).re *
      (max 1 (K₀ * (3 * (1 + |CH|) ^ M)) * wordTheta ηg letters *
        (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ (2 * M) * (1 + Y))) (by
      have hx2 : 0 ≤ (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ (2 * M) := pow_nonneg (by linarith) _
      have hfac : 0 ≤ Real.exp (blockGauge pkg.actual.lam η a b θ).re * wordTheta ηg letters *
          (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ (2 * M) := by positivity
      have := mul_le_mul_of_nonneg_left hconst hfac
      calc Real.exp (blockGauge pkg.actual.lam η a b θ).re * Cout * wordTheta ηg letters * Λ *
            (6 * Cd * (1 + 3 * T * err))
          = Real.exp (blockGauge pkg.actual.lam η a b θ).re * wordTheta ηg letters *
              (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ (2 * M) * (K₀ * (1 + 3 * T * err)) := by
            rw [hΛdef, hK₀def]; ring
        _ ≤ _ := this
        _ = _ := by ring)
  exact hgoal

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped ENNReal RealInnerProductSpace
namespace AVRegularity.CycleWords.Assembly

/-! # Band-limited calculus and Plancherel

Smoothness and the derivative bound are `ampFun_contDiff` and `norm_orderedDerivative_ampFun_le`.
For an even/odd amplitude pair the band-limited function is `∫ e^{iθ·z} (a - i b)(θ) dθ`
coordinatewise (the cross terms are odd), so the scalar Plancherel identity
(`eLpNorm_sq_scalarAmp`) gives `‖g‖₂² = (2π)² (‖A‖₂² + ‖B‖₂²)` in `[0, ∞]`, summing over an
orthonormal basis of the fibre (`eLpNorm_ampFun_sq`). Both sides are finite together, which is the
equivalence of square integrability (`amplitudePlancherel`). -/

universe u v

section Squares

theorem enorm_sq_eq_ofReal {F : Type*} [NormedAddCommGroup F] (x : F) :
    ‖x‖ₑ ^ 2 = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- The squared `L²` norm as a lower integral. -/
theorem eLpNorm_two_sq {X F : Type*} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup F]
    {f : X → F} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hf,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  simp only [ENNReal.toReal_ofNat, Nat.cast_ofNat, ENNReal.rpow_two]
  norm_num

/-- Squares of `L²` norms add over orthonormal coordinates. -/
theorem eLpNorm_two_sq_coord {X F ι : Type*} [MeasurableSpace X] {μ : Measure X} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (b : OrthonormalBasis ι ℝ F) {f : X → F}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∑ i, eLpNorm (fun x => ⟪b i, f x⟫) 2 μ ^ 2 := by
  have hfi : ∀ i, AEStronglyMeasurable (fun x => ⟪b i, f x⟫) μ := fun i =>
    aestronglyMeasurable_const.inner hf
  rw [eLpNorm_two_sq hf]
  simp_rw [eLpNorm_two_sq (hfi _)]
  rw [← lintegral_finsetSum' _ fun i _ => (hfi i).enorm.pow_const 2]
  refine lintegral_congr fun x => ?_
  have h : ‖f x‖ ^ 2 = ∑ i, ⟪b i, f x⟫ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner (f x) (f x)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm, sq]
  rw [enorm_sq_eq_ofReal, h, ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [enorm_sq_eq_ofReal, Real.norm_eq_abs, sq_abs]

theorem sq_rpow_half (a : ℝ≥0∞) : (a ^ 2) ^ (1 / 2 : ℝ) = a := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

end Squares

section Scalar

private theorem vecDot_neg_left (θ z : Vec 2) : vecDot (-θ) z = -vecDot θ z := by
  simp only [vecDot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem integrable_cos_mul {a : Vec 2 → ℝ} (ha : Integrable a) (z : Vec 2) :
    Integrable (fun θ => Real.cos (vecDot θ z) * a θ) := by
  have hc : Continuous fun θ : Vec 2 => vecDot θ z := by unfold vecDot; fun_prop
  refine Integrable.mono' ha.norm
    ((Real.continuous_cos.comp hc).aestronglyMeasurable.mul ha.aestronglyMeasurable)
    (Eventually.of_forall fun θ => ?_)
  rw [norm_mul, Real.norm_eq_abs (Real.cos _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)

theorem integrable_sin_mul {a : Vec 2 → ℝ} (ha : Integrable a) (z : Vec 2) :
    Integrable (fun θ => Real.sin (vecDot θ z) * a θ) := by
  have hc : Continuous fun θ : Vec 2 => vecDot θ z := by unfold vecDot; fun_prop
  refine Integrable.mono' ha.norm
    ((Real.continuous_sin.comp hc).aestronglyMeasurable.mul ha.aestronglyMeasurable)
    (Eventually.of_forall fun θ => ?_)
  rw [norm_mul, Real.norm_eq_abs (Real.sin _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _)

/-- For an even `a` and an odd `b`, the cosine/sine integral is the exponential transform of
`a - i b`. -/
theorem expTransform_amp {a b : Vec 2 → ℝ} (ha : Integrable a) (hb : Integrable b)
    (hae : ∀ θ, a (-θ) = a θ) (hbo : ∀ θ, b (-θ) = -b θ) (z : Vec 2) :
    expTransform (fun θ => (a θ : ℂ) - (b θ : ℂ) * Complex.I) z =
      ((∫ θ, (Real.cos (vecDot θ z) * a θ + Real.sin (vecDot θ z) * b θ) : ℝ) : ℂ) := by
  set f : Vec 2 → ℝ := fun θ => Real.cos (vecDot θ z) * a θ + Real.sin (vecDot θ z) * b θ
    with hf
  set k : Vec 2 → ℝ := fun θ => Real.sin (vecDot θ z) * a θ - Real.cos (vecDot θ z) * b θ
    with hk
  have hpt : ∀ θ, Complex.exp (↑(vecDot θ z) * Complex.I) * ((a θ : ℂ) - (b θ : ℂ) * Complex.I) =
      (f θ : ℂ) + (k θ : ℂ) * Complex.I := by
    intro θ
    apply Complex.ext
    · simp [hf, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
        Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    · simp [hk, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
        Complex.cos_ofReal_re, Complex.sin_ofReal_re]
      ring
  have hfi : Integrable f := (integrable_cos_mul ha z).add (integrable_sin_mul hb z)
  have hki : Integrable k := (integrable_sin_mul ha z).sub (integrable_cos_mul hb z)
  have hk0 : ∫ θ, k θ = 0 := by
    have hodd : ∀ θ, k (-θ) = -k θ := by
      intro θ
      simp only [hk, vecDot_neg_left, Real.sin_neg, Real.cos_neg, hae, hbo]
      ring
    have h := integral_neg_eq_self k volume
    simp_rw [hodd, integral_neg] at h
    linarith
  unfold expTransform
  simp_rw [hpt]
  rw [integral_add hfi.ofReal (hki.ofReal.mul_const _), integral_mul_const,
    integral_complex_ofReal, integral_complex_ofReal, hk0, Complex.ofReal_zero, zero_mul,
    add_zero]

/-- **Scalar Plancherel** for an even/odd amplitude pair. -/
theorem eLpNorm_sq_scalarAmp {a b : Vec 2 → ℝ} (ha : Integrable a) (hb : Integrable b)
    (hae : ∀ θ, a (-θ) = a θ) (hbo : ∀ θ, b (-θ) = -b θ) :
    eLpNorm (fun z => ∫ θ, (Real.cos (vecDot θ z) * a θ + Real.sin (vecDot θ z) * b θ)) 2
        volume ^ 2 =
      ENNReal.ofReal (2 * Real.pi) ^ 2 * (eLpNorm a 2 volume ^ 2 + eLpNorm b 2 volume ^ 2) := by
  set c : Vec 2 → ℂ := fun θ => (a θ : ℂ) - (b θ : ℂ) * Complex.I with hc
  have hci : Integrable c := ha.ofReal.sub (hb.ofReal.mul_const _)
  have hE := expTransform_amp ha hb hae hbo
  have hcont := expTransform_continuous hci
  have hsg : (fun z => ∫ θ, (Real.cos (vecDot θ z) * a θ + Real.sin (vecDot θ z) * b θ)) =
      fun z => (expTransform c z).re := funext fun z => by rw [hE z, Complex.ofReal_re]
  have hsgc : Continuous
      (fun z => ∫ θ, (Real.cos (vecDot θ z) * a θ + Real.sin (vecDot θ z) * b θ)) := by
    rw [hsg]
    exact Complex.continuous_re.comp hcont
  have e1 : eLpNorm (fun z => ∫ θ, (Real.cos (vecDot θ z) * a θ +
      Real.sin (vecDot θ z) * b θ)) 2 volume = eLpNorm (expTransform c) 2 volume :=
    eLpNorm_congr_norm_ae hsgc.aestronglyMeasurable hcont.aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [hE z, Complex.norm_real])
  have e2 : eLpNorm c 2 volume ^ 2 = eLpNorm a 2 volume ^ 2 + eLpNorm b 2 volume ^ 2 := by
    rw [eLpNorm_two_sq hci.aestronglyMeasurable, eLpNorm_two_sq ha.aestronglyMeasurable,
      eLpNorm_two_sq hb.aestronglyMeasurable,
      ← lintegral_add_left' (ha.aestronglyMeasurable.enorm.pow_const 2)]
    refine lintegral_congr fun θ => ?_
    rw [enorm_sq_eq_ofReal, enorm_sq_eq_ofReal, enorm_sq_eq_ofReal,
      ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    congr 1
    rw [Complex.sq_norm, Complex.normSq_apply, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    simp [hc]
    ring
  rw [e1, eLpNorm_expTransform hci, mul_pow, e2]

end Scalar

section Vector

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem integrable_of_amplitude {r : ℝ} {A : Vec 2 → E}
    (hzero : ∀ θ : Vec 2, r ^ 2 < vecDot θ θ → A θ = 0)
    (hA : IntegrableOn A {θ : Vec 2 | vecDot θ θ ≤ r ^ 2}) : Integrable A := by
  refine (integrableOn_iff_integrable_of_support_subset fun θ hθ => ?_).1 hA
  by_contra hθs
  exact hθ (hzero θ (lt_of_not_ge hθs))

omit [FiniteDimensional ℝ E] in
theorem ampFun_eq_integral {r : ℝ} {A B : Vec 2 → E}
    (hzero : ∀ θ : Vec 2, r ^ 2 < vecDot θ θ → A θ = 0 ∧ B θ = 0) (z : Vec 2) :
    ampFun r A B z = ∫ θ, (Real.cos (vecDot θ z) • A θ + Real.sin (vecDot θ z) • B θ) := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun θ hθ => ?_
  obtain ⟨hA0, hB0⟩ := hzero θ (lt_of_not_ge hθ)
  rw [hA0, hB0, smul_zero, smul_zero, add_zero]

omit [FiniteDimensional ℝ E] in
theorem integrable_ampIntegrand {A B : Vec 2 → E} (hA : Integrable A) (hB : Integrable B)
    (z : Vec 2) :
    Integrable fun θ => Real.cos (vecDot θ z) • A θ + Real.sin (vecDot θ z) • B θ := by
  have hc : Continuous fun θ : Vec 2 => vecDot θ z := by unfold vecDot; fun_prop
  refine Integrable.mono' (hA.norm.add hB.norm)
    (((Real.continuous_cos.comp hc).aestronglyMeasurable.smul hA.aestronglyMeasurable).add
      ((Real.continuous_sin.comp hc).aestronglyMeasurable.smul hB.aestronglyMeasurable))
    (Eventually.of_forall fun θ => ?_)
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _)

variable [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
theorem inner_ampFun {r : ℝ} {A B : Vec 2 → E}
    (hzero : ∀ θ : Vec 2, r ^ 2 < vecDot θ θ → A θ = 0 ∧ B θ = 0)
    (hA : Integrable A) (hB : Integrable B) (e : E) (z : Vec 2) :
    ⟪e, ampFun r A B z⟫ =
      ∫ θ, (Real.cos (vecDot θ z) * ⟪e, A θ⟫ + Real.sin (vecDot θ z) * ⟪e, B θ⟫) := by
  rw [ampFun_eq_integral hzero, ← integral_inner (integrable_ampIntegrand hA hB z) e]
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  simp only [inner_add_right, real_inner_smul_right]

/-- **Plancherel for band-limited functions**: `‖g‖₂² = (2π)² (‖A‖₂² + ‖B‖₂²)` in `[0, ∞]`. -/
theorem eLpNorm_ampFun_sq {r : ℝ} (hr : 0 ≤ r) {A B : Vec 2 → E}
    (hzero : ∀ θ : Vec 2, r ^ 2 < vecDot θ θ → A θ = 0 ∧ B θ = 0)
    (hA : IntegrableOn A {θ : Vec 2 | vecDot θ θ ≤ r ^ 2})
    (hB : IntegrableOn B {θ : Vec 2 | vecDot θ θ ≤ r ^ 2})
    (hpar : ∀ θ, A (-θ) = A θ ∧ B (-θ) = -B θ) :
    eLpNorm (ampFun r A B) 2 volume ^ 2 =
      ENNReal.ofReal (2 * Real.pi) ^ 2 * (eLpNorm A 2 volume ^ 2 + eLpNorm B 2 volume ^ 2) := by
  let bas := stdOrthonormalBasis ℝ E
  have hAi := integrable_of_amplitude (fun θ h => (hzero θ h).1) hA
  have hBi := integrable_of_amplitude (fun θ h => (hzero θ h).2) hB
  have hg := (ampFun_contDiff hr 0 hA hB).continuous
  rw [eLpNorm_two_sq_coord bas hg.aestronglyMeasurable,
    eLpNorm_two_sq_coord bas hAi.aestronglyMeasurable,
    eLpNorm_two_sq_coord bas hBi.aestronglyMeasurable, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (fun z => ⟪bas i, ampFun r A B z⟫) = fun z => ∫ θ, (Real.cos (vecDot θ z) *
      ⟪bas i, A θ⟫ + Real.sin (vecDot θ z) * ⟪bas i, B θ⟫) from
    funext (inner_ampFun hzero hAi hBi (bas i))]
  exact eLpNorm_sq_scalarAmp (hAi.const_inner _) (hBi.const_inner _)
    (fun θ => by rw [(hpar θ).1]) (fun θ => by rw [(hpar θ).2, inner_neg_right])

end Vector

/-- **Band-limited calculus and Plancherel** (`AmplitudePlancherelStatement`). -/
theorem amplitudePlancherel : AmplitudePlancherelStatement.{v} := by
  intro E _ _ _ _ _ _ r g A B hr hg
  obtain ⟨hzero, hA, hB, hgz⟩ := hg
  obtain rfl : g = ampFun r A B := funext hgz
  refine ⟨fun M => ampFun_contDiff hr.le M hA hB,
    fun a wd z => norm_orderedDerivative_ampFun_le hr.le hA hB wd z, fun hpar => ?_⟩
  have hsq := eLpNorm_ampFun_sq hr.le hzero hA hB hpar
  have hK0 : ENNReal.ofReal (2 * Real.pi) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hKt : ENNReal.ofReal (2 * Real.pi) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hsqlt : ∀ x : ℝ≥0∞, x < ⊤ ↔ x ^ 2 < ⊤ := fun x =>
    ⟨fun h => ENNReal.pow_lt_top h, fun h => ENNReal.pow_lt_top_iff.1 h |>.resolve_right
      two_ne_zero⟩
  refine ⟨?_, fun _ => ?_⟩
  · rw [memLp_iff, memLp_iff, memLp_iff, hsqlt, hsq, hsqlt (eLpNorm A 2 volume),
      hsqlt (eLpNorm B 2 volume), ← ENNReal.add_lt_top]
    constructor
    · intro h
      by_contra hX
      rw [not_lt_top_iff.1 hX, ENNReal.mul_top hK0] at h
      exact lt_irrefl _ h
    · exact fun h => ENNReal.mul_lt_top hKt.lt_top h
  · rw [← sq_rpow_half (eLpNorm (ampFun r A B) 2 volume), hsq,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), sq_rpow_half]

end AVRegularity.CycleWords.Assembly
end
