-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.Recon.Coarse
import AVRegularity.Applications.Global.CompactRangeMain
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-! # A lift setting is monotone in its orders

`K, k, L` enter `IsLiftSetting` only through the smoothness floors `qs, qf`; every field that
mentions `qs` or `qf` is a regularity or jet bound that weakens when the floors decrease. -/

/-- **Monotonicity of lift settings.** -/
theorem liftSettingMono : LiftSettingMonoStatement := by
  intro ι _ h _ _ D Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ hs
    K' k' L' hK hk hL
  have hqs : K' + 4 * (H + 1) * (N + D) ^ 2 ≤ qs := by
    rw [hs.qs_eq]; exact Nat.add_le_add_right hK _
  have hqf : max k' (L' + 2) + H * D + 2 * N + 2 * D ≤ qf := by
    rw [hs.qf_eq]
    have : max k' (L' + 2) ≤ max k (L + 2) := max_le_max hk (by omega)
    omega
  have cd : ∀ {m n : ℕ} {f : Vec 2 → ℝ}, m ≤ n → ContDiff ℝ (n : ℕ∞) f → ContDiff ℝ (m : ℕ∞) f :=
    fun hmn hf => hf.of_le (by exact_mod_cast hmn)
  exact
    { window := hs.window, e_pos := hs.e_pos, ν_pos := hs.ν_pos, B_pos := hs.B_pos
      ρ_pos := hs.ρ_pos, E_pos := hs.E_pos, ℓ_eq := hs.ℓ_eq, η_eq := hs.η_eq, η_le := hs.η_le
      dstar_eq := hs.dstar_eq, εc_eq := hs.εc_eq, εc_le := hs.εc_le, lam_eq := hs.lam_eq
      lam_le := hs.lam_le, N_ge := hs.N_ge, D_ge := hs.D_ge, qs_eq := rfl, qf_eq := rfl
      mass_pos := hs.mass_pos, G_symm := hs.G_symm, G_meas := hs.G_meas
      G_smooth := fun t ht i j => cd hqs (hs.G_smooth t ht i j)
      G_ellip := hs.G_ellip
      G_jets := fun r hr => hs.G_jets r (hr.trans hqs)
      v_shear := hs.v_shear
      V_smooth := fun t ht => (hs.V_smooth t ht).of_le (by exact_mod_cast hqf)
      V_per := hs.V_per, V_mean := hs.V_mean, v_meas := hs.v_meas
      w_jets := fun q hq => hs.w_jets q (hq.trans hqf)
      depth := hs.depth, transverse := hs.transverse, coeff_meas := hs.coeff_meas
      coeff_smooth := fun v u d γ hγ α t ht =>
        (hs.coeff_smooth v u d γ hγ α t ht).mono hqs hqf
      envelope :=
        { nonneg := hs.envelope.nonneg, row_sum := hs.envelope.row_sum
          col_sum := hs.envelope.col_sum
          jets := fun v u r hr q hq => hs.envelope.jets v u r (hr.trans hqs) q (hq.trans hqf) } }

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end

section
@[expose] public section
open AVenhance AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-! **The factor of `partition_window_input` is at most `C_px 𝔅_rec`.** With the rate
`c_gap = c_gate/2` and `C_g = 1`, the pulse count times `e^{-c_gap τ/ℓ²}` is bounded by one constant
(`card_exp_le_of_scaleLaws`, the window `T_obs ≤ T₀`), and the rest of the factor,
`ℓ √(1/τ) e^{-c_gap τ/ℓ²}`, is at most `√c_gap` times the gluing term of `reconBill`
(`E^{-1} ≥ 1` since `E ≤ 1`, and `1 + T/τ ≥ 1`); the other terms of the bill are nonnegative.

Degenerate cases:
- No observed pulse: the left side is `0`.
- `S_b = 0`: the factor `(1 + S_b)^{d_W}` is `1`. -/

/-- The algebra of the comparison. -/
theorem reconPartScale_alg (Kg P ℓ τ cg Kc bill : ℝ) (hKg : 0 ≤ Kg) (hP : 0 ≤ P) (hℓ : 0 ≤ ℓ)
    (hτ : 0 < τ) (hcg : 0 < cg) (hcard : P * Real.exp (-(cg * τ / ℓ ^ 2)) ≤ Kc)
    (hbill : ℓ * Real.sqrt (1 / (cg * τ)) * Real.exp (-(cg * τ / ℓ ^ 2)) ≤ bill) :
    Kg * P * ℓ * Real.sqrt (1 / τ) * Real.exp (-(2 * cg * τ / ℓ ^ 2)) ≤
      Kg * Kc * Real.sqrt cg * bill := by
  have he : Real.exp (-(2 * cg * τ / ℓ ^ 2)) =
      Real.exp (-(cg * τ / ℓ ^ 2)) * Real.exp (-(cg * τ / ℓ ^ 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hs : Real.sqrt (1 / τ) = Real.sqrt cg * Real.sqrt (1 / (cg * τ)) := by
    rw [← Real.sqrt_mul hcg.le]; congr 1; field_simp
  have h0 : 0 ≤ Real.exp (-(cg * τ / ℓ ^ 2)) := (Real.exp_pos _).le
  have hsq : 0 ≤ Real.sqrt cg := Real.sqrt_nonneg _
  have hsq2 : 0 ≤ Real.sqrt (1 / (cg * τ)) := Real.sqrt_nonneg _
  calc Kg * P * ℓ * Real.sqrt (1 / τ) * Real.exp (-(2 * cg * τ / ℓ ^ 2))
      = Kg * Real.sqrt cg * (P * Real.exp (-(cg * τ / ℓ ^ 2))) *
          (ℓ * Real.sqrt (1 / (cg * τ)) * Real.exp (-(cg * τ / ℓ ^ 2))) := by
        rw [he, hs]; ring
    _ ≤ Kg * Real.sqrt cg * Kc * bill := by
        have hA : 0 ≤ Kg * Real.sqrt cg := mul_nonneg hKg hsq
        have hB : 0 ≤ P * Real.exp (-(cg * τ / ℓ ^ 2)) := mul_nonneg hP h0
        have hC : 0 ≤ ℓ * Real.sqrt (1 / (cg * τ)) * Real.exp (-(cg * τ / ℓ ^ 2)) :=
          mul_nonneg (mul_nonneg hℓ hsq2) h0
        exact mul_le_mul (mul_le_mul_of_nonneg_left hcard hA) hbill hC
          (mul_nonneg hA (hB.trans hcard))
    _ = _ := by ring

section Context

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- The gluing term of the bill is at most the bill (`C_g = 1`). -/
theorem reconPartScale_bill_ge
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (hk1 : 0 < c.D.κ M) (hΛ : 128 ≤ c.D.Λ)
    (hqq : 1 < c.D.q) (hdl : c.tp < c.a + A.T₀) (cgap : ℝ) (hcg : 0 < cgap) :
    ocEll c.D.q c.D.Λ M (c.D.κ M) *
        Real.sqrt (1 / (cgap * ocTau c.D.α c.D.q c.D.Λ M)) *
        Real.exp (-(cgap * ocTau c.D.α c.D.q c.D.Λ M / ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2)) ≤
      c.reconBill cgap 1 := by
  have hone := x.one
  have hε : ∀ m, 0 < ocEpsilon c.D.q c.D.Λ m := fun m => Applications.eps_pos hqq hΛ
  have hε1 : ocEpsilon c.D.q c.D.Λ (M - 1) ≤ 1 := Applications.eps_le_one hqq hΛ
  have hτ : 0 < ocTau c.D.α c.D.q c.D.Λ M := Construction.Stream.ocTau_pos (by omega)
  have hell : Real.sqrt (c.D.termEllSq M) = ocEll c.D.q c.D.Λ M (c.D.κ M) := by
    simp only [OCData.termEllSq, OCData.termNu, ocEll, OCData.eps]
    rw [Real.sqrt_div' _ hk1.le, Real.sqrt_sq (hε M).le]
  have hℓ : 0 ≤ ocEll c.D.q c.D.Λ M (c.D.κ M) := hell ▸ Real.sqrt_nonneg _
  have hT : 0 ≤ c.a + A.T₀ - c.tp := by linarith
  have hρ : 0 ≤ c.D.termRho cr M := by
    simp only [OCData.termRho]
    exact mul_nonneg (by rw [hone]; exact zero_le_one) (Real.sqrt_nonneg _)
  have hεc : 0 ≤ c.D.termEpsCell cr M := by
    simp only [OCData.termEpsCell, OCData.termDstar]
    exact div_nonneg (mul_nonneg (hε M).le (Real.sqrt_nonneg _)) hρ
  have hsqrt : 0 ≤ Real.sqrt (c.a + A.T₀ - c.tp) / Real.sqrt (c.D.termEllSq M) :=
    div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hr : 0 ≤ (c.D.eps M / c.D.termRho cr M) ^ A.AT :=
    pow_nonneg (div_nonneg (hε M).le hρ) _
  have hR : 0 ≤ 1 + Real.sqrt (c.a + A.T₀ - c.tp) / Real.sqrt (c.D.termEllSq M) *
      (c.D.eps M / c.D.termRho cr M) ^ A.AT := by
    have := mul_nonneg hsqrt hr; linarith
  have hA := mul_nonneg (pow_nonneg hεc A.NT) hR
  have hfront : 0 ≤ c.frontPrice := Real.rpow_nonneg (hε (M - 1)).le _
  have hcov : 0 ≤ c.covPrice := Real.rpow_nonneg (hε (M - 1)).le _
  have hRW : 0 ≤ c.D.termRW A.σw M := Real.rpow_nonneg (hε M).le _
  have hfilter : 0 ≤ c.filterPrice :=
    add_nonneg (Real.rpow_nonneg (hε (M - 1)).le _)
      (mul_nonneg (Real.rpow_nonneg (hε M).le _) (pow_nonneg (div_nonneg hRW hρ) _))
  have hB := mul_nonneg (add_nonneg (Real.sqrt_nonneg (c.D.termB M / c.D.termNu M))
    (mul_nonneg (sq_nonneg (c.D.termEpsCell cr M)) hR))
    (add_nonneg (add_nonneg hfront hcov) hfilter)
  have hE1 : 1 ≤ c.D.eps (M - 1) ^ (-(1 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (hε (M - 1)) hε1 (by norm_num)
  have h1 : Real.sqrt (1 / (cgap * ocTau c.D.α c.D.q c.D.Λ M)) ≤
      Real.sqrt ((1 + (c.a + A.T₀ - c.tp) / ocTau c.D.α c.D.q c.D.Λ M) /
        (cgap * ocTau c.D.α c.D.q c.D.Λ M)) := by
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_right (by have := div_nonneg hT hτ.le; linarith)
      (mul_pos hcg hτ).le
  have hex := (Real.exp_pos (-(cgap * ocTau c.D.α c.D.q c.D.Λ M /
    ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2))).le
  have hG : ocEll c.D.q c.D.Λ M (c.D.κ M) *
        Real.sqrt (1 / (cgap * ocTau c.D.α c.D.q c.D.Λ M)) *
        Real.exp (-(cgap * ocTau c.D.α c.D.q c.D.Λ M / ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2)) ≤
      1 * c.D.eps (M - 1) ^ (-(1 : ℝ)) * Real.sqrt (c.D.termEllSq M) *
        Real.sqrt ((1 + (c.a + A.T₀ - c.tp) / ocTau c.D.α c.D.q c.D.Λ M) /
          (cgap * ocTau c.D.α c.D.q c.D.Λ M)) *
        Real.exp (-(cgap * ocTau c.D.α c.D.q c.D.Λ M / Real.sqrt (c.D.termEllSq M) ^ 2)) := by
    rw [hell]
    have h2 : ocEll c.D.q c.D.Λ M (c.D.κ M) *
        Real.sqrt (1 / (cgap * ocTau c.D.α c.D.q c.D.Λ M)) *
        Real.exp (-(cgap * ocTau c.D.α c.D.q c.D.Λ M / ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2)) ≤
        ocEll c.D.q c.D.Λ M (c.D.κ M) *
        Real.sqrt ((1 + (c.a + A.T₀ - c.tp) / ocTau c.D.α c.D.q c.D.Λ M) /
          (cgap * ocTau c.D.α c.D.q c.D.Λ M)) *
        Real.exp (-(cgap * ocTau c.D.α c.D.q c.D.Λ M / ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hℓ) hex
    have h3 : 0 ≤ ocEll c.D.q c.D.Λ M (c.D.κ M) *
        Real.sqrt ((1 + (c.a + A.T₀ - c.tp) / ocTau c.D.α c.D.q c.D.Λ M) /
          (cgap * ocTau c.D.α c.D.q c.D.Λ M)) *
        Real.exp (-(cgap * ocTau c.D.α c.D.q c.D.Λ M / ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2)) :=
      mul_nonneg (mul_nonneg hℓ (Real.sqrt_nonneg _)) hex
    calc _ ≤ _ := h2
      _ = 1 * (ocEll c.D.q c.D.Λ M (c.D.κ M) *
        Real.sqrt ((1 + (c.a + A.T₀ - c.tp) / ocTau c.D.α c.D.q c.D.Λ M) /
          (cgap * ocTau c.D.α c.D.q c.D.Λ M)) *
        Real.exp (-(cgap * ocTau c.D.α c.D.q c.D.Λ M / ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2))) :=
          (one_mul _).symm
      _ ≤ c.D.eps (M - 1) ^ (-(1 : ℝ)) * (ocEll c.D.q c.D.Λ M (c.D.κ M) *
        Real.sqrt ((1 + (c.a + A.T₀ - c.tp) / ocTau c.D.α c.D.q c.D.Λ M) /
          (cgap * ocTau c.D.α c.D.q c.D.Λ M)) *
        Real.exp (-(cgap * ocTau c.D.α c.D.q c.D.Λ M / ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2))) :=
          mul_le_mul_of_nonneg_right hE1 h3
      _ = _ := by ring
  unfold TermResCtx.reconBill
  linarith [hA, hB, hG]

end Context

/-- **The factor of `partition_window_input` is at most `C_px 𝔅_rec`.** -/
theorem termReconPartition : TermReconPartitionStatement := by
  intro ℓ X
  obtain ⟨C, hC1, Λ1, hΛ1, hlaw⟩ := CycleComparison.Assembly.scale_laws X.α X.s X.hα₀ X.hα₁
    X.hs₀ X.hs₁ X.q X.hq X.ζ X.hζ
  refine ⟨Λ1, hΛ1, fun A hΛ hV => ?_⟩
  have h128 : 128 ≤ A.Λ := le_trans hΛ1 hΛ
  refine ⟨0, fun kc _ => ⟨0, 0, 0, fun sXT sZT _ _ Kout _ => ⟨0, ?_⟩⟩⟩
  intro Kw Lt nW hk₀w _ cr kS _ _ _ _ _ _ _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW hcK _ _
    cP CP cHP Cw Ce cker hcP Cgate cgate Sb hCgate hcgate hSb
  obtain ⟨Kc, hKc0, hcard⟩ := CycleComparison.Reconstruction.card_exp_le_of_scaleLaws X.α X.s
    X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.q X.hq A.Λ h128 C hC1 0 A.T₀ (cgate / 2) (half_pos hcgate)
  refine ⟨Cgate * (1 + Sb) ^ A.dW * Kc * Real.sqrt (cgate / 2), cgate / 2, 1,
    mul_nonneg (mul_nonneg (mul_nonneg hCgate (pow_nonneg (by linarith) _)) hKc0)
      (Real.sqrt_nonneg _), half_pos hcgate, zero_le_one, 1, 1, le_rfl, one_pos,
    fun j₀ _ => ⟨2, fun M hM c x => ?_⟩⟩
  intro hdl
  obtain ⟨hα, hq, hΛD, hζ, -, hchain, -⟩ := c.data
  have hΛ' : 128 ≤ c.D.Λ := hΛD ▸ h128
  have hqq : 1 < c.D.q := hq ▸ X.hq.1
  have hlaws := hlaw A.Λ hΛ M c.D.κ hchain M hM le_rfl (c.D.κ M)
    (c.D.κ (M - 1)) rfl rfl
  have hk1 : 0 < c.D.κ M := hlaws.ν_pos
  have hτ : 0 < ocTau c.D.α c.D.q c.D.Λ M := Construction.Stream.ocTau_pos (by omega)
  -- the window length
  have haM : c.a ≤ c.aM := c.weak.1
  have hprep : c.aM + cP * c.D.termH M ≤ c.tp := c.prep.2.1
  have hH : 0 < c.D.termH M := Construction.Stream.ocTauPP_pos (by omega)
  have hatp : c.a ≤ c.tp := by nlinarith
  have hTpos : 0 < rTobs c := by unfold rTobs; linarith
  have hTle : rTobs c ≤ A.T₀ * ocEpsilon X.q A.Λ (M - 1) ^ (-(0 : ℝ)) := by
    simp only [neg_zero, Real.rpow_zero, mul_one, rTobs]; linarith
  have hcard' : ((ocObsPulses c.D.α c.D.q c.D.Λ M c.tp (c.tp + rTobs c)).card : ℝ) *
      Real.exp (-(cgate / 2 * ocTau c.D.α c.D.q c.D.Λ M /
        ocEll c.D.q c.D.Λ M (c.D.κ M) ^ 2)) ≤ Kc := by
    rw [hα, hq, hΛD]
    exact hcard M (c.D.κ M) (c.D.κ (M - 1)) hlaws c.tp (rTobs c) hTpos hTle
  have hbill := reconPartScale_bill_ge c x hk1 hΛ' hqq hdl (cgate / 2) (half_pos hcgate)
  have hℓ : 0 ≤ ocEll c.D.q c.D.Λ M (c.D.κ M) :=
    div_nonneg (Applications.eps_pos hqq hΛ').le (Real.sqrt_nonneg _)
  have key := reconPartScale_alg (Cgate * (1 + Sb) ^ A.dW) _ _ _ (cgate / 2) Kc _
    (mul_nonneg hCgate (pow_nonneg (by linarith) _)) (Nat.cast_nonneg _) hℓ hτ
    (half_pos hcgate) hcard' hbill
  have h2 : 2 * (cgate / 2) = cgate := by ring
  rw [h2] at key
  calc _ = _ := by ring
    _ ≤ _ := key
    _ = _ := by ring

end AVRegularity.EntryTerminal.Ingredients.Recon
end
end
