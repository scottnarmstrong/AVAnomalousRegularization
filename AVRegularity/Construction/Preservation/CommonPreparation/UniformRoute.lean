-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.CommonPreparation.RouteAssembly
public import AVRegularity.Construction.Preservation.CommonPreparation.CtxAssembly

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! **The route part of the actual preparation context** (`RoutePieceStatement`).

`route_piece`: at fixed choices, from the copied-coefficient piece (`copyCoeffPiece`,
constant `C_plain` and level `m_c`) and the plain-frame/sampled-source piece (`source_piece`,
constant `C_s` and level `m_s`): the moment-budget parameters

  `F_m = (q, Λ, H_pr, L_pr, σ_f, θ = min(δ/4, τ_e), max C_wid 0, c_s(φ₀, Γ_k, D, L_pr) C_s, C_I,
  C_plain, √(bufferEnergyCost K_buf))`,

the defect constant `C_def = preparationMomentDefectConstant F_m` and the level
`max m_c (max m_s (max m_tower m_scalar))`. At every context of that level: the native tower of
the datum, the scalar environment of the datum (radius, old radius, delay, drift), and the route
package of the request (`request_routePkg`).

The selected depth satisfies `H_pr ≥ 1`; an empty component family and the zero datum are
allowed. -/

/-- **The route part.** -/
theorem route_piece (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ)
    (hζ : IsFastProfile ζ) : RoutePieceStatement α s q ζ := by
  intro Λg g₀ orders
  refine ((copyCoeffPiece α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λg g₀ orders).and
    (source_piece hα₀ hα₁ hs₀ hs₁ hq hζ Λg g₀ orders)).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
    sX sZ Ce kS kI CI Cw j₀ hf x hx y hy
  obtain ⟨⟨hCplain, hcopy⟩, ⟨hCs, hsrc⟩⟩ := hy
  obtain ⟨⟨-, -, -, -, hms2, hscalar, hcap, -⟩, -, -, htower⟩ := hx
  obtain ⟨hcI, -, hCI, -, hσ, -, -, hθ, -, -⟩ :=
    preparation_context_numeric_orders hα₀ hα₁ hs₀ hs₁ hq hf
  have h128 : 128 ≤ Λ := hf.hΛ
  have hΛ1 : 1 ≤ Λ := by omega
  let Fm : PreparationMomentBudgetParameters :=
    { q := q, Λ := Λ
      H := preparationDepthFunction α q Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl
        Naux Nout Kres npad σ₀ a σ
      L := Lpr, σ := kI.σf, θ := min (ocDelta α q / 4) τe, Cwid := max kI.Cwid 0
      Csample := preparationPlainSampledConstant φ₀ kI.Γk (succSchedD D₀ N p (H + 1)) Lpr * y.2.1
      CI := CI, Cplain := y.1.1
      Cbuf := Real.sqrt (Buffer.bufferEnergyCost (preparationBufferFunction α q Λ φ₀ bw Q T₀ r₀ D₀
        τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ))
      q_pos := hq.1, q_lt := hq.2.1, frequency := h128, sigma_nonneg := hσ.le
      theta_nonneg := hθ.le, width_nonneg := le_max_right _ _
      sample_nonneg := mul_nonneg (preparation_plain_sampled_constant_nonneg _ _ _ _) hCs
      ledger_nonneg := zero_le_one.trans hCI, plain_nonneg := hCplain
      buffer_nonneg := Real.sqrt_nonneg _ }
  refine ⟨(preparationMomentDefectConstant Fm,
    max y.1.2 (max y.2.2 (max x.2.2 x.1.2.2.2.2))), ?_⟩
  intro hr _ _ _ _ _ _ _ c hm
  replace hm : max y.1.2 (max y.2.2 (max x.2.2 x.1.2.2.2.2)) ≤ c.m := hm
  have hmc : y.1.2 ≤ c.m := by omega
  have hms : y.2.2 ≤ c.m := by omega
  have hmt : x.2.2 ≤ c.m := by omega
  have hmsc : x.1.2.2.2.2 ≤ c.m := by omega
  have hm2 : 2 ≤ c.m := hms2.trans hmsc
  have hmM : c.m < c.M := lt_of_le_of_lt c.hmn c.hnM
  obtain ⟨T⟩ := htower c hmt
  have hscl := hscalar c.M c.D.κ c.hband c.m hmsc hmM
  obtain ⟨-, holdpos, holdle, -⟩ := hscl.1
  obtain ⟨hdelay, hdriftAll, -⟩ := hscl.2 c.D.Φ c.hseq
  have hρ : rhoStar c.D kI.c₀ c.G.level =
      kI.c₀ * min (ocEpsilon q Λ c.m) (Real.sqrt (c.D.κ c.m / ocA α q Λ c.m)) := by
    simp only [rhoStar, OCData.eps, c.hα, c.hq, c.hΛ, c.hlevel]
  have hτ : 0 < ocTauPP α q Λ c.m := Stream.ocTauPP_pos hΛ1
  have hcb : c.request.bufferEnd ≤ c.request.tf := by
    change c.s₀ + rhoStar c.D kI.c₀ c.G.level ^ 2 / c.D.κ c.G.level ≤ c.tf
    rw [hρ, c.hlevel]
    have := c.htf
    linarith
  have hD : 2 ≤ succSchedD D₀ N p (H + 1) := by
    change 2 ≤ succSchedD D₀ N p H + 2 * N + 4 * p + 4
    omega
  have hseq : IsOCStreamSeq c.D.α c.D.q c.D.Λ c.D.ζ c.D.Φ := by
    rw [c.hα, c.hq, c.hΛ, c.hζ]
    exact c.hseq
  have hqD : IsAdmissibleQ c.D.α s c.D.q := by
    rw [c.hα, c.hq]
    exact hq
  have hlev : 1 ≤ c.request.G.level := by
    rw [c.request_level]
    omega
  have hκ : 0 < c.D.κ c.request.G.level := by
    rw [c.request_level]
    exact c.kappa_pos hΛ1 hζ
  have hρ' : rhoStar c.D c.request.c₀ c.request.G.level =
      kI.c₀ * min (ocEpsilon q Λ c.m) (Real.sqrt (c.D.κ c.m / ocA α q Λ c.m)) := hρ
  have hρpos : 0 < rhoStar c.D c.request.c₀ c.request.G.level := by
    rw [hρ']
    exact holdpos.trans_le holdle
  have hdrift : Providers.WeakGen.Comparison.TorusDriftData (c.D.κ c.request.G.level)
      (rhoStar c.D c.request.c₀ c.request.G.level) c.request.bufferEnd c.request.tf
      (streamVel (c.D.Φ c.request.G.level))
      (preparationPlainBaseOrder (succSchedD D₀ N p (H + 1)) Nout Lpr +
        c.request.Hpr * (succSchedD D₀ N p (H + 1) - 2)) := by
    rw [hρ', c.request_level]
    exact hdriftAll _ _ _
  have hold1 : x.1.2.2.1 * ocEpsilon q Λ c.m ^ (1 + ocGamma α q / 2 + ocDelta α q) ≤
      rhoStar c.D c.request.c₀ c.request.G.level := by
    rw [hρ']
    exact holdle
  have hαD0 : 0 < c.D.α := by rw [c.hα]; exact hα₀
  have hαD1 : c.D.α < 1 / 3 := by rw [c.hα]; exact hα₁
  have hsD1 : s < (1 - c.D.α) / 2 := by rw [c.hα]; exact hs₁
  have hζD : IsFastProfile c.D.ζ := by rw [c.hζ]; exact hζ
  exact request_routePkg c.request hD (Kbase := preparationPlainBaseOrder
      (succSchedD D₀ N p (H + 1)) Nout Lpr) T s hαD0 hαD1 hs₀ hsD1 hqD
    hζD (c.lambda_ge h128) hseq hlev hcI hcap hcb hκ hρpos hdrift holdpos.le hold1
    (mul_nonneg hCplain (mul_nonneg (zero_le_one.trans hCI)
      (Real.rpow_nonneg (Stream.ocEpsilon_pos hΛ1).le _)))
    (hcopy c hmc) (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg
      (Stream.ocEpsilon_pos hΛ1).le _)) hCs
    (mul_nonneg (zero_le_one.trans hCI) (Real.rpow_nonneg (Stream.ocEpsilon_pos hΛ1).le _))
    (fun hac => hsrc c hms T hac hcb) Fm c.hq.symm c.hΛ.symm rfl rfl rfl le_rfl
    (by rw [c.request_level]) (by rw [c.request_level]) le_rfl

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance AVRegularity
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! **The actual preparation context** (the actual-context callback
`UniformActualPreparationContextStatement`, in the form with a frequency floor `Λ_c` with the callback at every `Λ_g ≥ Λ_c`).

`uniformActualPreparationContext`: the route part (`route_piece`) and the model piece
(`preparation_model_piece`) joined by `actualContext_of_pieces`. This is the exact
hypothesis `hctx` of `preparation_uniform_route_of_actual_context`.

The degenerate cases (an empty component family, the zero datum) are as in the two pieces
combined here. -/

/-- **The actual preparation context**, above a frequency floor `Λ_c`. -/
theorem uniformActualPreparationContext (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ)
    (hζ : IsFastProfile ζ) :
    ∃ Λc : ℕ, 128 ≤ Λc ∧ ∀ (Λg : ℕ) (g₀ : ℕ → ℝ)
      (orders : PreparationEarlyOrderRequest → PreparationGateNumericOrders)
      (horders : ∀ E : PreparationEarlyOrderRequest, Λg ≤ E.Λ → 0 < E.Q →
        PreparationGateAfterOrders α q ζ E.Λ (g₀ E.Λ) E.Q E.Nout
          (E.depth α q) E.dimension (E.buffer α q)
          (orders E).Ks (orders E).Ls (orders E).Jm (orders E).qJ (orders E).Jchart),
      Λc ≤ Λg → UniformActualPreparationContextStatement α s q ζ Λg g₀ orders horders :=
  actualContext_of_pieces α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (route_piece α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)
    (preparation_model_piece hα₀ hα₁ hs₀ hs₁ hq hζ)

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The unconditional common-preparation route from the completed actual callback.
All frequency floors, order requests, maps and models remain those of the proved
assemblies; no analytic or callback input remains. -/

/-- The uniform preparation route with the final actual-context input discharged. -/
theorem preparation_uniform_route (α s : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    UniformCommonPreparationRouteStatement α s q ζ :=
  preparation_uniform_route_of_actual_context α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (uniformActualPreparationContext α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
