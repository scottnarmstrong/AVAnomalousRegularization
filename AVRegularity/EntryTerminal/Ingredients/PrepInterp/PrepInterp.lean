-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Assembly.Prep.ModelAssembly
import AVRegularity.EntryTerminal.Ingredients.CoarseFamily.CoarseFamily
public import AVRegularity.IterationPassage.PassageJetClausesOfBounds
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.EntryTerminal.Ingredients.SeedStruct.SeedStruct
import AVRegularity.Construction.Scales.Times
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleComparison.Error.Main
import Mathlib.Algebra.Order.Star.Real

/-! **Part 3 of E2, the interpolation** (`PrepInterpPart`, Step 6; `e.term.prep`). Let `D` be the
difference `V(t_p) - P_term V(a_M)`, truncated to the order `2k₀` at the radius `r = c_K x`. Then
the half-order interpolation (`weightedNorm_half_interpolation`) gives
`‖D‖_{r,k₀} ≤ √c_{k₀} ‖D‖_{1,0}^{1/2} ‖D‖_{r,2k₀}^{1/2}`, where:
- `‖D‖_{1,0} ≤ C_M E^{Q_T}‖f‖` is the model error;
- `‖V(t_p)‖_{r,2k₀} ≤ C_K‖f‖` is the weak strong energy at `r = c_K x`, at the time
  `t_p ∈ [a_M, a + T₀]`;
- `‖P_term V(a_M)‖_{r,2k₀} ≤ ‖P_term V(a_M)‖_{ρ,K̂} ≤ C_M‖f‖`, because `c_K x ≤ ρ = c_r√(Bh)` at
  late levels (`terminal_scales_core`: `x√(B/ν)/ρ ≤ C E^{qγ+3δ}` and `B ≥ ν`).

So `‖D‖_{r,k₀} ≤ √(c_{k₀} C_M (C_K + C_M)) E^{Q_T/2}‖f‖`. The reserve is `K_need = 2k₀ ≤ K_w`.

Special cases:
- `k₀ = 0`: the `L²` bound at `c_K x`.
- `V(t_p) = P_term V(a_M)`: both sides vanish.
- `C_M ≤ 0`: the model bounds force `D = 0` up to the constant `max C_M 0`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.EntryTerminal.Ingredients

open AVRegularity.EntryTerminal.Route

/-- Truncation lowers the weighted norm. -/
theorem weightedNorm_truncate_le {S : Finset Comp} {K L : ℕ} (hKL : K ≤ L) (ρ : ℝ)
    (π : CompIn S → ℝ) (hπ : ∀ v, 0 < π v) (f : ∀ _v : CompIn S, TorusHk L ℝ) :
    weightedNorm (hr := fun _ => ℝ) ρ π (fun _ => 1) (fun v => truncateTorusHk hKL (f v)) ≤
      weightedNorm (hr := fun _ => ℝ) ρ π (fun _ => 1) f := by
  unfold weightedNorm massNormSq
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left
    (CycleComparison.Error.factorialNormSq_truncateTorusHk_le hKL ρ (f v)) ?_)
  have := hπ v
  positivity

/-- The weighted norm grows with the radius. -/
theorem weightedNorm_radius_le {S : Finset Comp} {K : ℕ} {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R)
    (π : CompIn S → ℝ) (hπ : ∀ v, 0 < π v) (f : ∀ _v : CompIn S, TorusHk K ℝ) :
    weightedNorm (hr := fun _ => ℝ) r π (fun _ => 1) f ≤
      weightedNorm (hr := fun _ => ℝ) R π (fun _ => 1) f := by
  unfold weightedNorm massNormSq
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left
    (CycleJointProofs.factorialNormSq_mono_radius hr hrR (f v).val) ?_)
  have := hπ v
  positivity

/-- The weighted norm at one time of the window is at most the strong energy. -/
theorem weightedNorm_le_of_strongEnergy {S : Finset Comp} {K : ℕ} {ρ B : ℝ}
    {π : CompIn S → ℝ} (hπ : ∀ v, 0 < π v) {t₀ t₁ s E : ℝ} (hs : s ∈ Set.Icc t₀ t₁)
    (hE0 : 0 ≤ E) (U : ∀ v : CompIn S, ℝ → TorusHk K (ScalarH v.1.root))
    (Uw : ∀ v : CompIn S, ℝ → TorusHk (K + 1) (ScalarH v.1.root))
    (hE : strongEnergy ρ B π t₀ t₁ U Uw ≤ ENNReal.ofReal E) :
    weightedNorm (hr := ScalarH) ρ π (fun _ => 1) (fun v => U v s) ≤ E := by
  unfold weightedNorm massNormSq
  simp only [one_pow, div_one]
  have hsq : ENNReal.ofReal (∑ v, (π v)⁻¹ * factorialNormSq ρ (U v s).val) ≤
      ENNReal.ofReal (E ^ 2) := by
    refine (slice_le_strongEnergy_sq (B := B) hπ U Uw hs).trans ?_
    calc strongEnergy ρ B π t₀ t₁ U Uw ^ (2 : ℝ)
        ≤ ENNReal.ofReal E ^ (2 : ℝ) := ENNReal.rpow_le_rpow hE (by norm_num)
      _ = ENNReal.ofReal (E ^ 2) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hE0 (by norm_num), Real.rpow_two]
  have hreal := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg E)).1 hsq
  calc Real.sqrt _ ≤ Real.sqrt (E ^ 2) := Real.sqrt_le_sqrt hreal
    _ = E := Real.sqrt_sq hE0

/-- `c_K x ≤ ρ` from `x s/ρ ≤ C e`, `s ≥ 1` and `c_K C e ≤ 1`. -/
theorem prepInterp_radius_le {x s ρ cK C e : ℝ} (hρ : 0 < ρ) (hx : 0 ≤ x) (hs : 1 ≤ s)
    (hcK : 0 ≤ cK) (h : x * s / ρ ≤ C * e) (hsmall : cK * (C * e) ≤ 1) : cK * x ≤ ρ := by
  rw [div_le_iff₀ hρ] at h
  calc cK * x ≤ cK * (x * s) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hx hs) hcK
    _ ≤ cK * (C * e * ρ) := mul_le_mul_of_nonneg_left h hcK
    _ = (cK * (C * e)) * ρ := by ring
    _ ≤ 1 * ρ := mul_le_mul_of_nonneg_right hsmall hρ.le
    _ = ρ := one_mul ρ

/-- The arithmetic of the interpolated bound. -/
theorem prepInterp_arith {c A B Cm Ck e F : ℝ} (hc : 0 ≤ c)
    (hCm : 0 ≤ Cm) (hCk : 0 ≤ Ck) (he : 0 ≤ e) (hF : 0 ≤ F)
    (hA : A ≤ Cm * e * F) (hB : B ≤ (Ck + Cm) * F) :
    Real.sqrt c * Real.sqrt A * Real.sqrt B ≤
      Real.sqrt (c * Cm * (Ck + Cm)) * Real.sqrt e * F := by
  calc Real.sqrt c * Real.sqrt A * Real.sqrt B
      ≤ Real.sqrt c * Real.sqrt (Cm * e * F) * Real.sqrt ((Ck + Cm) * F) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hA) (Real.sqrt_nonneg _))
          (Real.sqrt_le_sqrt hB) (Real.sqrt_nonneg _)
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = Real.sqrt (c * (Cm * e * F) * ((Ck + Cm) * F)) := by
        rw [Real.sqrt_mul (mul_nonneg hc (by positivity)), Real.sqrt_mul hc]
    _ = Real.sqrt ((c * Cm * (Ck + Cm)) * e * F ^ 2) := by ring_nf
    _ = Real.sqrt (c * Cm * (Ck + Cm)) * Real.sqrt e * F := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hF]

/-- **The interpolation of a difference** at the order `k₀` from the order `0` and the order `2k₀`. -/
theorem prepInterp_core {S : Finset Comp} {Kw Kh k₀ : ℕ} (h1 : 2 * k₀ ≤ Kw) (h2 : 2 * k₀ ≤ Kh)
    (hk1 : k₀ ≤ Kw) (hk2 : k₀ ≤ Kh) {r : ℝ} (hr : 0 ≤ r) (π : CompIn S → ℝ)
    (hπ : ∀ v, 0 < π v) (X : ∀ _v : CompIn S, TorusHk Kw ℝ) (Y : ∀ _v : CompIn S, TorusHk Kh ℝ)
    {a b e : ℝ} (hX : weightedNorm (hr := fun _ => ℝ) r π (fun _ => 1) X ≤ a)
    (hY : weightedNorm (hr := fun _ => ℝ) r π (fun _ => 1) Y ≤ b)
    (hE : weightedNorm (hr := fun _ => ℝ) 1 π (fun _ => 1)
      (fun v => truncateTorusHk (Nat.zero_le Kw) (X v) - truncateTorusHk (Nat.zero_le Kh) (Y v)) ≤
        e) :
    weightedNorm (hr := fun _ => ℝ) r π (fun _ => 1)
        (fun v => truncateTorusHk hk1 (X v) - truncateTorusHk hk2 (Y v)) ≤
      Real.sqrt (IterationPassage.factorialHalfCost k₀) * Real.sqrt e * Real.sqrt (a + b) := by
  let X2 : ∀ _v : CompIn S, TorusHk (2 * k₀) ℝ := fun v => truncateTorusHk h1 (X v)
  let Y2 : ∀ _v : CompIn S, TorusHk (2 * k₀) ℝ := fun v => truncateTorusHk h2 (Y v)
  have hint := IterationPassage.weightedNorm_half_interpolation r hr k₀ π hπ (X2 - Y2)
  have e1 : (fun v => truncateTorusHk hk1 (X v) - truncateTorusHk hk2 (Y v)) =
      fun v => truncateTorusHk (show k₀ ≤ 2 * k₀ by omega) ((X2 - Y2) v) := by
    funext v
    rw [Pi.sub_apply, map_sub]
    rfl
  have e0 : (fun v => truncateTorusHk (Nat.zero_le (2 * k₀)) ((X2 - Y2) v)) =
      fun v => truncateTorusHk (Nat.zero_le Kw) (X v) - truncateTorusHk (Nat.zero_le Kh) (Y v) := by
    funext v
    rw [Pi.sub_apply, map_sub]
    rfl
  have hD : weightedNorm (hr := fun _ => ℝ) r π (fun _ => 1) (X2 - Y2) ≤ a + b :=
    (IterationPassage.weightedNorm_sub_le r π hπ X2 Y2).trans (add_le_add
      ((weightedNorm_truncate_le h1 r π hπ X).trans hX)
      ((weightedNorm_truncate_le h2 r π hπ Y).trans hY))
  rw [e1]
  rw [e0] at hint
  exact hint.trans (mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE)
    (Real.sqrt_nonneg _)) (Real.sqrt_le_sqrt hD) (Real.sqrt_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))

/-- **Part 3 of E2, the interpolation.** -/
theorem prepInterp : PrepInterpPart := by
  intro X
  obtain ⟨ΛT, hΛT, hT⟩ := EntryScales.terminal_scales_core X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq X.hζ
  refine ⟨ΛT, hΛT, fun PA hΛ _ Kout => ⟨2 * PA.k₀, fun Kw Lt nW hk₀w cr hKw _ _ hcr _ cK CK CL Cχ
    kW hcK _ _ _ _ _ _ => ?_⟩⟩
  intro CM
  refine ⟨Real.sqrt (IterationPassage.factorialHalfCost PA.k₀ * max CM 0 * (max CK 0 + max CM 0)),
    fun j₀ => ?_⟩
  have h128 : 128 ≤ PA.Λ := hΛT.trans hΛ
  have hq1 : 1 < X.q := X.hq.1
  obtain ⟨C, M₁, hC1, hsc⟩ := hT PA.Λ hΛ cr hcr
  have hC : 0 < C := by linarith
  have hγ := (Scales.admissible_exponent_facts X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq).1
  have hδ := (Scales.admissible_exponent_facts X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq).2.1
  have hp : 0 < X.q * ocGamma X.α X.q + 3 * ocDelta X.α X.q := by
    have : 0 < X.q := by linarith
    positivity
  obtain ⟨Me, hMe⟩ := EntryWeakProofs.weak_epsilon_rpow_eventually_small hq1 h128 hp
    (c := (cK * C)⁻¹) (by positivity)
  refine ⟨max M₁ (Me + 1), fun M hM => ?_⟩
  have hM₁ : M₁ ≤ M := le_trans (le_max_left _ _) hM
  have hMe' : Me ≤ M - 1 := by have := le_trans (le_max_right _ _) hM; omega
  intro D hD a lawW PW Gw aM hW tp Pterm haM htp f U₀ U V Uw Vw Uk Vk hpair hmod herr
  obtain ⟨hDα, hDq, hDΛ, -, -, hband, -⟩ := hD
  have hq1D : 1 < D.q := hDq ▸ hq1
  have hΛD : 128 ≤ D.Λ := hDΛ ▸ h128
  have hπ : ∀ v, 0 < Gw.mass lawW v := fun v =>
    Construction.Preservation.Buffer.birth_compMass_pos hq1D hΛD lawW v.1
  have hF : 0 ≤ Real.sqrt (l2NormSq f) := Real.sqrt_nonneg _
  obtain ⟨hε, -, -⟩ := Scales.epsilon_basic (m := M) hq1 h128
  obtain ⟨hE, -, -⟩ := Scales.epsilon_basic (m := M - 1) hq1 h128
  -- the radius `c_K x ≤ ρ`
  obtain ⟨hr1, -, -, -, -, -, hr7, -, -, -, -⟩ := hsc M hM₁ D.κ hband
  have hκ1 : 0 < D.κ (M - 1) := by
    have hM2 : 1 ≤ PA.Λ := by omega
    exact CycleReference.bandChain_pos hM2 X.hζ hband (by omega)
  have hτ : 0 < ocTauPP X.α X.q PA.Λ M := Construction.Stream.ocTauPP_pos (by omega)
  have hrStar0 : 0 ≤ D.termRStar cK M := by
    simp only [OCData.termRStar, OCData.eps, hDq, hDΛ]
    exact mul_nonneg hcK.le hε.le
  have hrad : D.termRStar cK M ≤ D.termRho cr M := by
    simp only [OCData.termRStar, OCData.termRho, OCData.termB, OCData.termH, OCData.eps, hDα, hDq,
      hDΛ]
    refine prepInterp_radius_le (mul_pos hcr (Real.sqrt_pos.mpr (mul_pos hκ1 hτ))) hε.le
      (Real.one_le_sqrt.mpr hr1) hcK.le hr7 ?_
    rw [← mul_assoc]
    exact seedStruct_mul_le_one (mul_pos hcK hC) (hMe (M - 1) hMe')
  -- the weak strong energy at `c_K x`
  have hVSE : strongEnergy (D.termRStar cK M) (D.κ M) (Gw.mass lawW) aM (a + PA.T₀) V Vw ≤
      ENNReal.ofReal (max CK 0 * Real.sqrt (l2NormSq f)) :=
    le_add_self.trans (hpair.2.2.2.1.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hF)))
  have hV := weightedNorm_le_of_strongEnergy hπ ⟨haM, htp⟩ (mul_nonneg (le_max_right _ _) hF)
    V Vw hVSE
  -- the model at `c_K x`
  have hP : weightedNorm (hr := ScalarH) (D.termRStar cK M) (Gw.mass lawW) (fun _ => 1)
      (Pterm fun v => V v aM) ≤ max CM 0 * Real.sqrt (l2NormSq f) :=
    (weightedNorm_radius_le hrStar0 hrad _ hπ _).trans
      (hmod.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hF))
  -- the interpolation
  have hcore := prepInterp_core (Kw := Kw)
    (Kh := max Kout (max (2 * PA.k₀ + 2) (PA.NT + 2 * PA.pT + PA.k₀ + 2))) (k₀ := PA.k₀)
    (a := max CK 0 * Real.sqrt (l2NormSq f)) (b := max CM 0 * Real.sqrt (l2NormSq f))
    (e := max CM 0 * D.eps (M - 1) ^ PA.QT * Real.sqrt (l2NormSq f))
    hKw (by omega) hk₀w (k0_le_khat Kout PA.k₀ PA.NT PA.pT) hrStar0 (Gw.mass lawW) hπ
    (fun v => V v tp) (Pterm fun v => V v aM) hV hP
    (herr.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by simpa only [OCData.eps, hDq, hDΛ] using hE.le) _)) hF))
  have hEQ : 0 ≤ D.eps (M - 1) ^ PA.QT :=
    Real.rpow_nonneg (by simpa only [OCData.eps, hDq, hDΛ] using hE.le) _
  have hsq : Real.sqrt (D.eps (M - 1) ^ PA.QT) = D.eps (M - 1) ^ (PA.QT / 2) := by
    have hE' : 0 ≤ D.eps (M - 1) := by simpa only [OCData.eps, hDq, hDΛ] using hE.le
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hE', mul_one_div]
  refine hcore.trans ?_
  rw [← hsq]
  calc Real.sqrt (IterationPassage.factorialHalfCost PA.k₀) *
        Real.sqrt (max CM 0 * D.eps (M - 1) ^ PA.QT * Real.sqrt (l2NormSq f)) *
        Real.sqrt (max CK 0 * Real.sqrt (l2NormSq f) + max CM 0 * Real.sqrt (l2NormSq f))
      ≤ _ := prepInterp_arith (IterationPassage.factorialHalfCost_nonneg PA.k₀)
          (le_max_right _ _) (le_max_right _ _) hEQ hF le_rfl (by rw [add_mul])

end AVRegularity.EntryTerminal.Ingredients
