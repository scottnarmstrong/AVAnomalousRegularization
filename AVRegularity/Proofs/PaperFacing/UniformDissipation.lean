-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.TorusEnergy.LocalInt
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Construction.OcBandSet
public import AVRegularity.Statements.Definitions.CsNormLe
public import AVRegularity.Statements.Definitions.IsWeakSolutionOn
import AVRegularity.Applications.Dissipation.Linear
import AVRegularity.Applications.Dissipation.Restart
import AVRegularity.Applications.Dissipation.SolutionOperator
import AVRegularity.Applications.Dissipation.OperatorLemma
import AVRegularity.Applications.Global.CompactRangeMain
import AVRegularity.Assembly.TopWiring.Summary
import AVRegularity.Construction.Scales.Times
import AVRegularity.Proofs.PaperFacing.Arithmetic
import AVRegularity.Proofs.Results.Applications.OcGlobal
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Uniform anomalous dissipation (Theorem B of the paper)

For the construction parameters of Theorem A of the paper (`AVRegularity.Providers.oc_global`), the
same `Λ₀`, and every `τ > 0`, there is `c > 0` such that for every initial time `a`, every permitted
diffusivity `κ ∈ 𝒦` and every `f ∈ L²(𝕋²)`, every weak solution on `[a, a + τ]` with `θ(a) = f`
satisfies `κ ∫_a^{a+τ} ∫_{𝕋²} |∇θ|² ≥ c ‖f - f̄‖₂²`, equivalently
`‖θ(a + τ) - f̄‖₂² ≤ (1 - 2c) ‖f - f̄‖₂²`, and exponential decay of the variance at the
`κ`-independent rate `1 - 2c` per time `τ` (`uniform_dissipation`). The same holds with the `Λ₀` of
Theorem A (`oc_global_and_uniform_dissipation`), and in the liminf form along `κ → 0` in `𝒦`
(`uniform_dissipation_liminf`).

`uniform_dissipation_of_holder_regularity` is the implication itself, for any bounded periodic
divergence-free drift and any set of positive diffusivities: a uniform `L² → C^s` bound at the
end of the window gives the dissipation bound with `c = 1/(4N⁴)`, `N = ⌈max(C,1)^{1/s}⌉`. Its
hypothesis is the conclusion of Theorem A on one window; it is a conditional helper. -/

public section

open MeasureTheory Filter Topology Homogenization AVenhance AVRegularity.Applications

namespace AVRegularity.PaperFacing

/-- The unit cell has finite measure. -/
local instance paperDissipationFiniteCube : IsFiniteMeasure (volume.restrict unitCube) :=
  isFiniteMeasure_restrict.2 Applications.unitCube_measure_ne_top

/-! ### The `C^s` bound and the torus distance -/

/-- A continuous periodic function takes equal values at points at torus distance `0`. -/
theorem eq_of_torusDist_eq_zero_of_periodic {g : Vec 2 → ℝ} (hg : Continuous g)
    (hgp : IsZ2Periodic g) {x y : Vec 2} (hxy : torusDist x y = 0) : g x = g y := by
  by_contra hne
  have hpos : 0 < |g x - g y| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuous_iff.1 hg x _ hpos
  have hlt : torusDist x y < δ := by rw [hxy]; exact hδ
  obtain ⟨n, hn⟩ := exists_lt_of_ciInf_lt hlt
  have hd : dist (y + latticeShift n) x < δ := by
    rw [dist_eq_norm]
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_) hn
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    have h := sq_apply_le_vecNormSq (x - y - latticeShift n) i
    have e : (y + latticeShift n - x) i = -((x - y - latticeShift n) i) := by
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    rw [e, neg_sq]
    exact h
  have h := hcont _ hd
  rw [hgp n y, Real.dist_eq, abs_sub_comm] at h
  exact lt_irrefl _ h

/-- The sup bound contained in `CsNormLe`. -/
theorem abs_le_of_csNormLe_dissipation {s : ℝ} {g : Vec 2 → ℝ} {K : ℝ} (h : CsNormLe s g K) (x : Vec 2) :
    |g x| ≤ K := by
  have hz : torusDist 0 (fun _ => (1 : ℝ) / 4) ≠ 0 := by
    refine (Applications.torusDist_pos_of_small ?_ ?_).ne'
    · intro h0
      have := congrFun h0 0
      norm_num at this
    · unfold Applications.eNorm
      rw [show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
        rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      refine Real.sqrt_le_sqrt ?_
      simp [vecNormSq, vecDot]
      norm_num
  have h1 := h x 0 (fun _ => (1 : ℝ) / 4) hz
  have h2 : 0 ≤ |g 0 - g (fun _ => (1 : ℝ) / 4)| / torusDist 0 (fun _ => (1 : ℝ) / 4) ^ s :=
    div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Applications.torusDist_nonneg _ _) _)
  linarith

/-- The Hölder bound contained in `CsNormLe`, at every pair of points. -/
theorem abs_sub_le_of_csNormLe_dissipation {s : ℝ} (hs : 0 < s) {g : Vec 2 → ℝ} {K : ℝ}
    (h : CsNormLe s g K) (hg : Continuous g) (hgp : IsZ2Periodic g) (y z : Vec 2) :
    |g y - g z| ≤ K * torusDist y z ^ s := by
  by_cases hd : torusDist y z = 0
  · rw [eq_of_torusDist_eq_zero_of_periodic hg hgp hd, hd, Real.zero_rpow hs.ne']
    simp
  · have hpos : 0 < torusDist y z ^ s :=
      Real.rpow_pos_of_pos (lt_of_le_of_ne (Applications.torusDist_nonneg _ _) (Ne.symm hd)) _
    have h1 := h y y z hd
    have h2 : |g y - g z| / torusDist y z ^ s ≤ K := by linarith [abs_nonneg (g y)]
    rwa [div_le_iff₀ hpos] at h2

/-- The unit cell has volume `1`. -/
theorem volume_unitCube_dissipation : (volume : Measure (Vec 2)) unitCube = 1 := by
  unfold unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

/-- Subtracting a constant from a weak solution and its datum. -/
theorem isWeakSolutionOnWith_sub_const_dissipation {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ}
    {g : Vec 2 → ℝ} (hg : MemL2On unitCube g) {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    (hθ : IsWeakSolutionOnWith b κ t₁ t₂ g θ Dθ) (m : ℝ) :
    IsWeakSolutionOnWith b κ t₁ t₂ (fun x => g x - m) (fun t x => θ t x - m) Dθ := by
  have h := Applications.Dissipation.isWeakSolutionOnWith_add hg (memLp_const (-m)) hθ
    (Applications.Dissipation.isWeakSolutionOnWith_const b κ t₁ t₂ (-m))
  have e1 : (g + fun _ => -m) = fun x => g x - m := by
    funext x
    simp only [Pi.add_apply, sub_eq_add_neg]
  have e2 : (θ + fun _ _ => -m) = fun t x => θ t x - m := by
    funext t x
    simp only [Pi.add_apply, sub_eq_add_neg]
  have e3 : (Dθ + fun _ _ => (0 : Vec 2)) = Dθ := by
    funext t x
    simp
  rw [e1, e2, e3] at h
  exact h

/-- **Regularity implies uniform dissipation** (a conditional helper). If on every
window `[a, a + τ]` and for every `κ ∈ K` the final slice of every weak solution has a continuous
periodic representative with `‖θ(a + τ)‖_{C^s} ≤ C ‖f‖₂`, then with
`c = 1/(4N⁴)`, `N = ⌈max(C,1)^{1/s}⌉`, every weak solution dissipates the fraction `c` of the
variance of its datum. -/
theorem uniform_dissipation_of_holder_regularity {s : ℝ} (hs : 0 < s)
    {b : ℝ → Vec 2 → Vec 2} {K : Set ℝ} (hK : ∀ κ ∈ K, 0 < κ) {τ C : ℝ} (hτ : 0 < τ)
    (hb : ∀ a : ℝ, IsWindowDrift b a (a + τ))
    (hreg : ∀ a : ℝ, ∀ κ ∈ K, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
      ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + τ) f θ →
        ∃ Θ : Vec 2 → ℝ, Continuous Θ ∧ IsZ2Periodic Θ ∧
          Θ =ᵐ[volume.restrict unitCube] θ (a + τ) ∧
          CsNormLe s Θ (C * Real.sqrt (l2NormSq f))) :
    ∀ a : ℝ, ∀ κ ∈ K, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
      ∀ θ : ℝ → Vec 2 → ℝ, ∀ Dθ : ℝ → Vec 2 → Vec 2,
        IsWeakSolutionOnWith b κ a (a + τ) f θ Dθ →
          1 / (4 * (⌈max C 1 ^ (1 / s)⌉₊ : ℝ) ^ 4) *
              l2NormSq (fun x => f x - ∫ y in unitCube, f y) ≤
            κ * ∫ p in Set.Ioo a (a + τ) ×ˢ unitCube, vecNormSq (Dθ p.1 p.2) ∧
          l2NormSq (fun x => θ (a + τ) x - ∫ y in unitCube, f y) ≤
            (1 - 2 * (1 / (4 * (⌈max C 1 ^ (1 / s)⌉₊ : ℝ) ^ 4))) *
              l2NormSq (fun x => f x - ∫ y in unitCube, f y) := by
  intro a κ hκK f hf θ Dθ hθ
  have hκ := hK κ hκK
  have h12 : a < a + τ := by linarith
  obtain ⟨S, hSex, hSrep, -, hSconst, hSmass, hSpos⟩ :=
    Applications.Dissipation.exists_weakSolutionOperator hκ h12 (hb a)
  have hrep : ∀ g : Lp ℝ 2 (volume.restrict unitCube), ∃ G : Vec 2 → ℝ, Continuous G ∧
      IsZ2Periodic G ∧ G =ᵐ[volume.restrict unitCube] S g ∧ CsNormLe s G (C * ‖g‖) := by
    intro g
    obtain ⟨θg, Dθg, hθg⟩ := hSex g
    obtain ⟨Θ, hΘc, hΘp, hΘe, hΘcs⟩ := hreg a κ hκK g (Lp.memLp g) θg ⟨Dθg, hθg⟩
    refine ⟨Θ, hΘc, hΘp, hΘe.trans (hSrep g θg Dθg hθg), ?_⟩
    rwa [Applications.Dissipation.l2NormSq_coe_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)] at hΘcs
  obtain ⟨P, hP⟩ := Applications.Dissipation.exists_continuous_representative_linearMap S
    (fun g => by
      obtain ⟨G, h1, h2, h3, -⟩ := hrep g
      exact ⟨G, h1, h2, h3⟩)
  have hPcs : ∀ g, CsNormLe s (P g) (C * ‖g‖) := by
    intro g
    obtain ⟨G, h1, h2, h3, h4⟩ := hrep g
    have : P g = G := Applications.Dissipation.eq_of_continuous_periodic_ae_eq (hP g).1 h1
      (hP g).2.1 h2 ((hP g).2.2.trans h3.symm)
    rw [this]
    exact h4
  -- the hypotheses of the operator lemma, with constant `max C 1`
  have hpos : ∀ g : Lp ℝ 2 (volume.restrict unitCube),
      (∀ᵐ x ∂(volume.restrict unitCube), 0 ≤ g x) → ∀ x, 0 ≤ P g x := by
    intro g hg x
    have h1 := hSpos g hg
    have heq : P g = fun y => max (P g y) 0 :=
      Applications.Dissipation.eq_of_continuous_periodic_ae_eq (hP g).1
        ((hP g).1.max continuous_const) (hP g).2.1 (fun k y => by simp only [(hP g).2.1 k y])
        (by
          filter_upwards [(hP g).2.2, h1] with y hy1 hy2
          exact (max_eq_left (hy1 ▸ hy2)).symm)
    rw [heq]
    exact le_max_right _ _
  have hone : ∀ g : Lp ℝ 2 (volume.restrict unitCube),
      (g : Vec 2 → ℝ) =ᵐ[volume.restrict unitCube] (fun _ => 1) → ∀ x, P g x = 1 := by
    intro g hg x
    have heq : P g = fun _ => 1 :=
      Applications.Dissipation.eq_of_continuous_periodic_ae_eq (hP g).1 continuous_const
        (hP g).2.1 (fun _ _ => rfl) ((hP g).2.2.trans (hSconst 1 g hg))
    rw [heq]
  have hmass : ∀ g : Lp ℝ 2 (volume.restrict unitCube),
      ∫ x in unitCube, P g x = ∫ x in unitCube, g x := fun g =>
    (integral_congr_ae (hP g).2.2).trans (hSmass g)
  have hsup : ∀ g x, |P g x| ≤ max C 1 * ‖g‖ := fun g x =>
    (abs_le_of_csNormLe_dissipation (hPcs g) x).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hhol : ∀ g x y, |P g x - P g y| ≤ max C 1 * torusDist x y ^ s * ‖g‖ := by
    intro g x y
    have h := abs_sub_le_of_csNormLe_dissipation hs (hPcs g) (hP g).1 (hP g).2.1 x y
    have hd : 0 ≤ torusDist x y ^ s := Real.rpow_nonneg (Applications.torusDist_nonneg _ _) _
    calc |P g x - P g y| ≤ C * ‖g‖ * torusDist x y ^ s := h
      _ ≤ max C 1 * ‖g‖ * torusDist x y ^ s :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)) hd
      _ = max C 1 * torusDist x y ^ s * ‖g‖ := by ring
  -- the centred datum
  have hmem0 : MemL2On unitCube (fun x => f x - ∫ y in unitCube, f y) :=
    hf.sub (memLp_const _)
  have hg₀ := hmem0.coeFn_toLp
  have hmean : ∫ x in unitCube, hmem0.toLp (fun x => f x - ∫ y in unitCube, f y) x = 0 := by
    rw [integral_congr_ae hg₀, integral_sub (hf.integrable one_le_two) (integrable_const _),
      integral_const, Measure.real, Measure.restrict_apply_univ, volume_unitCube_dissipation]
    simp
  have hop := Applications.Dissipation.integral_sq_le_of_positive_holder_operator hs
    (le_max_right C 1) P (fun g => (hP g).1) hpos hone hmass hsup hhol _ hmean
  -- the centred solution, its final slice, and the energy identity
  have hθ' := isWeakSolutionOnWith_sub_const_dissipation hf hθ (∫ y in unitCube, f y)
  have hfin : (fun x => θ (a + τ) x - ∫ y in unitCube, f y) =ᵐ[volume.restrict unitCube]
      P (hmem0.toLp (fun x => f x - ∫ y in unitCube, f y)) :=
    (hSrep _ _ _ (Applications.Dissipation.isWeakSolutionOnWith_congr_datum hg₀.symm hθ')).trans
      (hP _).2.2.symm
  have hW : ∫ x in unitCube, P (hmem0.toLp (fun x => f x - ∫ y in unitCube, f y)) x ^ 2 =
      l2NormSq (fun x => θ (a + τ) x - ∫ y in unitCube, f y) := by
    unfold l2NormSq
    refine integral_congr_ae ?_
    filter_upwards [hfin] with x hx
    rw [hx]
  have hV : ‖hmem0.toLp (fun x => f x - ∫ y in unitCube, f y)‖ ^ 2 =
      l2NormSq (fun x => f x - ∫ y in unitCube, f y) := by
    rw [← Applications.Dissipation.l2NormSq_coe_eq_norm_sq]
    unfold l2NormSq
    refine integral_congr_ae ?_
    filter_upwards [hg₀] with x hx
    rw [hx]
  rw [hW, hV] at hop
  have hE := energy_identity h12 (hb a) hmem0 hθ' (a + τ) ⟨h12.le, le_rfl⟩
  have hc : 2 * (1 / (4 * (⌈max C 1 ^ (1 / s)⌉₊ : ℝ) ^ 4)) =
      1 / (2 * (⌈max C 1 ^ (1 / s)⌉₊ : ℝ) ^ 4) := by ring
  refine ⟨?_, ?_⟩
  · nlinarith [hE, hop, hc]
  · rw [hc]
    exact hop

/-- Iterating the one-window contraction `‖θ(a + τ) - f̄‖² ≤ (1 - 2c) ‖f - f̄‖²` on consecutive
windows by restarts (conditional helper; its hypothesis is the second conclusion of
`uniform_dissipation_of_holder_regularity`). -/
theorem l2NormSq_sub_mean_le_pow_of_contraction {b : ℝ → Vec 2 → Vec 2} {κ c τ : ℝ}
    (hκ : 0 < κ) (hτ : 0 < τ) (hc : 0 ≤ 1 - 2 * c) (hbw : ∀ t₁ t₂ : ℝ, IsWindowDrift b t₁ t₂)
    (hone : ∀ a : ℝ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
      ∀ θ : ℝ → Vec 2 → ℝ, ∀ Dθ : ℝ → Vec 2 → Vec 2,
        IsWeakSolutionOnWith b κ a (a + τ) f θ Dθ →
          l2NormSq (fun x => θ (a + τ) x - ∫ y in unitCube, f y) ≤
            (1 - 2 * c) * l2NormSq (fun x => f x - ∫ y in unitCube, f y))
    {a t : ℝ} (ht : 0 < t) {f : Vec 2 → ℝ} (hf : MemL2On unitCube f) {θ : ℝ → Vec 2 → ℝ}
    {Dθ : ℝ → Vec 2 → Vec 2} (hθ : IsWeakSolutionOnWith b κ a (a + t) f θ Dθ) :
    l2NormSq (fun x => θ (a + t) x - ∫ y in unitCube, f y) ≤
      (1 - 2 * c) ^ ⌊t / τ⌋₊ * l2NormSq (fun x => f x - ∫ y in unitCube, f y) := by
  have hat : a < a + t := by linarith
  set m := ∫ y in unitCube, f y with hm
  -- the mean is conserved
  have hmass : ∀ u ∈ Set.Icc a (a + t), ∫ x in unitCube, θ u x = m := fun u hu =>
    Applications.Dissipation.integral_eq_of_isWeakSolutionOnWith hat (hbw a (a + t)) hf hθ u hu
  -- the variance does not increase
  have hmono : ∀ u ∈ Set.Icc a (a + t), l2NormSq (fun x => θ (a + t) x - m) ≤
      l2NormSq (fun x => θ u x - m) := by
    intro u hu
    rcases eq_or_lt_of_le hu.2 with heq | hlt
    · rw [heq]
    · have hθu := Applications.Dissipation.isWeakSolutionOnWith_restart hu hθ
      have hmemu : MemL2On unitCube (θ u) := (hθ.1 u hu).2
      have h := (l2NormSq_le_of_weakSolutionOnWith hκ.le hlt (hbw u (a + t))
        (hmemu.sub (memLp_const m)) (isWeakSolutionOnWith_sub_const_dissipation hmemu hθu m)).1
        (a + t) ⟨hlt.le, le_rfl⟩
      exact h
  -- one window from `a + jτ`, `j ≥ 1`
  have hstep : ∀ j : ℕ, ((j : ℝ) + 1) * τ ≤ t →
      l2NormSq (fun x => θ (a + ((j : ℝ) + 1) * τ) x - m) ≤
        (1 - 2 * c) * l2NormSq (fun x => θ (a + (j : ℝ) * τ) x - m) := by
    intro j hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hu : a + (j : ℝ) * τ ∈ Set.Icc a (a + t) :=
      ⟨by nlinarith, by nlinarith⟩
    have hθu := Applications.Dissipation.isWeakSolutionOnWith_restart hu hθ
    have hθu' := isWeakSolutionOnWith_restrict
      (show a + (j : ℝ) * τ + τ ≤ a + t by nlinarith) hθu
    have h := hone (a + (j : ℝ) * τ) (θ (a + (j : ℝ) * τ)) (hθ.1 _ hu).2 θ Dθ hθu'
    rw [hmass _ hu] at h
    rw [show a + ((j : ℝ) + 1) * τ = a + (j : ℝ) * τ + τ by ring]
    exact h
  -- iterate
  have hiter : ∀ j : ℕ, ((j : ℝ) + 1) * τ ≤ t →
      l2NormSq (fun x => θ (a + ((j : ℝ) + 1) * τ) x - m) ≤
        (1 - 2 * c) ^ (j + 1) * l2NormSq (fun x => f x - m) := by
    intro j
    induction j with
    | zero =>
      intro hj
      have hθ1 := isWeakSolutionOnWith_restrict (show a + τ ≤ a + t by simpa using hj) hθ
      have h := hone a f hf θ Dθ hθ1
      simpa using h
    | succ j ih =>
      intro hj
      have hj2 : ((j : ℝ) + 1 + 1) * τ ≤ t := by
        have := hj
        push_cast at this
        linarith
      have hj' : ((j : ℝ) + 1) * τ ≤ t := by nlinarith
      have h1 := hstep (j + 1) (by push_cast; linarith)
      have h2 := ih hj'
      push_cast at h1 ⊢
      calc l2NormSq (fun x => θ (a + ((j : ℝ) + 1 + 1) * τ) x - m)
          ≤ (1 - 2 * c) * l2NormSq (fun x => θ (a + ((j : ℝ) + 1) * τ) x - m) := h1
        _ ≤ (1 - 2 * c) * ((1 - 2 * c) ^ (j + 1) * l2NormSq (fun x => f x - m)) :=
          mul_le_mul_of_nonneg_left h2 hc
        _ = (1 - 2 * c) ^ (j + 1 + 1) * l2NormSq (fun x => f x - m) := by ring
  -- conclude with `k = ⌊t/τ⌋`
  have hk : (⌊t / τ⌋₊ : ℝ) * τ ≤ t := by
    have := Nat.floor_le (div_nonneg ht.le hτ.le)
    rwa [le_div_iff₀ hτ] at this
  rcases Nat.eq_zero_or_pos ⌊t / τ⌋₊ with h0 | hpos
  · rw [h0, pow_zero, one_mul]
    have h := (l2NormSq_le_of_weakSolutionOnWith hκ.le hat (hbw a (a + t))
      (hf.sub (memLp_const m)) (isWeakSolutionOnWith_sub_const_dissipation hf hθ m)).1
      (a + t) ⟨hat.le, le_rfl⟩
    exact h
  · obtain ⟨j, hj⟩ : ∃ j, ⌊t / τ⌋₊ = j + 1 := ⟨⌊t / τ⌋₊ - 1, by omega⟩
    rw [hj] at hk ⊢
    push_cast at hk
    have hu : a + ((j : ℝ) + 1) * τ ∈ Set.Icc a (a + t) :=
      ⟨by nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)], by linarith⟩
    exact (hmono _ hu).trans (hiter j hk)

/-- **Theorem A of the paper and the uniform dissipation with one `Λ₀`.** The conclusion of
Theorem A (`AVRegularity.Providers.oc_global`) and the conclusion of `uniform_dissipation` hold for
the same `Λ₀`: the uniform dissipation needs no enlargement of the `Λ₀` of Theorem A. -/
theorem oc_global_and_uniform_dissipation (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∀ b : ℝ → Vec 2 → Vec 2,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) →
          (∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C : ℝ,
            ∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
            ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ →
              ∃ Θ : ℝ → Vec 2 → ℝ,
                ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2)
                  (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) ∧
                ∀ t ∈ Set.Icc (a + t₀) (a + T),
                  IsZ2Periodic (Θ t) ∧ Θ t =ᵐ[volume.restrict unitCube] θ t ∧
                  CsNormLe s (Θ t) (C * Real.sqrt (l2NormSq f))) ∧
          ∀ τ : ℝ, 0 < τ → ∃ c : ℝ, 0 < c ∧
            (∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
              ∀ θ : ℝ → Vec 2 → ℝ, ∀ Dθ : ℝ → Vec 2 → Vec 2,
                IsWeakSolutionOnWith b κ a (a + τ) f θ Dθ →
                  c * l2NormSq (fun x => f x - ∫ y in unitCube, f y) ≤
                      κ * ∫ p in Set.Ioo a (a + τ) ×ˢ unitCube, vecNormSq (Dθ p.1 p.2) ∧
                    l2NormSq (fun x => θ (a + τ) x - ∫ y in unitCube, f y) ≤
                      (1 - 2 * c) * l2NormSq (fun x => f x - ∫ y in unitCube, f y)) ∧
            (∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
              ∀ t : ℝ, 0 < t → ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + t) f θ →
                l2NormSq (fun x => θ (a + t) x - ∫ y in unitCube, f y) ≤
                  (1 - 2 * c) ^ ⌊t / τ⌋₊ *
                    l2NormSq (fun x => f x - ∫ y in unitCube, f y)) := by
  obtain ⟨Λ₀, hΛ₀, hA⟩ := Providers.oc_global α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ Φ hΦ b hb => ⟨hA Λ hΛ Φ hΦ b hb, fun τ hτ => ?_⟩⟩
  have hΛ128 : 128 ≤ Λ := hΛ₀.trans hΛ
  obtain ⟨C, hC⟩ := hA Λ hΛ Φ hΦ b hb (τ / 2) τ (half_pos hτ) (half_lt_self hτ)
  have hbH := Applications.limit_isHolderDivFree α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ128 Φ hΦ b hb
  have hbw : ∀ t₁ t₂ : ℝ, IsWindowDrift b t₁ t₂ := fun t₁ t₂ =>
    isWindowDrift_of_isHolderDivFreeVelocity hα₀ hbH t₁ t₂
  have hK : ∀ κ ∈ ocBandSet α q Λ, 0 < κ := fun κ hκ =>
    Assembly.TopWiring.pos_of_mem_ocBandSet (by omega) hκ
  have hreg : ∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
      ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + τ) f θ →
        ∃ Θ : Vec 2 → ℝ, Continuous Θ ∧ IsZ2Periodic Θ ∧
          Θ =ᵐ[volume.restrict unitCube] θ (a + τ) ∧
          CsNormLe s Θ (C * Real.sqrt (l2NormSq f)) := by
    intro a κ hκ f hf θ hθ
    obtain ⟨Θ, hΘc, hΘ⟩ := hC a κ hκ f hf θ hθ
    have hT : a + τ ∈ Set.Icc (a + τ / 2) (a + τ) := ⟨by linarith, le_rfl⟩
    obtain ⟨hp, he, hcs⟩ := hΘ (a + τ) hT
    refine ⟨Θ (a + τ), ?_, hp, he, hcs⟩
    have hmaps : Set.MapsTo (fun x : Vec 2 => (a + τ, x)) Set.univ
        (Set.Icc (a + τ / 2) (a + τ) ×ˢ Set.univ) := fun x _ => ⟨hT, Set.mem_univ x⟩
    exact continuousOn_univ.1
      (hΘc.comp (Continuous.prodMk_right (a + τ)).continuousOn hmaps)
  have hD := uniform_dissipation_of_holder_regularity hs₀ hK hτ (fun a => hbw a (a + τ)) hreg
  set N : ℝ := (⌈max C 1 ^ (1 / s)⌉₊ : ℝ) with hN
  have hN1 : 1 ≤ N := by
    rw [hN]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (Real.rpow_pos_of_pos
      (lt_of_lt_of_le one_pos (le_max_right C 1)) _)).ne'
  have hcpos : 0 < 1 / (4 * N ^ 4) := by positivity
  have hc2 : 0 ≤ 1 - 2 * (1 / (4 * N ^ 4)) := by
    have : N ^ 4 ≥ 1 := one_le_pow₀ hN1
    rw [sub_nonneg, show 2 * (1 / (4 * N ^ 4)) = 1 / (2 * N ^ 4) by ring, div_le_one (by positivity)]
    linarith
  refine ⟨1 / (4 * N ^ 4), hcpos, fun a κ hκ f hf θ Dθ hθ => hD a κ hκ f hf θ Dθ hθ,
    fun a κ hκ f hf t ht θ hθ => ?_⟩
  obtain ⟨Dθ, hθ'⟩ := hθ
  exact l2NormSq_sub_mean_le_pow_of_contraction (hK κ hκ) hτ hc2 hbw
    (fun a' f' hf' θ' Dθ' hθ'' => (hD a' κ hκ f' hf' θ' Dθ' hθ'').2) ht hf hθ'

/-- **Uniform anomalous dissipation.** For the construction parameters of Theorem A of the paper
and `Λ ≥ Λ₀`, for every `τ > 0` there is `c > 0` such that for every `a ∈ ℝ`,
`κ ∈ 𝒦` and `f ∈ L²(𝕋²)`, with `f̄ = ∫_{𝕋²} f`:
(1) every weak solution on `[a, a + τ]` with `θ(a) = f` has
`κ ∫_a^{a+τ} ∫_{𝕋²} |∇θ|² ≥ c ‖f - f̄‖₂²`, (2) equivalently `‖θ(a + τ) - f̄‖₂² ≤ (1 - 2c) ‖f - f̄‖₂²`;
(3) every weak solution on `[a, a + t]`, `t > 0`, with `θ(a) = f` has
`‖θ(a + t) - f̄‖₂² ≤ (1 - 2c)^{⌊t/τ⌋} ‖f - f̄‖₂²`. -/
theorem uniform_dissipation (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∀ b : ℝ → Vec 2 → Vec 2,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) →
          ∀ τ : ℝ, 0 < τ → ∃ c : ℝ, 0 < c ∧
            (∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
              ∀ θ : ℝ → Vec 2 → ℝ, ∀ Dθ : ℝ → Vec 2 → Vec 2,
                IsWeakSolutionOnWith b κ a (a + τ) f θ Dθ →
                  c * l2NormSq (fun x => f x - ∫ y in unitCube, f y) ≤
                      κ * ∫ p in Set.Ioo a (a + τ) ×ˢ unitCube, vecNormSq (Dθ p.1 p.2) ∧
                    l2NormSq (fun x => θ (a + τ) x - ∫ y in unitCube, f y) ≤
                      (1 - 2 * c) * l2NormSq (fun x => f x - ∫ y in unitCube, f y)) ∧
            (∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
              ∀ t : ℝ, 0 < t → ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + t) f θ →
                l2NormSq (fun x => θ (a + t) x - ∫ y in unitCube, f y) ≤
                  (1 - 2 * c) ^ ⌊t / τ⌋₊ *
                    l2NormSq (fun x => f x - ∫ y in unitCube, f y)) := by
  obtain ⟨Λ₀, hΛ₀, hall⟩ := oc_global_and_uniform_dissipation α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  exact ⟨Λ₀, hΛ₀, fun Λ hΛ Φ hΦ b hb => (hall Λ hΛ Φ hΦ b hb).2⟩

/-- **Uniform anomalous dissipation, liminf form.** Same setting: for every `τ > 0` there is `c > 0`
such that for every `a`, every mean-zero `f ∈ L²(𝕋²)` and every family `θ_κ` (`κ ∈ 𝒦`) of weak
solutions on `[a, a + τ]` with `θ_κ(a) = f`: `𝒦` accumulates at `0`, the dissipation
`κ ∬ |∇θ_κ|²` lies in `[0, ‖f‖₂²/2]` for every `κ ∈ 𝒦` (so its `liminf` along `κ → 0` in `𝒦` is a
genuine one), and `c ‖f‖₂² ≤ liminf_{κ → 0, κ ∈ 𝒦} κ ∬ |∇θ_κ|²`. -/
theorem uniform_dissipation_liminf (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∀ b : ℝ → Vec 2 → Vec 2,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) →
          ∀ τ : ℝ, 0 < τ → ∃ c : ℝ, 0 < c ∧
            ∀ a : ℝ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f → ∫ x in unitCube, f x = 0 →
            ∀ θ : ℝ → ℝ → Vec 2 → ℝ, ∀ Dθ : ℝ → ℝ → Vec 2 → Vec 2,
              (∀ κ ∈ ocBandSet α q Λ, IsWeakSolutionOnWith b κ a (a + τ) f (θ κ) (Dθ κ)) →
                (𝓝[ocBandSet α q Λ] (0 : ℝ)).NeBot ∧
                (∀ κ ∈ ocBandSet α q Λ,
                  0 ≤ κ * ∫ p in Set.Ioo a (a + τ) ×ˢ unitCube, vecNormSq (Dθ κ p.1 p.2) ∧
                  κ * ∫ p in Set.Ioo a (a + τ) ×ˢ unitCube, vecNormSq (Dθ κ p.1 p.2) ≤
                    l2NormSq f / 2) ∧
                c * l2NormSq f ≤ Filter.liminf
                  (fun κ => κ * ∫ p in Set.Ioo a (a + τ) ×ˢ unitCube, vecNormSq (Dθ κ p.1 p.2))
                  (𝓝[ocBandSet α q Λ] (0 : ℝ)) := by
  obtain ⟨Λ₀, hΛ₀, hall⟩ := uniform_dissipation α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ Φ hΦ b hb τ hτ => ?_⟩
  obtain ⟨c, hc, hdiss, -⟩ := hall Λ hΛ Φ hΦ b hb τ hτ
  have hΛ128 : 128 ≤ Λ := hΛ₀.trans hΛ
  have hbH := Applications.limit_isHolderDivFree α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ128 Φ hΦ b hb
  refine ⟨c, hc, fun a f hf hmean θ Dθ hθ => ?_⟩
  -- the bands accumulate at `0`
  have hq1 : 1 < q := hq.1
  have he : 0 < (1 + α) - ocGamma α q := by
    unfold ocGamma
    have hq0 : 0 < q + 1 := by linarith
    rw [sub_pos, div_lt_iff₀ hq0]
    nlinarith
  have hneBot : (𝓝[ocBandSet α q Λ] (0 : ℝ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot]
    have hεpos : ∀ M : ℕ, 0 < ocEpsilon q Λ M := fun M =>
      (Scales.epsilon_basic (m := M) hq1 hΛ128).1
    have hmem : ∀ M : ℕ, ocEpsilon q Λ (M + 1) ^ ((1 + α) - ocGamma α q) ∈ ocBandSet α q Λ := by
      intro M
      have hp : 0 < ocEpsilon q Λ (M + 1) ^ ((1 + α) - ocGamma α q) :=
        Real.rpow_pos_of_pos (hεpos _) _
      refine Set.mem_iUnion.2 ⟨M + 1, Set.mem_iUnion.2 ⟨by omega, ?_, ?_⟩⟩
      · linarith
      · linarith
    have hΛ1 : (1 : ℝ) < Λ := by exact_mod_cast (by omega : 1 < Λ)
    have hgeom : Tendsto (fun M : ℕ => ((Λ : ℝ)⁻¹) ^ (M + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 (by linarith))
        (inv_lt_one_of_one_lt₀ hΛ1)).comp (tendsto_add_atTop_nat 1)
    have hcont : Tendsto (fun y : ℝ => y ^ ((1 + α) - ocGamma α q)) (𝓝 0) (𝓝 0) := by
      have h := (Real.continuousAt_rpow_const 0 ((1 + α) - ocGamma α q) (Or.inr he.le)).tendsto
      rwa [Real.zero_rpow he.ne'] at h
    have hlim : Tendsto (fun M : ℕ => ocEpsilon q Λ (M + 1) ^ ((1 + α) - ocGamma α q)) atTop
        (𝓝 0) := by
      refine squeeze_zero (fun M => (Real.rpow_pos_of_pos (hεpos _) _).le) (fun M => ?_)
        (hcont.comp hgeom)
      exact Real.rpow_le_rpow (hεpos _).le (epsilon_le_inv_pow hq1 hΛ128 (M + 1)) he.le
    exact mem_closure_of_tendsto hlim (Filter.Eventually.of_forall hmem)
  -- the energy bound
  have hbound : ∀ κ ∈ ocBandSet α q Λ,
      0 ≤ κ * ∫ p in Set.Ioo a (a + τ) ×ˢ unitCube, vecNormSq (Dθ κ p.1 p.2) ∧
      κ * ∫ p in Set.Ioo a (a + τ) ×ˢ unitCube, vecNormSq (Dθ κ p.1 p.2) ≤ l2NormSq f / 2 := by
    intro κ hκ
    have hκ0 := Assembly.TopWiring.pos_of_mem_ocBandSet (by omega) hκ
    have h := (l2NormSq_le_of_weakSolutionOnWith hκ0.le (by linarith : a < a + τ)
      (isWindowDrift_of_isHolderDivFreeVelocity hα₀ hbH a (a + τ)) hf (hθ κ hκ)).2
      (a + τ) ⟨by linarith, le_rfl⟩
    refine ⟨mul_nonneg hκ0.le (integral_nonneg fun p => vecNormSq_nonneg _), by linarith⟩
  refine ⟨hneBot, hbound, ?_⟩
  have hV : l2NormSq (fun x => f x - ∫ y in unitCube, f y) = l2NormSq f := by
    rw [hmean]
    simp
  have hev : ∀ᶠ κ in 𝓝[ocBandSet α q Λ] (0 : ℝ), c * l2NormSq f ≤
      κ * ∫ p in Set.Ioo a (a + τ) ×ˢ unitCube, vecNormSq (Dθ κ p.1 p.2) := by
    filter_upwards [self_mem_nhdsWithin] with κ hκ
    rw [← hV]
    exact (hdiss a κ hκ f hf (θ κ) (Dθ κ) (hθ κ hκ)).1
  have hbdd : IsBoundedUnder (· ≤ ·) (𝓝[ocBandSet α q Λ] (0 : ℝ))
      (fun κ => κ * ∫ p in Set.Ioo a (a + τ) ×ˢ unitCube, vecNormSq (Dθ κ p.1 p.2)) :=
    ⟨l2NormSq f / 2, by
      rw [eventually_map]
      filter_upwards [self_mem_nhdsWithin] with κ hκ
      exact (hbound κ hκ).2⟩
  exact le_liminf_of_le hbdd.isCoboundedUnder_ge hev

/-- `(1 - 2c)^{⌊u⌋} ≤ 4 e^{-2cu}` for `0 ≤ c ≤ 1/4`. -/
private theorem pow_floor_le_four_mul_exp_dissipation {c : ℝ} (u : ℝ) (hc0 : 0 ≤ c)
    (hc : c ≤ 1 / 4) : (1 - 2 * c) ^ ⌊u⌋₊ ≤ 4 * Real.exp (-2 * c * u) := by
  have h1 : 0 ≤ 1 - 2 * c := by linarith
  have h2 : 1 - 2 * c ≤ Real.exp (-2 * c) := by
    have := Real.add_one_le_exp (-2 * c)
    linarith
  have hn : u < (⌊u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one u
  have hlin : -2 * c * (⌊u⌋₊ : ℝ) ≤ -2 * c * u + 2 * c := by
    nlinarith [mul_nonneg hc0 (sub_pos.2 hn).le]
  have hexp : Real.exp (2 * c) ≤ 4 := by
    have h3 : Real.exp (2 * c) ≤ Real.exp 1 := Real.exp_le_exp.2 (by linarith)
    have h4 := Real.exp_one_lt_d9
    linarith
  calc (1 - 2 * c) ^ ⌊u⌋₊ ≤ Real.exp (-2 * c) ^ ⌊u⌋₊ := pow_le_pow_left₀ h1 h2 _
    _ = Real.exp (-2 * c * (⌊u⌋₊ : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
    _ ≤ Real.exp (-2 * c * u + 2 * c) := Real.exp_le_exp.2 hlin
    _ = Real.exp (2 * c) * Real.exp (-2 * c * u) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ 4 * Real.exp (-2 * c * u) := mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le

/-- **Theorems A and B of the paper with one `Λ₀`.** The conclusion of Theorem A
(`AVRegularity.Providers.oc_global`) and the conclusion of `uniform_dissipation_exp` (Theorem B)
hold for the same `Λ₀`. -/
theorem oc_global_and_uniform_dissipation_exp (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∀ b : ℝ → Vec 2 → Vec 2,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) →
          (∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C : ℝ,
            ∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
            ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ →
              ∃ Θ : ℝ → Vec 2 → ℝ,
                ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2)
                  (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) ∧
                ∀ t ∈ Set.Icc (a + t₀) (a + T),
                  IsZ2Periodic (Θ t) ∧ Θ t =ᵐ[volume.restrict unitCube] θ t ∧
                  CsNormLe s (Θ t) (C * Real.sqrt (l2NormSq f))) ∧
          ∃ c : ℝ, 0 < c ∧
            (∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
              ∀ θ : ℝ → Vec 2 → ℝ, ∀ Dθ : ℝ → Vec 2 → Vec 2,
                IsWeakSolutionOnWith b κ a (a + 1) f θ Dθ →
                  c * l2NormSq (fun x => f x - ∫ y in unitCube, f y) ≤
                    κ * ∫ p in Set.Ioo a (a + 1) ×ˢ unitCube, vecNormSq (Dθ p.1 p.2)) ∧
            (∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
              ∀ t : ℝ, a < t → ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a t f θ →
                l2NormSq (fun x => θ t x - ∫ y in unitCube, f y) ≤
                  4 * Real.exp (-2 * c * (t - a)) *
                    l2NormSq (fun x => f x - ∫ y in unitCube, f y)) := by
  obtain ⟨Λ₀, hΛ₀, hA⟩ := Providers.oc_global α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ Φ hΦ b hb => ⟨hA Λ hΛ Φ hΦ b hb, ?_⟩⟩
  have hΛ128 : 128 ≤ Λ := hΛ₀.trans hΛ
  have hτ : (0 : ℝ) < 1 := one_pos
  obtain ⟨C, hC⟩ := hA Λ hΛ Φ hΦ b hb (1 / 2) 1 (by norm_num) (by norm_num)
  have hbH := Applications.limit_isHolderDivFree α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ128 Φ hΦ b hb
  have hbw : ∀ t₁ t₂ : ℝ, IsWindowDrift b t₁ t₂ := fun t₁ t₂ =>
    isWindowDrift_of_isHolderDivFreeVelocity hα₀ hbH t₁ t₂
  have hK : ∀ κ ∈ ocBandSet α q Λ, 0 < κ := fun κ hκ =>
    Assembly.TopWiring.pos_of_mem_ocBandSet (by omega) hκ
  have hreg : ∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
      ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + 1) f θ →
        ∃ Θ : Vec 2 → ℝ, Continuous Θ ∧ IsZ2Periodic Θ ∧
          Θ =ᵐ[volume.restrict unitCube] θ (a + 1) ∧
          CsNormLe s Θ (C * Real.sqrt (l2NormSq f)) := by
    intro a κ hκ f hf θ hθ
    obtain ⟨Θ, hΘc, hΘ⟩ := hC a κ hκ f hf θ hθ
    have hT : a + 1 ∈ Set.Icc (a + 1 / 2) (a + 1) := ⟨by linarith, le_rfl⟩
    obtain ⟨hp, he, hcs⟩ := hΘ (a + 1) hT
    refine ⟨Θ (a + 1), ?_, hp, he, hcs⟩
    have hmaps : Set.MapsTo (fun x : Vec 2 => (a + 1, x)) Set.univ
        (Set.Icc (a + 1 / 2) (a + 1) ×ˢ Set.univ) := fun x _ => ⟨hT, Set.mem_univ x⟩
    exact continuousOn_univ.1
      (hΘc.comp (Continuous.prodMk_right (a + 1)).continuousOn hmaps)
  have hD := uniform_dissipation_of_holder_regularity hs₀ hK hτ (fun a => hbw a (a + 1)) hreg
  set N : ℝ := (⌈max C 1 ^ (1 / s)⌉₊ : ℝ) with hN
  have hN1 : 1 ≤ N := by
    rw [hN]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (Real.rpow_pos_of_pos
      (lt_of_lt_of_le one_pos (le_max_right C 1)) _)).ne'
  have hN4 : 1 ≤ N ^ 4 := one_le_pow₀ hN1
  have hcpos : 0 < 1 / (4 * N ^ 4) := by positivity
  have hc4 : 1 / (4 * N ^ 4) ≤ 1 / 4 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hc2 : 0 ≤ 1 - 2 * (1 / (4 * N ^ 4)) := by linarith
  refine ⟨1 / (4 * N ^ 4), hcpos, fun a κ hκ f hf θ Dθ hθ => (hD a κ hκ f hf θ Dθ hθ).1,
    fun a κ hκ f hf t ht θ hθ => ?_⟩
  obtain ⟨Dθ, hθ'⟩ := hθ
  have hu : 0 < t - a := sub_pos.2 ht
  have e : a + (t - a) = t := by ring
  have hθ'' : IsWeakSolutionOnWith b κ a (a + (t - a)) f θ Dθ := by
    rw [e]
    exact hθ'
  have h := l2NormSq_sub_mean_le_pow_of_contraction (hK κ hκ) hτ hc2 hbw
    (fun a' f' hf' θ' Dθ' h' => (hD a' κ hκ f' hf' θ' Dθ' h').2) hu hf hθ''
  rw [e, div_one] at h
  have hX : 0 ≤ l2NormSq (fun x => f x - ∫ y in unitCube, f y) := by
    show 0 ≤ ∫ x in unitCube, (f x - ∫ y in unitCube, f y) ^ 2
    exact integral_nonneg fun x => sq_nonneg _
  exact h.trans (mul_le_mul_of_nonneg_right
    (pow_floor_le_four_mul_exp_dissipation (t - a) hcpos.le hc4) hX)


/-- **Uniform anomalous dissipation** (Theorem B of the paper: exponential decay with unit time).
For the construction parameters of Theorem A and `Λ ≥ Λ₀`, there is `c > 0` such that for every
`a ∈ ℝ`, `κ ∈ 𝒦` and `f ∈ L²(𝕋²)`, with `f̄ = ∫_{𝕋²} f`: (i) every weak solution on `[a, a + 1]`
with `θ(a) = f` has `κ ∫_a^{a+1} ∫_{𝕋²} |∇θ|² ≥ c ‖f - f̄‖₂²`; (ii) every weak solution on `[a, t]`,
`t > a`, with `θ(a) = f` has `‖θ(t) - f̄‖₂² ≤ 4 e^{-2c(t-a)} ‖f - f̄‖₂²`. -/
theorem uniform_dissipation_exp (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∀ b : ℝ → Vec 2 → Vec 2,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) →
          ∃ c : ℝ, 0 < c ∧
            (∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
              ∀ θ : ℝ → Vec 2 → ℝ, ∀ Dθ : ℝ → Vec 2 → Vec 2,
                IsWeakSolutionOnWith b κ a (a + 1) f θ Dθ →
                  c * l2NormSq (fun x => f x - ∫ y in unitCube, f y) ≤
                    κ * ∫ p in Set.Ioo a (a + 1) ×ˢ unitCube, vecNormSq (Dθ p.1 p.2)) ∧
            (∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
              ∀ t : ℝ, a < t → ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a t f θ →
                l2NormSq (fun x => θ t x - ∫ y in unitCube, f y) ≤
                  4 * Real.exp (-2 * c * (t - a)) *
                    l2NormSq (fun x => f x - ∫ y in unitCube, f y)) := by
  obtain ⟨Λ₀, hΛ₀, hall⟩ := oc_global_and_uniform_dissipation_exp α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  exact ⟨Λ₀, hΛ₀, fun Λ hΛ Φ hΦ b hb => (hall Λ hΛ Φ hΦ b hb).2⟩

end AVRegularity.PaperFacing

end
