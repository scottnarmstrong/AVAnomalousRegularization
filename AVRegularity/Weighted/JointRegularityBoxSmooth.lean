-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import AVRegularity.Weighted.PeriodicScalarZeroEnergy
public import AVRegularity.Statements.Intermediate.Families.JetSupOn
public import AVRegularity.Sobolev.Basic
public import AVRegularity.CycleEvolution.TimeEnergy
import AVRegularity.CycleEvolution.StrongUniqueness
public import AVRegularity.Statements.Intermediate.CycleComparison.IsBoxSmooth
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Filter
open scoped Topology
namespace AVRegularity.Weighted

/-! Dominated convergence of literal plane representatives in their Hilbert L2 classes. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem planeLp_tendsto_of_dominated_normSq
    (f : ℕ → Vec 2 → E) (g : Vec 2 → E)
    (hf : ∀ n, MemLp (f n) 2 (volume : Measure (Vec 2))) (hg : MemLp g 2 volume)
    (B : Vec 2 → ℝ) (hB : Integrable B volume)
    (hb : ∀ n, ∀ᵐ x ∂volume, ‖f n x - g x‖ ^ 2 ≤ B x)
    (hc : ∀ᵐ x ∂volume, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  have hi : Tendsto (fun n => ∫ x, ‖f n x - g x‖ ^ 2) atTop (𝓝 (∫ _x : Vec 2, (0 : ℝ))) :=
    tendsto_integral_of_dominated_convergence (F := fun n x => ‖f n x - g x‖ ^ 2)
      (f := fun _ => (0 : ℝ)) B
      (fun n => by
        convert ((hf n).sub hg).aestronglyMeasurable.norm.pow 2 using 1) hB
      (fun n => (hb n).mono (fun x hx => by
        change |‖f n x - g x‖ ^ 2| ≤ B x
        rw [abs_of_nonneg (sq_nonneg _)]
        exact hx))
        (hc.mono (fun x hx => by
        have hc' : Tendsto (fun _ : ℕ => g x) atTop (𝓝 (g x)) := tendsto_const_nhds
        simpa only [sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using (hx.sub hc').norm.pow 2))
  have he (n : ℕ) : ‖(hf n).toLp (f n) - hg.toLp g‖ ^ 2 = ∫ x, ‖f n x - g x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hf n).toLp (f n)) (hg.toLp g),
      (hf n).coeFn_toLp, hg.coeFn_toLp] with x hx hfx hgx
    rw [hx]
    change inner ℝ (((hf n).toLp (f n)) x - (hg.toLp g) x)
      (((hf n).toLp (f n)) x - (hg.toLp g) x) = _
    rw [hfx, hgx, real_inner_self_eq_norm_sq]
  have hn : Tendsto (fun n => ‖(hf n).toLp (f n) - hg.toLp g‖ ^ 2) atTop (𝓝 0) := by
    simpa only [he, integral_zero] using hi
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  simpa [Function.comp_def] using hs

end AVRegularity.Weighted
end
end

section
@[expose] public section
namespace AVRegularity.Weighted

/-! Abstract-real bookkeeping for multiplication by a polynomial and square-root moment weights. -/

theorem polynomial_square_root_moment_absorption (x b C : ℝ)
    (hx : 0 ≤ x) (hb : 0 ≤ b) (hC : 0 ≤ C) (hbound : x ^ 2 ≤ C ^ 2 * b)
    (n r : ℕ) : x ^ r * Real.sqrt (b ^ n) ≤ C ^ r * Real.sqrt (b ^ (n + r)) := by
  have hp : (x ^ r) ^ 2 ≤ (C ^ r) ^ 2 * b ^ r := by
    calc
      (x ^ r) ^ 2 = (x ^ 2) ^ r := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ (C ^ 2 * b) ^ r := pow_le_pow_left₀ (sq_nonneg x) hbound r
      _ = (C ^ r) ^ 2 * b ^ r := by rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm 2 r]
  have hsq : (x ^ r * Real.sqrt (b ^ n)) ^ 2 ≤
      (C ^ r * Real.sqrt (b ^ (n + r))) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (pow_nonneg hb n),
      Real.sq_sqrt (pow_nonneg hb (n + r))]
    calc
      (x ^ r) ^ 2 * b ^ n ≤ ((C ^ r) ^ 2 * b ^ r) * b ^ n :=
        mul_le_mul_of_nonneg_right hp (pow_nonneg hb n)
      _ = (C ^ r) ^ 2 * b ^ (n + r) := by rw [pow_add]; ring
  have hl : 0 ≤ x ^ r * Real.sqrt (b ^ n) := mul_nonneg (pow_nonneg hx _) (Real.sqrt_nonneg _)
  have hr : 0 ≤ C ^ r * Real.sqrt (b ^ (n + r)) := mul_nonneg (pow_nonneg hC _) (Real.sqrt_nonneg _)
  nlinarith only [hsq, hl, hr]

/-! Abstract real arithmetic choosing the common drift and metric radius reserve. -/

theorem exists_radius_absorption_reserve (A D : ℝ) (hA : 0 ≤ A) :
    ∃ L : ℝ, 1 ≤ L ∧ A * (1 + D ^ 2) / L ^ 2 ≤ 1 / 16 := by
  let L := 1 + 16 * A * (1 + D ^ 2)
  have hL : 1 ≤ L := by
    have hp : 0 ≤ 16 * A * (1 + D ^ 2) := by positivity
    dsimp only [L]
    linarith only [hp]
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  refine ⟨L, hL, ?_⟩
  apply (div_le_iff₀ (sq_pos_of_pos hLp)).mpr
  have hsq : L ≤ L ^ 2 := by nlinarith only [hL, sq_nonneg (L - 1)]
  dsimp only [L] at hsq ⊢
  linarith only [hsq]

/-! The original derivative envelopes gain explicit powers at the reserved radius. -/

theorem reducedRadius_metric_scale {r δ L : ℝ}
    (hL : 0 < L) (h : r * δ ≤ 1) : (r / L) * δ ≤ 1 / L := by
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right h hL.le

theorem reducedRadius_drift_scale {r B lam L : ℝ}
    (hlam : 0 < lam) (hL : 0 < L) (h : B * r / lam ≤ 1 / 2) :
    B * (r / L) / lam ≤ (1 / 2) / L := by
  have he : B * (r / L) / lam = (B * r / lam) / L := by
    field_simp
  rw [he]
  exact div_le_div_of_nonneg_right h hL.le

theorem reducedRadius_strain_scale {r a B L : ℝ}
    (h : a * B * r ^ 2 ≤ 1 / 8) :
    a * B * (r / L) ^ 2 ≤ (1 / 8) / L ^ 2 := by
  rw [div_pow, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right h (sq_nonneg L)

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.Weighted

/-! Almost-everywhere source representatives determine the literal spatial energy integrals. -/

variable {E : Type*} [NormedAddCommGroup E]

theorem weightedValueProduct_readout (q : Vec 2 → ℝ)
    (R u : Lp E 2 (volume : Measure (Vec 2))) (f g : Vec 2 → E)
    (hR : R =ᵐ[volume] fun x => -f x) (hu : u =ᵐ[volume] g) :
    (∫ x, q x * (‖R x‖ * ‖u x‖)) = ∫ x, q x * (‖f x‖ * ‖g x‖) := by
  apply integral_congr_ae
  filter_upwards [hR, hu] with x hx hy
  rw [hx, hy, norm_neg]

theorem weightedFluxEnergy_readout (q : Vec 2 → ℝ)
    (R : PiLp 2 (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2))))
    (f : Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (hR : ∀ k : Fin 2, R k =ᵐ[volume] fun x => f x k) :
    (∫ x, q x * ‖(WithLp.toLp 2 (fun k => R k x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) =
      ∫ x, q x * ‖f x‖ ^ 2 := by
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr hR] with x hx
  have he : (WithLp.toLp 2 (fun k => R k x) : PiLp 2 (fun _ : Fin 2 => E)) = f x := by
    apply PiLp.ext
    intro k
    exact hx k
  rw [he]

end AVRegularity.Weighted
end
end

section
@[expose] public section
namespace AVRegularity.Weighted

/-! The absorbed real factorial bound retains its production in extended real form. -/

theorem retained_factorial_energy_to_ennreal {e d i f A : ℝ}
    (he : 0 ≤ e) (hd : 0 ≤ d) (hi : 0 ≤ i) (hf : 0 ≤ f)
    (h : e + d / 2 ≤ A * (i + 16 * f)) :
    ENNReal.ofReal e + ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal d ≤
      ENNReal.ofReal A * (ENNReal.ofReal i + 16 * ENNReal.ofReal f) := by
  have hh := ENNReal.ofReal_le_ofReal h
  rw [mul_comm A] at hh
  have hhalf : d / 2 = (1 / 2 : ℝ) * d := by ring
  rw [hhalf, ENNReal.ofReal_add he (by positivity),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.ofReal_mul (add_nonneg hi (mul_nonneg (by norm_num) hf)),
    ENNReal.ofReal_add hi (mul_nonneg (by norm_num) hf),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)] at hh
  simpa only [ENNReal.ofReal_ofNat, mul_comm] using hh

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Weighted

/-! Scaling and increasing the polynomial degree preserve classical jet growth estimates. -/

theorem growing_scalar_jet_const_mul_bound (J p : ℕ) (f : Vec 2 → ℝ)
    (hf : ContDiff ℝ (J : ℕ) f) (A c : ℝ)
    (hb : ∀ j ≤ J, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ A * (1 + ‖x‖) ^ p) :
    ∀ j ≤ J, ∀ x, ‖iteratedFDeriv ℝ j (fun x => c * f x) x‖ ≤
      (|c| * A) * (1 + ‖x‖) ^ p := by
  intro j hj x
  have he : iteratedFDeriv ℝ j (fun x => c * f x) x = c • iteratedFDeriv ℝ j f x := by
    simpa only [smul_eq_mul] using iteratedFDeriv_const_smul_apply'
      (a := c) ((hf.of_le (by exact_mod_cast hj)).contDiffAt (x := x))
  rw [he, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hb j hj x) (abs_nonneg c)).trans_eq (by ring)

theorem growing_scalar_jet_increase_degree (J p q : ℕ) (hpq : p ≤ q)
    (f : Vec 2 → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ j ≤ J, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ A * (1 + ‖x‖) ^ p) :
    ∀ j ≤ J, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ A * (1 + ‖x‖) ^ q := by
  intro j hj x
  exact (hb j hj x).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by linarith [norm_nonneg x] : 1 ≤ 1 + ‖x‖) hpq) hA)

/-! Finite sums preserve a common polynomial growth bound for classical jets. -/

theorem growing_scalar_jet_sum_bound {ι : Type*} (s : Finset ι) (J p : ℕ)
    (f : ι → Vec 2 → ℝ) (hf : ∀ i ∈ s, ContDiff ℝ (J : ℕ) (f i))
    (A : ι → ℝ) (hb : ∀ i ∈ s, ∀ j ≤ J, ∀ x,
      ‖iteratedFDeriv ℝ j (f i) x‖ ≤ A i * (1 + ‖x‖) ^ p) :
    ∀ j ≤ J, ∀ x, ‖iteratedFDeriv ℝ j (fun x => ∑ i ∈ s, f i x) x‖ ≤
      (∑ i ∈ s, A i) * (1 + ‖x‖) ^ p := by
  intro j hj x
  rw [iteratedFDeriv_sum (fun i hi => (hf i hi).of_le (by exact_mod_cast hj))]
  simp only [Finset.sum_apply]
  calc
    ‖∑ i ∈ s, iteratedFDeriv ℝ j (f i) x‖ ≤
        ∑ i ∈ s, ‖iteratedFDeriv ℝ j (f i) x‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, A i * (1 + ‖x‖) ^ p := Finset.sum_le_sum (fun i hi => hb i hi j hj x)
    _ = _ := (Finset.sum_mul _ _ _).symm

end AVRegularity.Weighted
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.Weighted

/-! Nonnegative weight comparisons preserve the absorbed full interval production. -/

theorem scaled_retained_energy_transfer {e d ec dc i f i₀ f₀ C A : ℝ≥0∞}
    (he : e ≤ C * ec) (hd : d ≤ C * dc)
    (h : ec + ENNReal.ofReal (1 / 2 : ℝ) * dc ≤ A * (i + 16 * f))
    (hi : i ≤ C * i₀) (hf : f ≤ C * f₀) :
    e + ENNReal.ofReal (1 / 2 : ℝ) * d ≤ C * C * A * (i₀ + 16 * f₀) := by
  calc
    _ ≤ C * ec + ENNReal.ofReal (1 / 2 : ℝ) * (C * dc) :=
      add_le_add he (mul_le_mul' le_rfl hd)
    _ = C * (ec + ENNReal.ofReal (1 / 2 : ℝ) * dc) := by ring
    _ ≤ C * (A * (i + 16 * f)) := mul_le_mul' le_rfl h
    _ ≤ C * (A * (C * i₀ + 16 * (C * f₀))) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl (add_le_add hi (mul_le_mul' le_rfl hf)))
    _ = _ := by ring

end AVRegularity.Weighted
end
end

section
@[expose] public section
namespace AVRegularity.Weighted

/-! Abstract real arithmetic for the true flux and value commutator budgets. -/

theorem three_source_budget_merge {P R D F I c ν : ℝ}
    (hp : P ≤ 2 * (c * D) + 2 * F) (hr : R ≤ (ν / 4) * D) :
    I + 8 * P + 2 * R ≤ I + 16 * F + (16 * c + ν / 2) * D := by
  nlinarith only [hp, hr]

theorem retained_global_production {E D I F A c : ℝ}
    (hE : 0 ≤ E) (hD : 0 ≤ D) (hc : A * c ≤ 1 / 2)
    (h : E + D ≤ A * (I + 16 * F + c * D)) :
    E + D / 2 ≤ A * (I + 16 * F) ∧ D ≤ 2 * A * (I + 16 * F) := by
  have hsmall := mul_le_mul_of_nonneg_right hc hD
  constructor <;> nlinarith only [h, hsmall, hE]

theorem retained_full_interval_energy {Et Eb D I F A c : ℝ}
    (hb : 0 ≤ Eb) (hD : 0 ≤ D) (hc : A * c ≤ 1 / 2)
    (he : Et ≤ A * (I + 16 * F + c * D))
    (h : Eb + D ≤ A * (I + 16 * F + c * D)) :
    Et + D / 2 ≤ 3 * A * (I + 16 * F) := by
  have hsmall := mul_le_mul_of_nonneg_right hc hD
  have hprod := (retained_global_production hb hD hc h).2
  nlinarith only [he, hsmall, hprod]

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.Weighted

/-! Dominated convergence for the compact spatial tests of a bounded clipped energy. -/

theorem integral_spatial_cutoff_tendsto {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (χ : ℕ → α → ℝ) (f : α → ℝ)
    (hχm : ∀ n, AEStronglyMeasurable (χ n) μ)
    (hχ : ∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1)
    (hχlim : ∀ x, Tendsto (fun n => χ n x) atTop (𝓝 1))
    (hf : Integrable f μ) :
    Tendsto (fun n => ∫ x, χ n x ^ 2 * f x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
  · intro n
    exact (hχm n).pow 2 |>.mul hf.aestronglyMeasurable
  · exact hf.norm
  · intro n
    exact Eventually.of_forall (fun x => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hs : χ n x ^ 2 ≤ 1 := by nlinarith only [(hχ n x).1, (hχ n x).2]
      exact (mul_le_mul_of_nonneg_right hs (norm_nonneg _)).trans_eq (one_mul _))
  · exact Eventually.of_forall (fun x => by
      simpa only [one_pow, one_mul] using (hχlim x).pow 2 |>.mul_const (f x))

theorem spatial_cutoff_integrable_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (χ f : α → ℝ) (hχm : AEStronglyMeasurable χ μ)
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) :
    Integrable (fun x => χ x ^ 2 * f x) μ ∧
    0 ≤ (∫ x, χ x ^ 2 * f x ∂μ) ∧ (∫ x, χ x ^ 2 * f x ∂μ) ≤ ∫ x, f x ∂μ := by
  have hs x : χ x ^ 2 ≤ 1 := by nlinarith only [(hχ x).1, (hχ x).2]
  have hi : Integrable (fun x => χ x ^ 2 * f x) μ :=
    hf.bdd_mul (hχm.pow 2) (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hs x))
  refine ⟨hi, integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hf0 x)), ?_⟩
  apply integral_mono hi hf
  intro x
  exact (mul_le_mul_of_nonneg_right (hs x) (hf0 x)).trans_eq (one_mul _)

theorem cutoff_error_rate_tendsto_zero {C M : ℝ} :
    Tendsto (fun n : ℕ => 4096 * (((n : ℝ) + 1)⁻¹ * C) ^ 2 +
      16 * M * (((n : ℝ) + 1)⁻¹ * C)) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ * C) atTop (𝓝 0) := by
    simpa only [one_div, zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const C
  simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add] using
    (h.pow 2).const_mul 4096 |>.add (h.const_mul (16 * M))

end AVRegularity.Weighted
end
end

section
@[expose] public section
open MeasureTheory
namespace AVRegularity.Weighted

/-! Integrate the three nonnegative budgets in the compact weighted estimate. -/

theorem integral_three_term_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (L e f m : α → ℝ) (a b c : ℝ)
    (hL : Integrable L μ) (he : Integrable e μ) (hf : Integrable f μ) (hm : Integrable m μ)
    (h : ∀ᵐ x ∂μ, L x ≤ a * e x + b * f x + c * m x) :
    (∫ x, L x ∂μ) ≤ a * (∫ x, e x ∂μ) + b * (∫ x, f x ∂μ) + c * (∫ x, m x ∂μ) := by
  have hh := integral_mono_ae hL (((he.const_mul a).add (hf.const_mul b)).add (hm.const_mul c)) h
  change (∫ x, L x ∂μ) ≤ ∫ x, a * e x + b * f x + c * m x ∂μ at hh
  rw [integral_add (f := fun x => a * e x + b * f x) (g := fun x => c * m x)
    ((he.const_mul a).add (hf.const_mul b)) (hm.const_mul c),
    integral_add (f := fun x => a * e x) (g := fun x => b * f x)
      (he.const_mul a) (hf.const_mul b), integral_const_mul, integral_const_mul, integral_const_mul] at hh
  exact hh

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Filter Set
open scoped Topology
namespace AVRegularity.Weighted

/-! Uniform scalar remainder estimates give derivatives in the bounded coefficient norm. -/

theorem bounded_derivative_absolutelyContinuous
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (u du : ℝ → X) (hd : ∀ t, HasDerivAt u (du t) t)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ t, ‖du t‖ ≤ M) (a b : ℝ) :
    AbsolutelyContinuousOnInterval u a b := by
  have hlip : LipschitzWith ⟨M, hM⟩ u := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [dist_eq_norm, dist_eq_norm]
    exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun q (_ : q ∈ (univ : Set ℝ)) => (hd q).hasDerivWithinAt)
      (fun q _ => hb q) convex_univ (mem_univ t) (mem_univ s)
  exact hlip.lipschitzOnWith.absolutelyContinuousOnInterval

theorem scalar_remainder_le_of_derivative_lipschitz
    {f df : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (df t) t)
    {L : ℝ} (hL : 0 ≤ L) (hdf : ∀ s t, ‖df s - df t‖ ≤ L * ‖s - t‖)
    (s t : ℝ) : ‖f s - f t - (s - t) * df t‖ ≤ L * ‖s - t‖ ^ 2 := by
  let R : ℝ → ℝ := fun r => f r - f t - (r - t) * df t
  have hR (r : ℝ) : HasDerivAt R (df r - df t) r := by
    convert ((hf r).sub_const (f t)).sub
      (((hasDerivAt_id r).sub_const t).mul_const (df t)) using 1
    · rfl
    · simp
  have hb : ∀ r ∈ segment ℝ t s, ‖df r - df t‖ ≤ L * ‖s - t‖ := by
    intro r hr
    exact (hdf r t).trans (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hr) hL)
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r (_ : r ∈ segment ℝ t s) => (hR r).hasDerivWithinAt) hb
    (convex_segment t s) (left_mem_segment ℝ t s) (right_mem_segment ℝ t s)
  simpa only [R, sub_self, zero_mul, sub_zero, pow_two, mul_assoc] using hm

theorem boundedScalarFamily_hasDerivAt
    (c dc : ℝ → BoundedContinuousFunction (Homogenization.Vec 2) ℝ)
    (hf : ∀ t x, HasDerivAt (fun s => c s x) (dc t x) t)
    {L : ℝ} (hL : 0 ≤ L)
    (hdc : ∀ s t x, ‖dc s x - dc t x‖ ≤ L * ‖s - t‖) (t : ℝ) :
    HasDerivAt c (dc t) t := by
  rw [hasDerivAt_iff_tendsto]
  have hb (s : ℝ) : ‖c s - c t - (s - t) • dc t‖ ≤ L * ‖s - t‖ ^ 2 := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).2
    intro x
    change ‖c s x - c t x - (s - t) * dc t x‖ ≤ _
    exact scalar_remainder_le_of_derivative_lipschitz
      (fun r => hf r x) hL (fun r q => hdc r q x) s t
  have hu (s : ℝ) : ‖s - t‖⁻¹ * ‖c s - c t - (s - t) • dc t‖ ≤ L * ‖s - t‖ := by
    calc
      _ ≤ ‖s - t‖⁻¹ * (L * ‖s - t‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hb s) (by positivity)
      _ ≤ L * ‖s - t‖ := by
        by_cases h : ‖s - t‖ = 0
        · simp [h]
        · field_simp
          rfl
  have ht : Tendsto (fun s : ℝ => L * ‖s - t‖) (𝓝 t) (𝓝 0) := by
    convert ((continuous_const : Continuous (fun _ : ℝ => L)).mul
      (continuous_id.sub (continuous_const : Continuous (fun _ : ℝ => t))).norm).tendsto t using 1
    · rfl
    · simp
  exact squeeze_zero (fun s => by positivity) hu ht

end AVRegularity.Weighted
end
end

section
@[expose] public section
namespace AVRegularity.Weighted

/-! Exact finite Hilbert algebra of the weighted scalar diffusion test. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem weighted_scalar_production_split (v dq : Fin 2 → ℝ) (q : ℝ)
    (G : Matrix (Fin 2) (Fin 2) ℝ) (u : E) (du F : Fin 2 → E) :
    -(∑ k : Fin 2, v k * inner ℝ (du k) (q • u)) -
      (∑ k : Fin 2, inner ℝ ((∑ j : Fin 2, G k j • du j) + F k)
        (q • du k + dq k • u)) =
      -q * (∑ k : Fin 2, ∑ j : Fin 2, G k j * inner ℝ (du j) (du k)) -
        (∑ k : Fin 2, inner ℝ (F k) (q • du k + dq k • u)) -
        inner ℝ (∑ j : Fin 2, (q * v j + ∑ k : Fin 2, G k j * dq k) • du j) u := by
  simp only [Fin.sum_univ_two, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  ring
end

/-! The same reserve simultaneously makes the weighted metric and drift source coefficient absorbable. -/

theorem radius_reserve_source_coefficient {A D L r δ g : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hL : 1 ≤ L)
    (hreserve : A * (1 + D ^ 2) / L ^ 2 ≤ 1 / 16)
    (hr : 0 ≤ r) (hδ : 0 ≤ δ) (hg : 0 ≤ g) (hg4 : g ≤ 1 / 4) (hscale : r * δ ≤ 1) :
    A * (16 * (D * g * ((r / L) * δ)) ^ 2 + 1 / (2 * L ^ 2)) ≤ 1 / 2 := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hρδ := reducedRadius_metric_scale hLp hscale
  have hmetric : D * g * ((r / L) * δ) ≤ D / (4 * L) := by
    calc
      D * g * ((r / L) * δ) ≤ D * (1 / 4) * (1 / L) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hg4 hD) hρδ
          (mul_nonneg (div_nonneg hr hLp.le) hδ) (by positivity)
      _ = _ := by ring
  have hmetric0 : 0 ≤ D * g * ((r / L) * δ) := by positivity
  have hs := pow_le_pow_left₀ hmetric0 hmetric 2
  have hcost : 16 * (D * g * ((r / L) * δ)) ^ 2 + 1 / (2 * L ^ 2) ≤
      (1 + D ^ 2) / L ^ 2 := by
    have he : 16 * (D / (4 * L)) ^ 2 = D ^ 2 / L ^ 2 := by field_simp; ring
    have hb : 16 * (D * g * ((r / L) * δ)) ^ 2 ≤ D ^ 2 / L ^ 2 :=
      (mul_le_mul_of_nonneg_left hs (by norm_num)).trans_eq he
    have hh : 1 / (2 * L ^ 2) ≤ 1 / L ^ 2 := by
      apply one_div_le_one_div_of_le (sq_pos_of_pos hLp)
      nlinarith only [sq_nonneg L]
    calc
      _ ≤ D ^ 2 / L ^ 2 + 1 / L ^ 2 := add_le_add hb hh
      _ = _ := by ring
  exact ((mul_le_mul_of_nonneg_left hcost hA).trans_eq (by ring)).trans
    (hreserve.trans (by norm_num))

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization Set
namespace AVRegularity.Weighted

/-! Compact space-time scalar fields have differentiable bounded spatial slices. -/

def boundedPlaneSlice (f : ℝ × Vec 2 → ℝ) (hc : Continuous f)
    (M : ℝ) (hb : ∀ p, ‖f p‖ ≤ M) (t : ℝ) : BoundedContinuousFunction (Vec 2) ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => f (t, x), hc.comp (continuous_const.prodMk continuous_id)⟩ (2 * M)
    (fun x y => by
      rw [dist_eq_norm]
      exact (norm_sub_le (f (t, x)) (f (t, y))).trans (by linarith [hb (t,x), hb (t,y)]))

theorem compactScalarFamily_differentiable
    (f : ℝ × Vec 2 → ℝ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    ∃ (c dc : ℝ → BoundedContinuousFunction (Vec 2) ℝ),
      (∀ t x, c t x = f (t, x)) ∧
      (∀ t x, dc t x = fderiv ℝ f (t, x) (1, 0)) ∧
      (∀ t, HasDerivAt c (dc t) t) := by
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) :=
    (contDiff_succ_iff_fderiv (n := 1)).1 hf |>.2.2
  let D : ℝ × Vec 2 → ℝ := fun p => fderiv ℝ f p (1, 0)
  have hD : ContDiff ℝ 1 D := hdf.clm_apply contDiff_const
  have hsD : HasCompactSupport D := hs.fderiv_apply ℝ (1, 0)
  obtain ⟨M, hb⟩ := hf.continuous.bounded_above_of_compact_support hs
  obtain ⟨Md, hbd⟩ := hD.continuous.bounded_above_of_compact_support hsD
  obtain ⟨L, hL⟩ := (hD.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (hsD.fderiv ℝ)
  let c := boundedPlaneSlice f hf.continuous M hb
  let dc := boundedPlaneSlice D hD.continuous Md hbd
  refine ⟨c, dc, fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  intro t
  apply boundedScalarFamily_hasDerivAt c dc ?_ (le_max_left 0 L) ?_ t
  · intro q x
    have hp := (hasDerivAt_id q).prodMk (hasDerivAt_const q x)
    change HasDerivAt (fun s => f (s, x)) (fderiv ℝ f (q, x) (1, 0)) q
    convert (hf.differentiable (by norm_num) (q, x)).hasFDerivAt.comp_hasDerivAt q hp using 1
    rfl
  · intro s q x
    have hm := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun p (_ : p ∈ (univ : Set (ℝ × Vec 2))) => hD.differentiable (by norm_num) p)
      (fun p _ => (hL p).trans (le_max_right 0 L)) convex_univ
      (mem_univ (q,x)) (mem_univ (s,x))
    simpa [c, dc, boundedPlaneSlice, Prod.norm_def] using hm

end AVRegularity.Weighted
end
end

section
@[expose] public section
namespace AVRegularity.Weighted

/-! Combine the defect rate with diffusion coercivity and cutoff absorption. -/

theorem cutoff_pointwise_energy_absorption {χ η r M d u f q lam Q R : ℝ}
    (hχ : 0 ≤ χ) (hχ1 : χ ≤ 1) (hη : 0 ≤ η) (hM : 0 ≤ M)
    (hq : 0 ≤ q) (hr : r ^ 2 = lam)
    (hQ : (3 / 4 : ℝ) * d ^ 2 ≤ Q)
    (hR : R ≤ q * (8 * χ * η * M * u ^ 2 + 32 * χ * η * r * u ^ 2 +
      40 * χ * η * d * u + 2 * χ ^ 2 * r * d * u +
      2 * χ ^ 2 * f * d + 2 * χ ^ 2 * r * f * u + 8 * χ * η * f * u)) :
    2 * lam * χ ^ 2 * q * u ^ 2 + R - 2 * χ ^ 2 * q * Q + χ ^ 2 * q * d ^ 2 ≤
      18 * lam * χ ^ 2 * q * u ^ 2 + 8 * q * f ^ 2 +
        (4096 * η ^ 2 + 16 * M * η) * q * u ^ 2 := by
  have hy := mul_le_mul_of_nonneg_left (compact_weight_cutoff_young hχ hχ1 hη hM
    (r := r) (d := d) (u := u) (f := f)) hq
  have hc := mul_le_mul_of_nonneg_left hQ (show 0 ≤ 2 * χ ^ 2 * q by positivity)
  rw [hr] at hy
  nlinarith only [hy, hc, hR]

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Weighted

/-! Arbitrary bounded matrix entries act on Hilbert fibers with a fixed dimension-two cost. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem finiteMetricFlux_norm_le_four
    (G : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hG : ∀ k j, |G k j| ≤ M) (u : PiLp 2 (fun _ : Fin 2 => E)) :
    ‖finiteMetricFlux G u‖ ≤ 4 * M * ‖u‖ := by
  have hb k : ‖finiteMetricFlux G u k‖ ≤ (2 * M) * ‖u‖ := by
    change ‖∑ j : Fin 2, G k j • u j‖ ≤ _
    calc
      _ ≤ ∑ j : Fin 2, ‖G k j • u j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin 2, M * ‖u‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (hG k j) (PiLp.norm_apply_le u j) (norm_nonneg _) hM
      _ = _ := by simp; ring
  exact (piLp_two_norm_le_sum _).trans (by linarith only [hb 0, hb 1])

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.Weighted

/-! A finite essential coefficient envelope gives simultaneous spatial bounds at almost every time. -/

theorem jetSupOn_ae_norm_bound (dom : Set (ℝ × Vec 2)) (r q : ℕ)
    (f : ℝ → Vec 2 → Vec 2 → Vec 2) (hf : jetSupOn dom r q f ≠ ⊤) :
    ∀ᵐ t ∂volume, ∀ Y, (t, Y) ∈ dom → ∀ z,
      ‖iteratedFDeriv ℝ r (fun Y' => iteratedFDeriv ℝ q (f t Y') z) Y‖ ≤
        (jetSupOn dom r q f).toReal := by
  have hh : ∀ᵐ t ∂(volume : Measure ℝ),
      (⨆ Y ∈ {Y : Vec 2 | (t, Y) ∈ dom}, ⨆ z : Vec 2,
        ‖iteratedFDeriv ℝ r (fun Y' => iteratedFDeriv ℝ q (f t Y') z) Y‖ₑ) ≤
        jetSupOn dom r q f := ae_le_essSup (μ := (volume : Measure ℝ))
    (f := fun t => ⨆ Y ∈ {Y : Vec 2 | (t, Y) ∈ dom}, ⨆ z : Vec 2,
      ‖iteratedFDeriv ℝ r (fun Y' => iteratedFDeriv ℝ q (f t Y') z) Y‖ₑ)
  filter_upwards [hh] with t ht
  intro Y hY z
  have hs : ‖iteratedFDeriv ℝ r (fun Y' => iteratedFDeriv ℝ q (f t Y') z) Y‖ₑ ≤
      jetSupOn dom r q f := by
    calc
      _ ≤ ⨆ Y ∈ {Y : Vec 2 | (t, Y) ∈ dom}, ⨆ z : Vec 2,
          ‖iteratedFDeriv ℝ r (fun Y' => iteratedFDeriv ℝ q (f t Y') z) Y‖ₑ :=
        le_iSup_of_le Y (le_iSup_of_le hY (le_iSup_of_le z le_rfl))
      _ ≤ _ := ht
  simpa only [toReal_enorm] using ENNReal.toReal_mono hf hs

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Finite coefficient regularity suffices to identify its ordered derivative tensor. -/

def orderedScalarDerivative (c : Vec 2 → ℝ) : (j : ℕ) → DerivativeWord2 j → Vec 2 → ℝ
  | 0, _ => c
  | j + 1, w => fun x => fderiv ℝ (orderedScalarDerivative c j (Fin.init w)) x
      (basisVec (w (Fin.last j)))

/-- For a `C^j` function, the ordered derivative along a word is the iterated derivative along the
basis vectors of the reversed word (finite regularity suffices). -/
theorem orderedScalarDerivative_eq_iterated
    (C : Vec 2 → ℝ) (j : ℕ) (hC : ContDiff ℝ (j : ℕ) C)
    (w : DerivativeWord2 j) (x : Vec 2) :
    orderedScalarDerivative C j w x =
      iteratedFDeriv ℝ j C x (fun k => basisVec (w k.rev)) := by
  induction j generalizing C x with
  | zero => simp only [orderedScalarDerivative, iteratedFDeriv_zero_apply]
  | succ j ih =>
    have hCj : ContDiff ℝ (j : ℕ) C := hC.of_le (by exact_mod_cast Nat.le_succ j)
    have he : orderedScalarDerivative C j (Fin.init w) = fun y =>
        iteratedFDeriv ℝ j C y (fun k => basisVec (Fin.init w k.rev)) :=
      funext (fun y => ih C hCj (Fin.init w) y)
    rw [orderedScalarDerivative, he]
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ j C) x :=
      hC.differentiable_iteratedFDeriv (m := j) (by exact_mod_cast Nat.lt_succ_self j) x
    have hder := hd.iteratedFDeriv_succ_apply_left'
      (m := fun k : Fin (j + 1) => basisVec (w k.rev))
    have ht : Fin.tail (fun k : Fin (j + 1) => basisVec (w k.rev)) =
        (fun k : Fin j => basisVec (Fin.init w k.rev)) := by
      funext k
      change basisVec (w k.succ.rev) = basisVec (w k.rev.castSucc)
      rw [Fin.rev_succ]
    rw [ht] at hder
    simpa only [Fin.rev_zero] using hder.symm

theorem orderedScalarDerivative_norm_le
    (C : Vec 2 → ℝ) (j : ℕ) (hC : ContDiff ℝ (j : ℕ) C)
    (w : DerivativeWord2 j) (x : Vec 2) :
    ‖orderedScalarDerivative C j w x‖ ≤ ‖iteratedFDeriv ℝ j C x‖ := by
  rw [orderedScalarDerivative_eq_iterated C j hC w x]
  have hh := (iteratedFDeriv ℝ j C x).le_opNorm (fun k => basisVec (w k.rev))
  simpa only [show ∀ k : Fin j, ‖basisVec (w k.rev)‖ = 1 by
    intro k; simp [basisVec, Pi.norm_single], Finset.prod_const_one, mul_one] using hh

end AVRegularity.Weighted
end
end

section
@[expose] public section
open AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Finite stored-word sums split into derivative order and word sums. -/

theorem storedWord_sum_weighted {K : ℕ} (c : Fin (K + 1) → ℝ)
    (f : JetIndex2 K → ℝ) :
    (∑ α : JetIndex2 K, c α.1 * f α) =
      ∑ j : Fin (K + 1), c j * ∑ w : DerivativeWord2 j.val, f ⟨j, w⟩ := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  exact (Finset.mul_sum Finset.univ (fun w : DerivativeWord2 j.val => f ⟨j, w⟩) (c j)).symm

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace AVRegularity.Weighted

/-! Time regularity depends only on the trajectory and production on the time window. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem strongTime_congr_on_window {a b : ℝ} (hab : a ≤ b)
    {u du v dv : ℝ → H} (h : AVRegularity.CycleEvolution.StrongTimeRegularity a b u du)
    (huv : ∀ t ∈ Icc a b, u t = v t) (hd : ∀ t ∈ Icc a b, du t = dv t) :
    AVRegularity.CycleEvolution.StrongTimeRegularity a b v dv := by
  refine ⟨h.ac.congr (fun t ht => huv t (by simpa only [uIcc_of_le hab] using ht)), ?_⟩
  have hder := h.derivative
  rw [uIcc_of_le hab, ← restrict_Ioo_eq_restrict_Icc] at hder ⊢
  filter_upwards [hder, ae_restrict_mem measurableSet_Ioo] with t ht hmem
  rw [hd t ⟨hmem.1.le, hmem.2.le⟩] at ht
  apply ht.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hmem] with s hs
  exact (huv s ⟨hs.1.le, hs.2.le⟩).symm

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Filter
open AVRegularity.CycleEvolution
namespace AVRegularity.Weighted

/-! Time-dependent bounded spatial multipliers act on strong Hilbert time curves. -/

variable {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Operator evaluation preserves absolute continuity on compact time intervals. -/
theorem absolutelyContinuous_clm_apply {a b : ℝ}
    {A : ℝ → H →L[ℝ] F} {u : ℝ → H}
    (hA : AbsolutelyContinuousOnInterval A a b)
    (hu : AbsolutelyContinuousOnInterval u a b) :
    AbsolutelyContinuousOnInterval (fun t => A t (u t)) a b := by
  obtain ⟨C, hC⟩ := hA.exists_bound
  obtain ⟨D, hD⟩ := hu.exists_bound
  unfold AbsolutelyContinuousOnInterval at hA hu ⊢
  apply squeeze_zero' ?_ ?_ (by simpa using (hu.const_mul C).add (hA.const_mul D))
  · exact Filter.Eventually.of_forall (fun _ => Finset.sum_nonneg (fun _ _ => dist_nonneg))
  rw [eventually_inf_principal]
  filter_upwards with (n, I) hnI
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hleft := hnI.1 i hi |>.1
  have hright := hnI.1 i hi |>.2
  calc
    dist (A (I i).1 (u (I i).1)) (A (I i).2 (u (I i).2)) ≤
        dist (A (I i).1 (u (I i).1)) (A (I i).1 (u (I i).2)) +
          dist (A (I i).1 (u (I i).2)) (A (I i).2 (u (I i).2)) := dist_triangle _ _ _
    _ ≤ C * dist (u (I i).1) (u (I i).2) + D * dist (A (I i).1) (A (I i).2) := by
      apply add_le_add
      · rw [dist_eq_norm, ← map_sub, dist_eq_norm]
        exact ((A (I i).1).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hC _ hleft) (norm_nonneg _))
      · rw [dist_eq_norm, ← sub_apply, dist_eq_norm, mul_comm D]
        exact ((A (I i).1 - A (I i).2).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (hD _ hright) (norm_nonneg _))

/-- A time-dependent multiplier has the ordinary operator product derivative. -/
theorem strongTimeRegularity_clm_apply {a b : ℝ}
    {A dA : ℝ → H →L[ℝ] F} {u du : ℝ → H}
    (hA : AbsolutelyContinuousOnInterval A a b)
    (hdA : ∀ᵐ t ∂volume.restrict (uIcc a b), HasDerivAt A (dA t) t)
    (hu : StrongTimeRegularity a b u du) :
    StrongTimeRegularity a b (fun t => A t (u t))
      (fun t => A t (du t) + dA t (u t)) := by
  refine ⟨absolutelyContinuous_clm_apply hA hu.ac, ?_⟩
  filter_upwards [hdA, hu.derivative] with t ht hut
  convert ht.clm_apply hut using 1
  simp only [add_comm]

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.Weighted

/-! Splitting a genuine flux source costs two copies of each weighted square. -/

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]

theorem weightedSource_integral_add_le {μ : Measure X}
    (q : X → ℝ) (hq : AEStronglyMeasurable q μ)
    (hq0 : ∀ x, 0 ≤ q x) {M : ℝ} (hb : ∀ᵐ x ∂μ, ‖q x‖ ≤ M)
    (f g : X → E) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, q x * ‖f x + g x‖ ^ 2 ∂μ) ≤
      2 * (∫ x, q x * ‖f x‖ ^ 2 ∂μ) +
      2 * (∫ x, q x * ‖g x‖ ^ 2 ∂μ) := by
  have hi := hf.norm.integrable_sq.bdd_mul hq hb
  have hj := hg.norm.integrable_sq.bdd_mul hq hb
  have hij := (bochnerSource_memLp_add hf hg).norm.integrable_sq.bdd_mul hq hb
  have hn (x : X) : ‖f x + g x‖ ^ 2 ≤ 2 * ‖f x‖ ^ 2 + 2 * ‖g x‖ ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (f x) (g x)) 2
    nlinarith only [h, sq_nonneg (‖f x‖ - ‖g x‖)]
  calc
    _ ≤ ∫ x, 2 * (q x * ‖f x‖ ^ 2) + 2 * (q x * ‖g x‖ ^ 2) ∂μ := by
      apply integral_mono hij ((hi.const_mul 2).add (hj.const_mul 2))
      intro x
      have h := mul_le_mul_of_nonneg_left (hn x) (hq0 x)
      exact h.trans_eq (by dsimp only [Pi.add_apply]; ring)
    _ = _ := by rw [integral_add (hi.const_mul 2) (hj.const_mul 2),
      integral_const_mul, integral_const_mul]


theorem weightedSource_integral_sum {μ : Measure X} {ι : Type*} [Fintype ι]
    (q : X → ℝ) (hq : AEStronglyMeasurable q μ)
    {M : ℝ} (hb : ∀ᵐ x ∂μ, ‖q x‖ ≤ M)
    (f : ι → X → E) (hf : ∀ i, MemLp (f i) 2 μ) :
    (∫ x, q x * (∑ i, ‖f i x‖ ^ 2) ∂μ) =
      ∑ i, ∫ x, q x * ‖f i x‖ ^ 2 ∂μ := by
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum _ (fun i _ => (hf i).norm.integrable_sq.bdd_mul hq hb)


theorem weightedSource_sum_add_le {μ : Measure X} {ι : Type*} [Fintype ι]
    (q : X → ℝ) (hq : AEStronglyMeasurable q μ) (hq0 : ∀ x, 0 ≤ q x)
    {M : ℝ} (hb : ∀ᵐ x ∂μ, ‖q x‖ ≤ M)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (f g : ι → X → E)
    (hf : ∀ i, MemLp (f i) 2 μ) (hg : ∀ i, MemLp (g i) 2 μ) :
    (∑ i, c i * (∫ x, q x * ‖f i x + g i x‖ ^ 2 ∂μ)) ≤
      2 * (∑ i, c i * (∫ x, q x * ‖f i x‖ ^ 2 ∂μ)) +
      2 * (∑ i, c i * (∫ x, q x * ‖g i x‖ ^ 2 ∂μ)) := by
  calc
    _ ≤ ∑ i, (2 * (c i * (∫ x, q x * ‖f i x‖ ^ 2 ∂μ)) +
        2 * (c i * (∫ x, q x * ‖g i x‖ ^ 2 ∂μ))) := by
      apply Finset.sum_le_sum
      intro i _
      exact (mul_le_mul_of_nonneg_left
        (weightedSource_integral_add_le q hq hq0 hb (f i) (g i) (hf i) (hg i))
        (hc i)).trans_eq (by ring)
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Weighted

/-! A product of linear coordinates has derivative growth bounded by its degree. -/

theorem linear_product_jet_growth {ι : Type*} [DecidableEq ι]
    (J : ℕ) (s : Finset ι) (L : ι → Vec 2 →L[ℝ] ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ j ≤ J, ∀ x,
      ‖iteratedFDeriv ℝ j (fun x => ∏ i ∈ s, L i x) x‖ ≤ A * (1 + ‖x‖) ^ s.card := by
  induction s using Finset.induction with
  | empty =>
    refine ⟨1, zero_le_one, ?_⟩
    intro j _ x
    cases j with
    | zero => simp
    | succ j => simp [iteratedFDeriv_succ_const]
  | insert i s hi ih =>
    obtain ⟨A, hA, hAb⟩ := ih
    let C : ℝ := (∑ j ∈ Finset.range (J + 1), (J.choose j : ℝ)) * ‖L i‖ * A
    have hC : 0 ≤ C := by dsimp [C]; positivity
    refine ⟨C, hC, ?_⟩
    intro j hj x
    have he : (fun x => ∏ k ∈ insert i s, L k x) =
        fun x => L i x * ∏ k ∈ s, L k x := by
      funext x
      rw [Finset.prod_insert hi]
    rw [he, Finset.card_insert_of_notMem hi]
    have hg : ContDiff ℝ (J : ℕ) (fun x => ∏ k ∈ s, L k x) :=
      contDiff_prod (fun k _ => (L k).contDiff)
    have hh := growing_scalar_jet_product_bound J 1 s.card (L i)
      (fun x => ∏ k ∈ s, L k x) (L i).contDiff hg ‖L i‖ A (norm_nonneg _) hA
      (fun k _ x => by simpa only [pow_one] using linear_iteratedFDeriv_growth (L i) k x)
      hAb j hj x
    simpa only [C, Nat.add_comm] using hh

theorem coordinate_monomial_jet_growth {r : ℕ} (J : ℕ)
    (w : Fin r → Fin 2) (δ : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ j ≤ J, ∀ x : Vec 2,
      ‖iteratedFDeriv ℝ j (fun x => ∏ i, δ * x (w i)) x‖ ≤ A * (1 + ‖x‖) ^ r := by
  have hh := linear_product_jet_growth J Finset.univ
    (fun i : Fin r => δ • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (w i))
  simpa only [smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    Finset.card_univ, Fintype.card_fin] using hh

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace AVRegularity.Weighted

/-! Dominated energy production retains integrability along with the endpoint identity. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem energy_increment_integrable_of_dominated_approximation {a b : ℝ} (hab : a ≤ b)
    (u du : ℕ → ℝ → H) (h : ∀ n, AVRegularity.CycleEvolution.StrongTimeRegularity a b (u n) (du n))
    (ua ub : H) (ha : Tendsto (fun n => u n a) atTop (𝓝 ua))
    (hb : Tendsto (fun n => u n b) atTop (𝓝 ub))
    (production bound : ℝ → ℝ) (hbound : IntegrableOn bound (Ioc a b))
    (hdom : ∀ n, ∀ᵐ t ∂volume.restrict (Ioc a b), ‖2 * inner ℝ (u n t) (du n t)‖ ≤ bound t)
    (hlim : ∀ᵐ t ∂volume.restrict (Ioc a b),
      Tendsto (fun n => 2 * inner ℝ (u n t) (du n t)) atTop (𝓝 (production t))) :
    (‖ub‖ ^ 2 - ‖ua‖ ^ 2 = ∫ t in a..b, production t) ∧
      IntervalIntegrable production volume a b := by
  have hmeas n : AEStronglyMeasurable (fun t => 2 * inner ℝ (u n t) (du n t))
      (volume.restrict (Ioc a b)) := by
    simpa only [intervalIntegrable_iff, uIoc_of_le hab] using
      (h n).energy_integrable.aestronglyMeasurable
  have hpm : AEStronglyMeasurable production (volume.restrict (Ioc a b)) :=
    aestronglyMeasurable_of_tendsto_ae _ hmeas hlim
  have hp : IntegrableOn production (Ioc a b) := by
    apply hbound.mono' hpm
    have hd : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ n, ‖2 * inner ℝ (u n t) (du n t)‖ ≤ bound t :=
      ae_all_iff.mpr hdom
    filter_upwards [hd, hlim] with t ht hl
    exact le_of_tendsto hl.norm (Filter.Eventually.of_forall ht)
  exact ⟨AVRegularity.CycleEvolution.energy_increment_of_dominated_approximation
    hab u du h ua ub ha hb production bound hbound hdom hlim,
    by simpa only [intervalIntegrable_iff, uIoc_of_le hab] using hp⟩

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Weighted

/-! Existential polynomial bounds assemble over a finite family of derivative orders. -/

theorem finite_scalar_growth_sum_exists {T ι : Type*} (s : Finset ι) (J p : ℕ)
    (f : ι → T → Vec 2 → ℝ) (d : ι → ℕ)
    (hd : ∀ i ∈ s, d i ≤ p) (hf : ∀ i ∈ s, ∀ t, ContDiff ℝ (J : ℕ) (f i t))
    (hb : ∀ i ∈ s, ∃ A : ℝ, 0 ≤ A ∧ ∀ t j, j ≤ J → ∀ x,
      ‖iteratedFDeriv ℝ j (f i t) x‖ ≤ A * (1 + ‖x‖) ^ d i) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t j, j ≤ J → ∀ x,
      ‖iteratedFDeriv ℝ j (fun x => ∑ i ∈ s, f i t x) x‖ ≤ A * (1 + ‖x‖) ^ p := by
  classical
  have hex (i : ι) : ∃ A : ℝ, 0 ≤ A ∧ ∀ t j, j ≤ J → ∀ x,
      i ∈ s → ‖iteratedFDeriv ℝ j (f i t) x‖ ≤ A * (1 + ‖x‖) ^ d i := by
    by_cases hi : i ∈ s
    · obtain ⟨A, hA, hAb⟩ := hb i hi
      exact ⟨A, hA, fun t j hj x _ => hAb t j hj x⟩
    · exact ⟨0, le_rfl, fun _ _ _ _ hh => False.elim (hi hh)⟩
  choose A hA hAb using hex
  refine ⟨∑ i ∈ s, A i, Finset.sum_nonneg (fun i _ => hA i), ?_⟩
  intro t
  exact growing_scalar_jet_sum_bound s J p (fun i => f i t) (fun i hi => hf i hi t) A
    (fun i hi => growing_scalar_jet_increase_degree J (d i) p (hd i hi) (f i t)
      (A i) (hA i) (fun j hj x => hAb i t j hj x hi))

/-! The joint regularity required of a cycle letter supplies its rectangular slow-fast reserve. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem joint_partialIteratedFDeriv_left_contDiff (n r : ℕ)
    (f : Vec 2 × Vec 2 → E) (hf : ContDiff ℝ (n + r : ℕ) f) :
    ContDiff ℝ (n : ℕ)
      (fun p : Vec 2 × Vec 2 => iteratedFDeriv ℝ r (fun X => f (X, p.2)) p.1) := by
  have hh := joint_partialIteratedFDeriv_right_contDiff n r (fun p => f (p.2, p.1))
    (hf.comp (contDiff_snd.prodMk contDiff_fst))
  exact hh.comp (contDiff_snd.prodMk contDiff_fst)

theorem isBoxSmooth_of_joint_contDiff (sX sZ : ℕ)
    (f : Vec 2 → Vec 2 → E)
    (hf : ContDiff ℝ (sX + sZ : ℕ) (Function.uncurry f)) :
    IsBoxSmooth sX sZ f := by
  refine ⟨?_, ?_, ?_⟩
  · intro X
    exact (hf.comp (contDiff_const.prodMk contDiff_id)).of_le
      (by exact_mod_cast Nat.le_add_left sZ sX)
  · intro b hb z
    have hh := joint_partialIteratedFDeriv_right_contDiff sX b (Function.uncurry f)
      (hf.of_le (by exact_mod_cast Nat.add_le_add_left hb sX))
    exact hh.comp (contDiff_id.prodMk contDiff_const)
  · intro a b ha hb
    have hh := joint_partialIteratedFDeriv_right_contDiff a b (Function.uncurry f)
      (hf.of_le (by exact_mod_cast Nat.add_le_add ha hb))
    have hj := joint_partialIteratedFDeriv_left_contDiff 0 a
      (fun p : Vec 2 × Vec 2 => iteratedFDeriv ℝ b (f p.1) p.2)
      (by simpa only [Nat.zero_add, Function.uncurry_def] using hh)
    exact hj.continuous
end

end AVRegularity.Weighted
end
end
