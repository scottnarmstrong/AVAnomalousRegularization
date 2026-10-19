-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.TransverseModeFactor
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep
public import AVRegularity.CycleWords.GeometryScalarComponentFlux
import AVRegularity.CycleReference.ChartIntegrandAlgebra
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleWords.GeometryScalarCoefficient
public import AVRegularity.CycleWords.CellAffineHomeomorph
import AVRegularity.CycleEvolution.FibreCoefficientLinearSeries

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleWords

/-! A finite coordinate synthesis recovers strong measurability of the full slow derivative. -/

open AVRegularity.CycleComparison.Lift
variable {T : Type*} [MeasurableSpace T]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem fderiv_parameter_stronglyMeasurable (f : T → Vec 2 → E)
    (hm : ∀ x, Measurable (fun t => f t x)) (hd : ∀ t, Differentiable ℝ (f t))
    (x : Vec 2) : StronglyMeasurable (fun t => fderiv ℝ (f t) x) := by
  let S := fun v : Fin 2 → E => ∑ q : Fin 2,
    (ContinuousLinearMap.proj q : Vec 2 →L[ℝ] ℝ).smulRight (v q)
  have hS : Continuous S := by
    apply continuous_finsetSum
    intro q _
    exact (ContinuousLinearMap.smulRightL ℝ (Vec 2) E
      (ContinuousLinearMap.proj q)).continuous.comp (continuous_apply q)
  have hv : StronglyMeasurable (fun t (q : Fin 2) => fderiv ℝ (f t) x (basisVec q)) :=
    (measurable_pi_iff.mpr (fun q => fderiv_apply_parameter_measurable f hm hd x (basisVec q))).stronglyMeasurable
  have he : (fun t => fderiv ℝ (f t) x) =
      fun t => S (fun q => fderiv ℝ (f t) x (basisVec q)) := by
    funext t
    apply ContinuousLinearMap.ext
    intro ξ
    conv_lhs => rw [vec_eq_sum_basis ξ]
    simp [S, map_smul, ContinuousLinearMap.smulRight_apply]
  rw [he]
  simpa only [Function.comp_def] using! hS.comp_stronglyMeasurable hv

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The coupled solution class, the scalar geometry chain and the chart weights see the metric only
on their time windows: they transfer to any metric agreeing with it there. -/

theorem coupledWeakIdentity_congr_flux {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {μ : Measure (Vec 2)} {ν t₀ t : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {u₀ f φ : Vec 2 → H} {dφ : Fin 2 → Vec 2 → H} {du : ℝ → Fin 2 → Vec 2 → H}
    {flux flux' F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)} {g : ℝ → Vec 2 → H}
    (hf : ∀ s ∈ Set.Ioc t₀ t, flux' s = flux s)
    (h : CoupledWeakIdentity μ ν t₀ t v u₀ f φ dφ du flux F g) :
    CoupledWeakIdentity μ ν t₀ t v u₀ f φ dφ du flux' F g := by
  unfold CoupledWeakIdentity at h ⊢
  dsimp only at h ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, fun s hs => by rw [hf s hs]; exact h3 s hs, ?_, ?_⟩
  · exact h4.congr_fun (fun s hs => by simp only [hf s hs]) measurableSet_Ioc
  · rw [h5]
    exact setIntegral_congr_fun measurableSet_Ioc (fun s hs => by simp only [hf s hs])

theorem isCoupledWeakSolutionPlane_congr_coeff {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {ν t₀ t₁ : ℝ} {v : ℝ → Vec 2 → Vec 2} {D : ℕ} {K : ι → ℕ}
    {A A' : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i))}
    {f : ∀ i, PlaneHk Set.univ (K i) (h i)}
    {F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
    {g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)}
    {u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)} {w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)}
    (hA : ∀ i i' d, ∀ s ∈ Set.Icc t₀ t₁, A' i i' d s = A i i' d s)
    (hsol : IsCoupledWeakSolutionPlane ν t₀ t₁ v D K A f F g u w) :
    IsCoupledWeakSolutionPlane ν t₀ t₁ v D K A' f F g u w := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hsol
  refine ⟨h1, h2, h3, h4, fun i t ht φ => coupledWeakIdentity_congr_flux ?_ (h5 i t ht φ)⟩
  intro s hs
  have hs' : s ∈ Set.Icc t₀ t₁ := ⟨hs.1.le, hs.2.trans ht.2⟩
  funext x
  simp only [hA i _ _ s hs']

theorem isPlaneChainFrom_geometryScalarData_congr {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {D : ℕ} {G G' : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {κ : Fin 1 → ι → ℕ} {a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {f : ∀ (j : Fin 1) (x : ι), PlaneHk Set.univ (κ j x) (h x)}
    {F : ∀ (j : Fin 1) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (PiLp 2 (fun _ : Fin 2 => h x))}
    {u : ∀ (j : Fin 1) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x)}
    {w : ∀ (j : Fin 1) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)}
    (hGG : ∀ t ∈ Set.Icc a b, G' t = G t)
    (hsol : IsPlaneChainFrom (geometryScalarData D G) κ a b v f F u w) :
    IsPlaneChainFrom (geometryScalarData D G') κ a b v f F u w := by
  unfold IsPlaneChainFrom at hsol ⊢
  refine isCoupledWeakSolutionPlane_congr_coeff (fun i i' d s hs => ?_) hsol
  funext z
  simp only [planeChainCoefficient, geometryScalarData, hGG s hs]

/-- Chart weights for `G` are chart weights for any `G'` agreeing with `G` on their window. -/
def chartWeightsOfEqOn {G G' : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {v : ℝ → Vec 2 → Vec 2} {t₀ S ϖ : ℝ} {zc : Vec 2} {M : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v t₀ S ϖ zc M Cw) (hGG : ∀ t ∈ Set.Icc t₀ (t₀ + S), G' t = G t) :
    ChartWeights G' v t₀ S ϖ zc M Cw where
  W := W.W
  Phi := W.Phi
  lam := W.lam
  smooth := W.smooth
  pos := W.pos
  comparable := W.comparable
  defect := fun m hm t ht z => by rw [hGG t ht]; exact W.defect m hm t ht z
  bound := W.bound
  lam_bound := W.lam_bound

end AVRegularity.CycleWords
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.CycleWords

/-! Sobolev caps keep every nonempty edge of the original word. -/

theorem nonempty_letter_order_le {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}
    {π : ι → ℝ} {L : CycleLetter ι h D} {dom : Set (ℝ × Vec 2)} {J H : ℕ}
    (hL : IsCycleLetter π L dom J H) (x y : ι) (o : Finset.Icc 2 D)
    (hne : L.edge x y o ≠ []) : o.1 ≤ L.order := by
  by_contra hn
  exact hne (hL.edge_order x y o (Nat.lt_of_not_ge hn))

theorem cappedWordSlots_nonempty_edge_admissible {ι : Type*} [Fintype ι]
    {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    {N D : ℕ} (κ : Fin (N + 1) → ι → ℕ) (K : ℕ) (d : Fin N → ℕ)
    (letters : Fin N → CycleLetter ι h D) {π : ι → ℝ} {dom : Set (ℝ × Vec 2)}
    {J H : ℕ} (hL : ∀ j, IsCycleLetter π (letters j) dom J H)
    (hd : ∀ j, (letters j).order = d j)
    (hκ : ∀ j x y (o : Finset.Icc 2 D), (letters j).edge x y o ≠ [] →
      κ j.succ x + o.1 ≤ κ j.castSucc y + 2)
    (j : Fin N) (x y : ι) (o : Finset.Icc 2 D) (hne : (letters j).edge x y o ≠ []) :
    o.1 ∈ admissibleOrders (fun p : Fin (N + 1) × ι => cappedWordSlots κ K d p.1 p.2)
      D (j.succ, x) (j.castSucc, y) := by
  apply Finset.mem_filter.mpr
  refine ⟨o.2, ?_⟩
  exact cappedWordSlots_edge_compatible κ K d j x y o.1
    (Finset.mem_Icc.mp o.2).1
    (by rw [← hd j]; exact nonempty_letter_order_le (hL j) x y o hne)
    (hκ j x y o hne)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The first chronological scalar component has no preceding letter source. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D N : ℕ}

theorem wordChainPreviousFlux_zero (letters : Fin N → CycleLetter ι h D)
    (X0 : Vec 2) (δ : ℝ) (κ : Fin (N + 1) → ι → ℕ)
    (U : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (x : ι) (t : ℝ) : wordChainPreviousFlux letters X0 δ κ U (0, x) t = 0 := by
  classical
  funext z
  simp [wordChainPreviousFlux]
end

/-! The actual scalar metric flux splits exactly into its central metric,
positive Taylor insertion, and omitted Taylor remainder. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def nativeMetricInsertionFlux {K : ℕ} (A : Matrix (Fin 2) (Fin 2) ℝ)
    (U : PlaneHk Set.univ (K + 1) E) (z : Vec 2) : PiLp 2 (fun _ : Fin 2 => E) :=
  WithLp.toLp 2 (fun k => ∑ l : Fin 2, A k l •
    U.toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => l⟩ z)

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem geometryScalarFlux_taylor_split (D : ℕ) (hD : 2 ≤ D) (Ks : ℕ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (κ : Fin 1 → ι → ℕ)
    (U : ∀ p : Fin 1 × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (i : Fin 1 × ι) (t : ℝ) (z : Vec 2) :
    geometryScalarFlux D G κ U i t z = geometryScalarFlux D (fun t _ => G t 0) κ U i t z +
      nativeMetricInsertionFlux (metricTaylor 1 Ks G t 0 z) (U i) z +
      nativeMetricInsertionFlux (G t z - metricTaylor 0 Ks G t 0 z) (U i) z := by
  apply PiLp.ext
  intro k
  rw [PiLp.add_apply, PiLp.add_apply, geometryScalarFlux_eq D hD, geometryScalarFlux_eq D hD]
  change (∑ l : Fin 2, (G t z - 1) k l • (U i).toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => l⟩ z) =
    (∑ l : Fin 2, (G t 0 - 1) k l • (U i).toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => l⟩ z) +
    (∑ l : Fin 2, metricTaylor 1 Ks G t 0 z k l • (U i).toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => l⟩ z) +
    (∑ l : Fin 2, (G t z - metricTaylor 0 Ks G t 0 z) k l •
      (U i).toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => l⟩ z)
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [← add_smul, ← add_smul]
  apply congrArg (fun a : ℝ => a • (U i).toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => l⟩ z)
  have ht := taylorSlow_zero_eq_constant_add_positive Ks (fun y => G t y k l) 0 z
  simp only [Matrix.sub_apply, metricTaylor, sub_zero]
  linarith only [ht]
end

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! The quarter-pulse buffers around an enlarged odd pulse lie in the genuine quiet gap. -/

theorem odd_pulse_unit_window_active_unique {τ t : ℝ} (hτ : 0 < τ)
    {k j : ℤ} (hk : Odd k) (hj : Odd j)
    (hwindow : |t - (k : ℝ) * τ| ≤ τ)
    (hactive : (j : ℝ) * τ - (2 / 3) * τ < t ∧
      t < (j : ℝ) * τ + (2 / 3) * τ) : k = j := by
  obtain ⟨a, ha⟩ := hk
  obtain ⟨b, hb⟩ := hj
  obtain ⟨hlo, hhi⟩ := abs_le.mp hwindow
  by_contra hne
  rcases lt_or_gt_of_ne hne with hkj | hjk
  · have hgap : k + 2 ≤ j := by omega
    have hgapR : (k : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast hgap
    have hmul := mul_le_mul_of_nonneg_right hgapR hτ.le
    linarith
  · have hgap : j + 2 ≤ k := by omega
    have hgapR : (j : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hgap
    have hmul := mul_le_mul_of_nonneg_right hgapR hτ.le
    linarith

theorem odd_pulses_zero_in_quiet_annulus {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {k : ℤ} (hk : Odd k) {t : ℝ}
    (hlo : 3 / 4 * ocTau α q Λ m ≤ |t - (k : ℝ) * ocTau α q Λ m|)
    (hhi : |t - (k : ℝ) * ocTau α q Λ m| ≤ ocTau α q Λ m) :
    ∀ j : ℤ, Odd j → ocPulse α q Λ ζ m j t = 0 := by
  intro j hj
  by_contra hp
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  have hd := CycleReference.pulse_nonzero_center_distance hΛ hζ hp
  have he := odd_pulse_unit_window_active_unique hτ hk hj hhi hd
  subst j
  have ha : |t - (k : ℝ) * ocTau α q Λ m| < 2 / 3 * ocTau α q Λ m :=
    abs_lt.mpr ⟨by linarith [hd.1], by linarith [hd.2]⟩
  linarith

theorem ocCellDrift_zero_in_pulse_quiet_annulus {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2) {k : ℤ} (hk : Odd k) {t : ℝ}
    (hlo : 3 / 4 * ocTau α q Λ m ≤ |ocEll q Λ m ν ^ 2 * t - (k : ℝ) * ocTau α q Λ m|)
    (hhi : |ocEll q Λ m ν ^ 2 * t - (k : ℝ) * ocTau α q Λ m| ≤ ocTau α q Λ m)
    (z : Vec 2) : ocCellDrift α q Λ ζ m ν y₀ t z = 0 := by
  have hz := odd_pulses_zero_in_quiet_annulus hΛ hζ hk hlo hhi
  simp only [ocCellDrift, CycleReference.pulseStreamVel_eq_zero_of_quiet hz, smul_zero]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization Filter Set
namespace AVRegularity.CycleWords

/-! Polynomially growing parameter jets may be differentiated under a finite integral. -/

variable {T : Type*} [MeasurableSpace T]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem parameter_integral_hasFDerivAt_growth (μ : Measure T) [IsFiniteMeasure μ]
    (f : T → Vec 2 → E) (hm : ∀ x, Measurable (fun t => f t x))
    (hd : ∀ t, Differentiable ℝ (f t)) (C₀ C₁ : ℝ) (hC₁ : 0 ≤ C₁) (p : ℕ)
    (hb₀ : ∀ t x, ‖f t x‖ ≤ C₀ * (1 + ‖x‖) ^ p)
    (hb₁ : ∀ t x, ‖fderiv ℝ (f t) x‖ ≤ C₁ * (1 + ‖x‖) ^ p) (x : Vec 2) :
    HasFDerivAt (fun y => ∫ t, f t y ∂μ)
      (∫ t, fderiv ℝ (f t) x ∂μ) x := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Metric.ball x 1)
    (μ := μ) (F := fun y t => f t y) (F' := fun y t => fderiv ℝ (f t) y)
    (bound := fun _ => C₁ * (2 + ‖x‖) ^ p) (Metric.ball_mem_nhds x (by norm_num))
  · exact Eventually.of_forall (fun y => (hm y).aestronglyMeasurable)
  · exact (integrable_const (C₀ * (1 + ‖x‖) ^ p)).mono' (hm x).aestronglyMeasurable
      (ae_of_all μ (fun t => hb₀ t x))
  · exact (fderiv_parameter_stronglyMeasurable f hm hd x).aestronglyMeasurable
  · apply ae_of_all
    intro t y hy
    have hn : ‖y‖ ≤ 1 + ‖x‖ := by
      have hdist : ‖y - x‖ ≤ 1 := by
        simpa only [dist_eq_norm] using (Metric.mem_ball.mp hy).le
      calc
        ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by simpa only [sub_add_cancel] using norm_add_le (y - x) x
        _ ≤ _ := add_le_add hdist le_rfl
    exact (hb₁ t y).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith : 1 + ‖y‖ ≤ 2 + ‖x‖) p) hC₁)
  · exact integrable_const _
  · exact ae_of_all μ (fun t y _ => (hd t y).hasFDerivAt)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! A finite global bound for the actual cell drift. -/

theorem cellDrift_component_abs_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (y₀ z : Vec 2) (i : Fin 2) :
    |ocCellDrift α q Λ ζ m ν y₀ t z i| ≤
      |ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m| *
        |2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹| := by
  classical
  by_cases hp : ∃ k : ℤ, Odd k ∧ ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) ≠ 0
  · obtain ⟨k, hk, hp⟩ := hp
    have hr := CycleReference.ocPulse_range (α := α) (q := q) (m := m) (Λ := Λ)
      hζ k (ocEll q Λ m ν ^ 2 * t)
    simp only [ocCellDrift, CycleReference.pulseStreamVel_eq_active hΛ hζ hk hp,
      Pi.smul_apply, smul_eq_mul, abs_mul]
    rw [abs_of_nonneg hr.1]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc
      _ ≤ 1 * |ocShearVel α q Λ m k (y₀ + ocEpsilon q Λ m • z) i| :=
        mul_le_mul_of_nonneg_right hr.2 (abs_nonneg _)
      _ ≤ _ := by
        rw [one_mul]
        simpa only [abs_mul] using ocShearVel_component_abs_le (α := α) (q := q)
          (Λ := Λ) (m := m) hk (y₀ + ocEpsilon q Λ m • z) i
  · have hz : ∀ k : ℤ, Odd k → ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) = 0 := by
      intro k hk
      by_contra hn
      exact hp ⟨k, hk, hn⟩
    simp only [ocCellDrift, CycleReference.pulseStreamVel_eq_zero_of_quiet hz,
      smul_zero, Pi.zero_apply, abs_zero]
    positivity

theorem cellDrift_norm_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (yc : Vec 2) :
    ∃ M : ℝ, ∀ t z, ‖ocCellDrift α q Λ ζ m ν yc t z‖ ≤ M := by
  refine ⟨|ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m| *
    |2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹|, ?_⟩
  intro t z
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  simpa only [Real.norm_eq_abs] using cellDrift_component_abs_bound hΛ hζ ν t yc z j

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open scoped ENNReal NNReal BigOperators
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Uniform Taylor majorants construct bounded time coefficients without time regularity. -/

theorem fibreBoundedTimeCoefficient_sup_lt_top (a : ℕ × ℕ → ℝ → ℂ)
    (R : ℝ≥0) (hR : 0 < R)
    (ha : (∑' p, fibreCoefficientWeight (R : ENNReal) p * ⨆ t, ‖a p t‖ₑ) < ⊤)
    (p : ℕ × ℕ) : (⨆ t, ‖a p t‖ₑ) < ⊤ := by
  have hp := (ENNReal.le_tsum (f := fun q =>
    fibreCoefficientWeight (R : ENNReal) q * ⨆ t, ‖a q t‖ₑ) p).trans_lt ha
  apply ENNReal.lt_top_of_mul_ne_top_right hp.ne
  exact pow_ne_zero _ (by exact_mod_cast hR.ne')

theorem fibreBoundedTimeCoefficient_mem (a : ℕ × ℕ → ℝ → ℂ)
    (R : ℝ≥0) (hR : 0 < R)
    (ha : (∑' p, fibreCoefficientWeight (R : ENNReal) p * ⨆ t, ‖a p t‖ₑ) < ⊤)
    (p : ℕ × ℕ) : Memℓp (a p) ⊤ := by
  have ht := fibreBoundedTimeCoefficient_sup_lt_top a R hR ha p
  apply memℓp_infty
  refine ⟨(⨆ t, ‖a p t‖ₑ).toReal, ?_⟩
  rintro _ ⟨t, rfl⟩
  have hb := ENNReal.toReal_mono ht.ne (le_iSup (fun t => ‖a p t‖ₑ) t)
  simpa only [enorm, ENNReal.coe_toReal, coe_nnnorm] using hb

def fibreBoundedTimeCoefficient (a : ℕ × ℕ → ℝ → ℂ)
    (R : ℝ≥0) (hR : 0 < R)
    (ha : (∑' p, fibreCoefficientWeight (R : ENNReal) p * ⨆ t, ‖a p t‖ₑ) < ⊤)
    (p : ℕ × ℕ) : BoundedComplexTime :=
  ⟨a p, fibreBoundedTimeCoefficient_mem a R hR ha p⟩

theorem fibreBoundedTimeCoefficient_enorm_le (a : ℕ × ℕ → ℝ → ℂ)
    (R : ℝ≥0) (hR : 0 < R)
    (ha : (∑' p, fibreCoefficientWeight (R : ENNReal) p * ⨆ t, ‖a p t‖ₑ) < ⊤)
    (p : ℕ × ℕ) : ‖fibreBoundedTimeCoefficient a R hR ha p‖ₑ ≤ ⨆ t, ‖a p t‖ₑ := by
  have ht := fibreBoundedTimeCoefficient_sup_lt_top a R hR ha p
  have hn : ‖fibreBoundedTimeCoefficient a R hR ha p‖ ≤ (⨆ t, ‖a p t‖ₑ).toReal := by
    apply lp.norm_le_of_forall_le ENNReal.toReal_nonneg
    intro t
    change ‖a p t‖ ≤ (⨆ t, ‖a p t‖ₑ).toReal
    have hb := ENNReal.toReal_mono ht.ne (le_iSup (fun t => ‖a p t‖ₑ) t)
    simpa only [enorm, ENNReal.coe_toReal, coe_nnnorm] using hb
  rw [← ofReal_norm]
  exact (ENNReal.ofReal_le_ofReal hn).trans_eq (ENNReal.ofReal_toReal ht.ne)

theorem fibreBoundedTimeCoefficient_weighted_summable (a : ℕ × ℕ → ℝ → ℂ)
    (R : ℝ≥0) (hR : 0 < R)
    (ha : (∑' p, fibreCoefficientWeight (R : ENNReal) p * ⨆ t, ‖a p t‖ₑ) < ⊤) :
    Summable (fun p => ‖fibreBoundedTimeCoefficient a R hR ha p‖ * (R : ℝ) ^ (p.1 + p.2)) := by
  apply fibreUniformMajorant_weighted_summable
    (fun p (_ : ℝ) => fibreBoundedTimeCoefficient a R hR ha p) R _ 0
  simp only [iSup_const]
  exact (ENNReal.tsum_le_tsum (fun p => mul_le_mul' le_rfl
    (fibreBoundedTimeCoefficient_enorm_le a R hR ha p))).trans_lt ha

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Exact collapse of the scalar chain's dependent coupling sum to the metric flux. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

def geometryActualFlux (D : ℕ) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (edge : ConstituentEdges D h) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin 1 → ι → ℕ)
    (w : ∀ p : Fin 1 × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (i : Fin 1 × ι) (t : ℝ) (z : Vec 2) : PiLp 2 (fun _ : Fin 2 => h i.2) :=
  ∑ i' : Fin 1 × ι, ∑ d : admissibleOrders (fun p => κ p.1 p.2) D i i',
    planeChainCoefficient (geometryActualData G edge X0 δ) κ i i' d t z
      (WithLp.toLp 2 fun word : DerivativeWord2 (d.val - 1) =>
        (w i').toFunction.jet
          ⟨⟨d.val - 1, by
            have hd := (Finset.mem_filter.mp d.property).2
            dsimp only at hd
            omega⟩, word⟩ z)

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem geometryActualFlux_split (D : ℕ) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (edge : ConstituentEdges D h) (X0 : Vec 2) (δ : ℝ) (κ : Fin 1 → ι → ℕ)
    (w : ∀ p : Fin 1 × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (i : Fin 1 × ι) (t : ℝ) (z : Vec 2) :
    geometryActualFlux D G edge X0 δ κ w i t z = geometryScalarFlux D G κ w i t z +
      ∑ i' : Fin 1 × ι, ∑ d : admissibleOrders (fun p => κ p.1 p.2) D i i',
        slowEvalCoefficient (fun f z => f (X0 + δ • z))
          (edge i.2 i'.2 ⟨d.1, (Finset.mem_filter.mp d.2).1⟩) t z
          (WithLp.toLp 2 (fun word : DerivativeWord2 (d.1 - 1) =>
            planeJetOrder (w i') (d.1 - 1) word z)) := by
  classical
  unfold geometryActualFlux geometryScalarFlux
  simp_rw [geometryActualCoefficient_split, add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i' _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  congr 2
  apply PiLp.ext
  intro word
  dsimp only
  have hd := (Finset.mem_filter.mp d.2).2
  dsimp only at hd
  rw [planeJetOrder_eq_stored (show d.1 - 1 ≤ κ i'.1 i'.2 + 1 by omega)]

end AVRegularity.CycleWords
end
end
