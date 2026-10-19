-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleDamping.TensorError
public import AVRegularity.CycleEvolution.FibreCoefficientLinearSeries
public import AVRegularity.CycleEvolution.CellDriftComplexMultiplier
import AVRegularity.CycleEvolution.CellSpatialEnergy
import AVRegularity.CycleReference.ChartTestTransport
import AVRegularity.CoupledEnergy.Galerkin.PlainVariationalEnergy
import AVRegularity.CycleReference.TransitionZero
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
import AVRegularity.Construction.Scales.Times
import AVRegularity.Construction.Stream.NextAdmissible
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

section
@[expose] public section
open Homogenization MeasureTheory
namespace AVRegularity.CycleDamping

/-! The quadratic near-identity hypothesis controls each symmetric matrix entry. -/

theorem metric_entry_error {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {g : ℝ} (hG : IsCellMetric G) (hg : IsMetricNearIdentity G g)
    (t : ℝ) (z : Vec 2) (i j : Fin 2) :
    |(G t z - (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j| ≤ g := by
  let A := G t z - (1 : Matrix (Fin 2) (Fin 2) ℝ)
  have h0 := hg t z ![1, 0]
  have h1 := hg t z ![0, 1]
  have hp := hg t z ![1, 1]
  have hm := hg t z ![1, -1]
  change |∑ i, ∑ j, (![1, 0] : Vec 2) i * A i j * (![1, 0] : Vec 2) j| ≤ _ at h0
  change |∑ i, ∑ j, (![0, 1] : Vec 2) i * A i j * (![0, 1] : Vec 2) j| ≤ _ at h1
  change |∑ i, ∑ j, (![1, 1] : Vec 2) i * A i j * (![1, 1] : Vec 2) j| ≤ _ at hp
  change |∑ i, ∑ j, (![1, -1] : Vec 2) i * A i j * (![1, -1] : Vec 2) j| ≤ _ at hm
  have hs : A 1 0 = A 0 1 := by
    dsimp [A]
    simp only [Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0),
      Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), sub_zero]
    exact (hG.2.2.1 t z).apply 0 1
  norm_num [Fin.sum_univ_two] at h0 h1 hp hm
  have h01 : |A 0 1| ≤ g := by
    rw [hs] at hp hm
    rcases abs_le.mp hp with ⟨hpl, hpu⟩
    rcases abs_le.mp hm with ⟨hml, hmu⟩
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  change |A i j| ≤ g
  fin_cases i <;> fin_cases j
  · exact h0
  · exact h01
  · change |A 1 0| ≤ g
    rw [hs]
    exact h01
  · exact h1

theorem metric_sup_error {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {g : ℝ} (hG : IsCellMetric G) (hg : IsMetricNearIdentity G g) :
    cellMetricSupNorm (G - fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) ≤
      ENNReal.ofReal g := by
  apply iSup_le
  intro t
  apply iSup_le
  intro z
  apply iSup_le
  intro i
  apply iSup_le
  intro j
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (metric_entry_error hG hg t z i j)

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleDamping

/-! Integrated quadratic coercivity survives an entrywise complex tensor error. -/

/-- Real matrix quadratic forms agree with their complex bilinear lifts. -/
theorem real_matrix_quadratic_cast (A : Matrix (Fin 2) (Fin 2) ℝ) (x : Vec 2) :
    (∑ i, ∑ j, (x i : ℂ) * (A i j : ℂ) * (x j : ℂ)) =
      ((vecDot x (A.mulVec x) : ℝ) : ℂ) := by
  simp [vecDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- Entrywise error gives an integrated upper bound for the negative quadratic symbol. -/
theorem quadratic_integral_of_entry_error
    (D : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (J : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (x : Vec 2) (a b c δ : ℝ) (hab : a ≤ b) (hδ : 0 ≤ δ)
    (hD : IntervalIntegrable (fun t => -(∑ i, ∑ j,
      (x i : ℂ) * D t i j * (x j : ℂ))) volume a b)
    (hJ : IntervalIntegrable (fun t => vecDot x ((J t).mulVec x)) volume a b)
    (herr : ∀ t ∈ Set.uIoc a b, ∀ i j, ‖D t i j - (J t i j : ℂ)‖ ≤ δ)
    (hcoercive : c * (b - a) * vecDot x x ≤
      ∫ t in a..b, vecDot x ((J t).mulVec x)) :
    (∫ t in a..b, -(∑ i, ∑ j, (x i : ℂ) * D t i j * (x j : ℂ))).re ≤
      -(c - 2 * δ) * (b - a) * vecDot x x := by
  let Q := fun t => -(∑ i, ∑ j, (x i : ℂ) * D t i j * (x j : ℂ))
  let P := fun t => ((vecDot x ((J t).mulVec x) : ℝ) : ℂ)
  have hP : IntervalIntegrable P volume a b := ⟨hJ.1.ofReal, hJ.2.ofReal⟩
  have hdiff : ∀ t ∈ Set.uIoc a b,
      ‖Q t + P t‖ ≤ 2 * δ * vecDot x x := by
    intro t ht
    have he : Q t + P t = -(∑ i, ∑ j, (x i : ℂ) *
        (D t i j - (J t i j : ℂ)) * (x j : ℂ)) := by
      dsimp only [Q, P]
      rw [← real_matrix_quadratic_cast]
      simp only [Fin.sum_univ_two]
      ring
    rw [he, norm_neg]
    simpa only [vecDot, dotProduct, ← pow_two] using
      quadratic_entry_error (fun i j => D t i j - (J t i j : ℂ)) x δ hδ (herr t ht)
  have hbnd := interval_remainder_real_bound (fun t => Q t + P t) a b
    (2 * δ * vecDot x x) hab hdiff
  rw [intervalIntegral.integral_add hD hP, Complex.add_re] at hbnd
  have hcast : (∫ t in a..b, P t).re = ∫ t in a..b, vecDot x ((J t).mulVec x) := by
    dsimp only [P]
    rw [intervalIntegral.integral_ofReal]
    rfl
  rw [hcast] at hbnd
  change (∫ t in a..b, Q t).re ≤ _
  nlinarith only [hbnd, hcoercive]

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleDamping

/-! The first Taylor forcing is the scaled drift with multiplier `-i`.
This is a calculation in the triangular coefficient recursion. -/

/-- At first order every lower correction coefficient is the zero coefficient. -/
theorem fibreCoefficientSource_direction (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (D : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (hD : D 0 = 0) (j : Fin 2) :
    CycleEvolution.fibreCoefficientSource η v D (CycleEvolution.cellJetDirection j) =
      fun t x => -Complex.I * ((Real.sqrt η * v t x j : ℝ) : ℂ) := by
  have hz : D (0, 0) = 0 := hD
  funext t x
  fin_cases j <;>
    simp [CycleEvolution.fibreCoefficientSource, CycleEvolution.fibreCoefficientLinearSource,
      CycleEvolution.fibreCoefficientLinearTerm, CycleEvolution.fibreCoefficientQuadraticSource,
      CycleEvolution.fibreCoefficientQuadraticTerm, CycleEvolution.fibreCoefficientDirections,
      CycleEvolution.fibreCoefficientPrevious, CycleEvolution.fibreCoefficientPairs,
      CycleEvolution.fibreCoefficientComplement, CycleEvolution.cellJetDirection,
      CycleEvolution.fibreCoordinateFrequency_coupling, Finset.sum_filter, Fin.sum_univ_two,
      hz, cellValue, Complex.ofReal_mul]

/-- No gradient flux appears in the first-order graph equation. -/
theorem fibreCoefficientFlux_direction (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (D : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (hD : D 0 = 0) (j : Fin 2) :
    CycleEvolution.fibreCoefficientFlux η G D (CycleEvolution.cellJetDirection j) = 0 := by
  have hz : D (0, 0) = 0 := hD
  funext t x
  apply PiLp.ext
  intro k
  fin_cases j <;>
    simp [CycleEvolution.fibreCoefficientFlux, CycleEvolution.fibreCoefficientDirections,
      CycleEvolution.fibreCoefficientPrevious, CycleEvolution.cellJetDirection,
      fibreGraphFlux, Finset.sum_filter, Fin.sum_univ_two, hz, cellValue]

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization
open scoped ENNReal
namespace AVRegularity.CycleDamping

/-! Conditional mark accumulation; the local drops are discharged by the genuine core theorem. -/

theorem admissible_decay_of_core_drops {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (ν B Θ d ta T : ℝ) (hd : 0 < d) (hΘ : 1 ≤ Θ)
    (hL : 0 < ocEll q Λ m ν ^ 2)
    (hadm : IsOCAdmissibleInterval α q Λ ζ m ν B Θ d ta T)
    (N : ℝ → ℝ≥0∞) (hN : AntitoneOn N (Icc ta (ta + T))) (j : Fin 2)
    (hdrop : ∀ x : ℝ, ta ≤ x → x + d * ocEll q Λ m ν ^ 2 ≤ ta + T →
      ∀ n : ℤ, n % 4 = (if j = 0 then 3 else 1) →
      IsOCCompleteCore α q Λ m (ocLabel α q Λ m n) n →
      ((n : ℝ) - 1 / 3) * ocTau α q Λ m ≤ x →
      x + d * ocEll q Λ m ν ^ 2 ≤ ((n : ℝ) + 1 / 3) * ocTau α q Λ m →
      N (x + d * ocEll q Λ m ν ^ 2) ≤ (1 / 2 : ℝ≥0∞) * N x) :
    N (ta + T) ≤ ENNReal.ofReal
      (Real.exp (-(((1 - Real.exp (-2)) / 288) * Real.log 2 / d) *
        (T / ocEll q Λ m ν ^ 2))) * N ta := by
  have hT : 0 ≤ T := by
    have hr := hΘ.trans hadm.2.1
    have hm := (le_div_iff₀ hL).mp hr
    linarith only [hm, hL]
  obtain ⟨marks, hcount, hin, hsep⟩ := hadm.2.2.2 j
  have hdm : 0 < d * ocEll q Λ m ν ^ 2 := mul_pos hd hL
  have hc := marked_contraction_of_local_bounds N (d * ocEll q Λ m ν ^ 2) hdm
    (1 / 2 : ℝ≥0∞) marks ta (ta + T) (by linarith) hN
    (fun x hx => ⟨(hin x hx).1, (hin x hx).2.1⟩) (by
      intro x hx y hy hxy
      rcases hsep x hx y hy (ne_of_lt hxy) with hs | hs
      · exact hs
      · exfalso; linarith only [hxy, hs, hdm]) (by
      intro x hx
      obtain ⟨ha, hb, n, hn, hcore, hlo, hhi⟩ := hin x hx
      exact hdrop x ha hb n hn hcore hlo hhi)
  have hp := half_power_decay ((1 - Real.exp (-2)) / 288)
    (T / ocEll q Λ m ν ^ 2) d marks.card hcount
  exact hc.trans (by simpa only [mul_comm] using mul_le_mul_right hp (N ta))

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleDamping

/-! Uniform cubic bounds for all finite homogeneous symbol tails. -/

theorem fibreHomogeneous_zero_low_degree (lam : ℕ × ℕ → ℝ → ℂ)
    (hlow : ∀ p : ℕ × ℕ, p.1 + p.2 ≤ 1 → ∀ t, lam p t = 0)
    (ξ : Fin 2 → ℂ) (n : ℕ) (hn : n ≤ 1) (t : ℝ) :
    fibreHomogeneous lam ξ n t = 0 := by
  simp only [fibreHomogeneous, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [hlow p ((Finset.HasAntidiagonal.mem_antidiagonal.mp hp).le.trans hn) t, mul_zero]

/-- One geometric estimate bounds every truncation independently of its order. -/
theorem homogeneous_cubic_tail_bound (lam : ℕ × ℕ → ℝ → ℂ) (ξ : Fin 2 → ℂ)
    (ξ₀ Cg : ℝ) (hξ₀ : 0 < ξ₀) (hCg : 0 ≤ Cg)
    (hsmall : fibreNorm ξ ≤ ξ₀ / 4)
    (hb : ∀ n t, ‖fibreHomogeneous lam ξ n t‖ ≤
      Cg * (2 / ξ₀) ^ n * fibreNorm ξ ^ n) (N : ℕ) (t : ℝ) :
    ‖∑ n ∈ Finset.range N, fibreHomogeneous lam ξ (n + 3) t‖ ≤
      (2 * Cg * (2 / ξ₀) ^ 3) * fibreNorm ξ ^ 3 := by
  let ρ := (2 / ξ₀) * fibreNorm ξ
  have hx : 0 ≤ fibreNorm ξ := by unfold fibreNorm; positivity
  have hρ : 0 ≤ ρ := mul_nonneg (by positivity) hx
  have hhalf : ρ ≤ 1 / 2 := by
    dsimp [ρ]
    have hh := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 2 / ξ₀ by positivity)
    calc
      _ ≤ (2 / ξ₀) * (ξ₀ / 4) := hh
      _ = 1 / 2 := by field_simp; norm_num
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖fibreHomogeneous lam ξ (n + 3) t‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, Cg * ρ ^ (n + 3) := by
      apply Finset.sum_le_sum
      intro n _
      simpa only [ρ, mul_pow, mul_assoc] using hb (n + 3) t
    _ ≤ 2 * Cg * ρ ^ 3 := geometric_cubic_tail_finset hρ hhalf hCg N
    _ = _ := by dsimp only [ρ]; rw [mul_pow]; ring

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleDamping

/-! The actual finite Taylor truncations have a common cubic remainder. -/

theorem finite_symbol_quadratic_remainder_bound (lam : ℕ × ℕ → ℝ → ℂ) (ξ : Fin 2 → ℂ)
    (ξ₀ Cg : ℝ) (hξ₀ : 0 < ξ₀) (hCg : 0 ≤ Cg)
    (hsmall : fibreNorm ξ ≤ ξ₀ / 4)
    (hlow : ∀ p : ℕ × ℕ, p.1 + p.2 ≤ 1 → ∀ t, lam p t = 0)
    (hb : ∀ n t, ‖fibreHomogeneous lam ξ n t‖ ≤
      Cg * (2 / ξ₀) ^ n * fibreNorm ξ ^ n)
    (N : ℕ) (hN : 2 ≤ N) (t : ℝ) :
    ‖(∑ n ∈ Finset.range (N + 1), fibreHomogeneous lam ξ n t) -
      fibreHomogeneous lam ξ 2 t‖ ≤
      (2 * Cg * (2 / ξ₀) ^ 3) * fibreNorm ξ ^ 3 := by
  have hp : (∑ n ∈ Finset.range 3, fibreHomogeneous lam ξ n t) =
      fibreHomogeneous lam ξ 2 t := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [fibreHomogeneous_zero_low_degree lam hlow ξ 0 (by omega) t,
      fibreHomogeneous_zero_low_degree lam hlow ξ 1 (by omega) t]
    simp
  have he : N + 1 = 3 + (N - 2) := by omega
  rw [he, Finset.sum_range_add, hp, add_sub_cancel_left]
  simpa only [Nat.add_comm] using homogeneous_cubic_tail_bound lam ξ ξ₀ Cg hξ₀ hCg
    hsmall hb (N - 2) t

/-! Regrouping the actual bivariate symbol by homogeneous degree. -/

theorem homogeneous_symbol_series (lam : ℕ × ℕ → ℝ → ℂ) (ξ : Fin 2 → ℂ) (t : ℝ)
    (hs : Summable (fun p => fibreMonomial ξ p * lam p t)) :
    Summable (fun n => fibreHomogeneous lam ξ n t) ∧
      (∑' n, fibreHomogeneous lam ξ n t) = fibreSeriesC lam ξ t := by
  let e := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)
  have hσ : Summable (fun p : Σ n : ℕ, ↥(Finset.HasAntidiagonal.antidiagonal n) =>
      fibreMonomial ξ p.2.val * lam p.2.val t) := e.summable_iff.mpr hs
  have he (n : ℕ) : (∑' p : ↥(Finset.HasAntidiagonal.antidiagonal n),
      fibreMonomial ξ p.val * lam p.val t) = fibreHomogeneous lam ξ n t := by
    rw [tsum_fintype]
    simp only [fibreHomogeneous, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_coe_sort (Finset.HasAntidiagonal.antidiagonal n)
      (fun p => fibreMonomial ξ p * lam p t)
  refine ⟨by simpa only [he] using hσ.sigma, ?_⟩
  rw [fibreSeriesC, ← e.tsum_eq (fun p => fibreMonomial ξ p * lam p t)]
  change (∑' n, fibreHomogeneous lam ξ n t) =
    ∑' p : Σ n : ℕ, ↥(Finset.HasAntidiagonal.antidiagonal n),
      fibreMonomial ξ p.2.val * lam p.2.val t
  rw [Summable.tsum_sigma' (fun _ => (hasSum_fintype _).summable) hσ]
  simp only [he]

/-! The full symbol and every Taylor truncation share the same cubic remainder budget. -/

theorem homogeneous_cubic_tail_tsum_bound (lam : ℕ × ℕ → ℝ → ℂ) (ξ : Fin 2 → ℂ)
    (ξ₀ Cg : ℝ) (hξ₀ : 0 < ξ₀) (hCg : 0 ≤ Cg)
    (hsmall : fibreNorm ξ ≤ ξ₀ / 4)
    (hb : ∀ n t, ‖fibreHomogeneous lam ξ n t‖ ≤
      Cg * (2 / ξ₀) ^ n * fibreNorm ξ ^ n) (t : ℝ) :
    Summable (fun n => ‖fibreHomogeneous lam ξ (n + 3) t‖) ∧
      ‖∑' n, fibreHomogeneous lam ξ (n + 3) t‖ ≤
        (2 * Cg * (2 / ξ₀) ^ 3) * fibreNorm ξ ^ 3 := by
  let ρ := (2 / ξ₀) * fibreNorm ξ
  have hx : 0 ≤ fibreNorm ξ := by unfold fibreNorm; positivity
  have hρ : 0 ≤ ρ := mul_nonneg (by positivity) hx
  have hhalf : ρ ≤ 1 / 2 := by
    dsimp [ρ]
    have hh := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 2 / ξ₀ by positivity)
    calc
      _ ≤ (2 / ξ₀) * (ξ₀ / 4) := hh
      _ = 1 / 2 := by field_simp; norm_num
  obtain ⟨hs, he⟩ := geometric_cubic_tail_tsum hρ hhalf hCg
  have hb' (n : ℕ) : ‖fibreHomogeneous lam ξ (n + 3) t‖ ≤ Cg * ρ ^ (n + 3) := by
    simpa only [ρ, mul_pow, mul_assoc] using hb (n + 3) t
  have hnorm := hs.of_nonneg_of_le (fun _ => norm_nonneg _) hb'
  refine ⟨hnorm, ?_⟩
  calc
    _ ≤ ∑' n, ‖fibreHomogeneous lam ξ (n + 3) t‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n, Cg * ρ ^ (n + 3) := hnorm.tsum_le_tsum hb' hs
    _ ≤ 2 * Cg * ρ ^ 3 := he
    _ = _ := by dsimp only [ρ]; rw [mul_pow]; ring

theorem symbol_quadratic_remainder_bound (lam : ℕ × ℕ → ℝ → ℂ) (ξ : Fin 2 → ℂ)
    (ξ₀ Cg : ℝ) (hξ₀ : 0 < ξ₀) (hCg : 0 ≤ Cg)
    (hsmall : fibreNorm ξ ≤ ξ₀ / 4)
    (hlow : ∀ p : ℕ × ℕ, p.1 + p.2 ≤ 1 → ∀ t, lam p t = 0)
    (hb : ∀ n t, ‖fibreHomogeneous lam ξ n t‖ ≤
      Cg * (2 / ξ₀) ^ n * fibreNorm ξ ^ n)
    (t : ℝ) (hs : Summable (fun p => fibreMonomial ξ p * lam p t)) :
    ‖fibreSeriesC lam ξ t - fibreHomogeneous lam ξ 2 t‖ ≤
      (2 * Cg * (2 / ξ₀) ^ 3) * fibreNorm ξ ^ 3 := by
  obtain ⟨hsn, he⟩ := homogeneous_symbol_series lam ξ t hs
  have hp : (∑ n ∈ Finset.range 3, fibreHomogeneous lam ξ n t) =
      fibreHomogeneous lam ξ 2 t := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [fibreHomogeneous_zero_low_degree lam hlow ξ 0 (by omega) t,
      fibreHomogeneous_zero_low_degree lam hlow ξ 1 (by omega) t]
    simp
  have ht := hsn.sum_add_tsum_nat_add 3
  rw [hp, he] at ht
  rw [← ht, add_sub_cancel_left]
  exact (homogeneous_cubic_tail_tsum_bound lam ξ ξ₀ Cg hξ₀ hCg hsmall hb t).2

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleDamping

/-! Actual graph hypotheses discharge the full and finite cubic symbol budgets. -/

theorem graph_symbol_summable_norm {η ξ₀ Cg : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {r : ℕ × ℕ → ℝ → RawJet2 1 ℂ} {lam : ℕ × ℕ → ℝ → ℂ}
    (h : IsFibreGraph η G v ξ₀ Cg r lam) (ξ : Fin 2 → ℂ)
    (hξ : fibreNorm ξ < ξ₀) (t : ℝ) :
    Summable (fun p => ‖fibreMonomial ξ p * lam p t‖) := by
  apply tsum_enorm_ne_top_iff_summable_norm.mp
  apply ne_of_lt
  apply lt_of_le_of_lt _ (h.2.1 ξ hξ).2.1
  apply ENNReal.tsum_le_tsum
  intro p
  rw [enorm_mul, ← ofReal_norm]
  exact mul_le_mul_right (le_iSup (fun s => ‖lam p s‖ₑ) t) _

theorem graph_symbol_quadratic_remainder {η ξ₀ Cg : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {r : ℕ × ℕ → ℝ → RawJet2 1 ℂ} {lam : ℕ × ℕ → ℝ → ℂ}
    (h : IsFibreGraph η G v ξ₀ Cg r lam) (hξ₀ : 0 < ξ₀) (hCg : 0 ≤ Cg)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ ξ₀ / 4) (t : ℝ) :
    ‖fibreSeriesC lam ξ t - fibreHomogeneous lam ξ 2 t‖ ≤
      (2 * Cg * (2 / ξ₀) ^ 3) * fibreNorm ξ ^ 3 := by
  have hx : fibreNorm ξ < ξ₀ := hξ.trans_lt (by linarith)
  exact symbol_quadratic_remainder_bound lam ξ ξ₀ Cg hξ₀ hCg hξ h.1
    (fun n t => h.2.2.2 n ξ t) t (graph_symbol_summable_norm h ξ hx t).of_norm

theorem graph_finite_symbol_quadratic_remainder {η ξ₀ Cg : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {r : ℕ × ℕ → ℝ → RawJet2 1 ℂ} {lam : ℕ × ℕ → ℝ → ℂ}
    (h : IsFibreGraph η G v ξ₀ Cg r lam) (hξ₀ : 0 < ξ₀) (hCg : 0 ≤ Cg)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ ξ₀ / 4) (N : ℕ) (hN : 2 ≤ N) (t : ℝ) :
    ‖(∑ n ∈ Finset.range (N + 1), fibreHomogeneous lam ξ n t) -
      fibreHomogeneous lam ξ 2 t‖ ≤ (2 * Cg * (2 / ξ₀) ^ 3) * fibreNorm ξ ^ 3 :=
  finite_symbol_quadratic_remainder_bound lam ξ ξ₀ Cg hξ₀ hCg hξ h.1
    (fun n t => h.2.2.2 n ξ t) N hN t

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleDamping

/-! Local time integration and uniform cubic absorption for actual graph symbols. -/

theorem intervalIntegrable_of_uniform_bound (f : ℝ → ℂ)
    (hm : AEStronglyMeasurable f volume) (K : ℝ) (hb : ∀ t, ‖f t‖ ≤ K) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  apply intervalIntegrable_iff.mpr
  exact Measure.integrableOn_of_bounded
    (measure_Ioc_lt_top (a := min a b) (b := max a b)).ne hm (Filter.Eventually.of_forall hb)

/-- Conditional assembly lemma: time measurability and quadratic coercivity are discharged
by the constructed graph and corrector bridge, respectively. -/
theorem low_symbol_damping_of_graph_budget {η ξ₀ Cg : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {r : ℕ × ℕ → ℝ → RawJet2 1 ℂ} {lam : ℕ × ℕ → ℝ → ℂ}
    (h : IsFibreGraph η G v ξ₀ Cg r lam)
    (ξ : Fin 2 → ℂ) (F : ℝ → ℂ)
    (hF : AEStronglyMeasurable F volume)
    (hQ : AEStronglyMeasurable (fun t => fibreHomogeneous lam ξ 2 t) volume)
    (hrem : ∀ t, ‖F t - fibreHomogeneous lam ξ 2 t‖ ≤
      (2 * Cg * (2 / ξ₀) ^ 3) * fibreNorm ξ ^ 3)
    (a b c : ℝ) (hab : a ≤ b)
    (hsmall : (2 * Cg * (2 / ξ₀) ^ 3) * fibreNorm ξ ≤ c / 4)
    (hquad : (∫ t in a..b, fibreHomogeneous lam ξ 2 t).re ≤
      -(3 * c / 4) * (b - a) * fibreNorm ξ ^ 2) :
    (∫ t in a..b, F t).re ≤ -(c / 2) * (b - a) * fibreNorm ξ ^ 2 := by
  let Q := fun t => fibreHomogeneous lam ξ 2 t
  let R := fun t => F t - Q t
  have hQi := intervalIntegrable_of_uniform_bound Q hQ
    (Cg * (2 / ξ₀) ^ 2 * fibreNorm ξ ^ 2) (fun t => h.2.2.2 2 ξ t) a b
  have hRi := intervalIntegrable_of_uniform_bound R (hF.sub hQ)
    ((2 * Cg * (2 / ξ₀) ^ 3) * fibreNorm ξ ^ 3) hrem a b
  have hh := low_damping_of_quadratic_and_cubic Q R a b c
    (2 * Cg * (2 / ξ₀) ^ 3) (fibreNorm ξ) hab hsmall hQi hRi hquad
    (fun t _ => hrem t)
  simpa only [Q, R, add_sub_cancel] using hh

end AVRegularity.CycleDamping
end
end

section
@[expose] public section
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping

/-! Coercive two-moment algebra for a stationary shear. -/

theorem shear_moment_production_identity (b m db : ℂ) (A K : ℝ) :
    inner ℝ db (Complex.I * m) +
      inner ℝ b (Complex.I * (-(A : ℂ) * m - Complex.I * (K : ℂ) * b)) =
    -(K / 2) * ‖m‖ ^ 2 +
      inner ℝ (db + Complex.I * ((K / 2 : ℝ) : ℂ) * m) (Complex.I * m) -
      A * inner ℝ b (Complex.I * m) + K * ‖b‖ ^ 2 := by
  simp only [cellComplexInner_eq, Complex.sq_norm, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.I_re, Complex.I_im]
  ring

theorem shear_moment_production_bound (b m db : ℂ) (A K L q : ℝ)
    (hK : 0 ≤ K) (hq : 0 ≤ q) (hA : 0 ≤ A) (hAL : A ≤ K * L)
    (hb : ‖b‖ ≤ q)
    (he : ‖db + Complex.I * ((K / 2 : ℝ) : ℂ) * m‖ ≤ K * L * q) :
    inner ℝ db (Complex.I * m) +
      inner ℝ b (Complex.I * (-(A : ℂ) * m - Complex.I * (K : ℂ) * b)) ≤
    -(K / 4) * ‖m‖ ^ 2 + K * (1 + 4 * L ^ 2) * q ^ 2 := by
  rw [shear_moment_production_identity]
  have him : ‖Complex.I * m‖ = ‖m‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have herr := (real_inner_le_norm (db + Complex.I * ((K / 2 : ℝ) : ℂ) * m)
    (Complex.I * m)).trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))
  rw [him] at herr
  have hcross : -(A * inner ℝ b (Complex.I * m)) ≤ K * L * q * ‖m‖ := by
    have hi := (neg_le_abs (inner ℝ b (Complex.I * m))).trans
      (abs_real_inner_le_norm b (Complex.I * m))
    rw [him] at hi
    have hi' := mul_le_mul_of_nonneg_left hi hA
    have hb' := mul_le_mul_of_nonneg_left hb hA
    have ha' := mul_le_mul_of_nonneg_right hAL hq
    have hprod := mul_le_mul_of_nonneg_right (hb'.trans ha') (norm_nonneg m)
    nlinarith only [hi', hprod]
  have hbsq : K * ‖b‖ ^ 2 ≤ K * q ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ hK
    nlinarith only [hb, norm_nonneg b, hq]
  have hy : 2 * L * q * ‖m‖ ≤ (1 / 4 : ℝ) * ‖m‖ ^ 2 + 4 * L ^ 2 * q ^ 2 := by
    nlinarith only [sq_nonneg (‖m‖ / 2 - 2 * L * q)]
  have hy' := mul_le_mul_of_nonneg_left hy hK
  nlinarith only [herr, hcross, hbsq, hy']

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization Set
open AVenhance.Infra.Parabolic.WeakUniqueness
namespace AVRegularity.CycleDamping

/-! Continuous fields have genuine joint L² membership on finite cell-time slabs. -/

local instance continuousCellProductProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using CycleEvolution.cellCube_volume_one⟩

theorem continuous_cell_product_memLp {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (f : ℝ × Vec 2 → E) (hf : Continuous f) (a b : ℝ) :
    MemLp f 2 ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) := by
  have hc := (isCompact_Icc (a := a) (b := b)).prod WeakAlgebra.weakSpatialClosedCell_compact
  obtain ⟨M, hM⟩ := hc.bddAbove_image hf.norm.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable M
  rw [Measure.prod_restrict]
  have hcube : MeasurableSet AVenhance.unitCube := by
    unfold AVenhance.unitCube
    exact (measurableSet_pi Set.countable_univ).2 (Or.inl (fun _ _ => measurableSet_Ioo))
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod hcube)] with p hp
  exact hM (mem_image_of_mem (fun p => ‖f p‖)
    ⟨hp.1, WeakAlgebra.weakUnitCube_subset_closedCell hp.2⟩)

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open MeasureTheory AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping

/-! Elementary sesquilinearity on the genuine complex cell L² carrier. -/

theorem cellComplexPair_inner (u z : ComplexCellL2) : cellComplexPair u z = inner ℂ z u := by
  rw [cellComplexPair, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [RCLike.inner_apply]
  rfl

theorem pair_scalar_left (c : ℂ) (u z : ComplexCellL2) :
    cellComplexPair (cellScalarCLM c u) z = c * cellComplexPair u z := by
  rw [cellComplexPair_inner, cellComplexPair_inner]
  change inner ℂ z (c • u) = _
  exact inner_smul_right _ _ _

theorem pair_scalar_right (c : ℂ) (u z : ComplexCellL2) :
    cellComplexPair u (cellScalarCLM c z) = star c * cellComplexPair u z := by
  rw [cellComplexPair_inner, cellComplexPair_inner]
  change inner ℂ (c • z) u = _
  exact inner_smul_left _ _ _

theorem pair_add_left (u v z : ComplexCellL2) :
    cellComplexPair (u + v) z = cellComplexPair u z + cellComplexPair v z := by
  simp only [cellComplexPair_inner, inner_add_right]

theorem pair_add_right (u v z : ComplexCellL2) :
    cellComplexPair u (v + z) = cellComplexPair u v + cellComplexPair u z := by
  simp only [cellComplexPair_inner, inner_add_left]

theorem pair_norm_le (u z : ComplexCellL2) : ‖cellComplexPair u z‖ ≤ ‖u‖ * ‖z‖ := by
  rw [cellComplexPair_inner, mul_comm]
  exact norm_inner_le_norm _ _

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping

/-! Time-integrated observability for two absolutely continuous shear moments. -/

theorem shear_moment_integral_bound {a b : ℝ} (hab : a ≤ b)
    (m dm z dz : ℝ → ℂ) (q A : ℝ → ℝ) (K L E : ℝ)
    (hm : StrongTimeRegularity a b m dm) (hz : StrongTimeRegularity a b z dz)
    (hK : 0 < K)
    (hA : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ A t)
    (hAL : ∀ᵐ t ∂volume.restrict (Icc a b), A t ≤ K * L)
    (hmi : IntervalIntegrable (fun t => ‖m t‖ ^ 2) volume a b)
    (hqi : IntervalIntegrable (fun t => q t ^ 2) volume a b)
    (hq : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ q t)
    (hzq : ∀ᵐ t ∂volume.restrict (Icc a b), ‖z t‖ ≤ q t)
    (hde : ∀ᵐ t ∂volume.restrict (Icc a b),
      dm t = -(A t : ℂ) * m t - Complex.I * (K : ℂ) * z t)
    (herr : ∀ᵐ t ∂volume.restrict (Icc a b),
      ‖dz t + Complex.I * ((K / 2 : ℝ) : ℂ) * m t‖ ≤ K * L * q t)
    (hea : ‖z a‖ * ‖m a‖ ≤ E) (heb : ‖z b‖ * ‖m b‖ ≤ E) :
    (K / 4) * (∫ t in a..b, ‖m t‖ ^ 2) ≤
      2 * E + K * (1 + 4 * L ^ 2) * (∫ t in a..b, q t ^ 2) := by
  let J : ℂ →L[ℝ] ℂ := Complex.I • ContinuousLinearMap.id ℝ ℂ
  have hmI : StrongTimeRegularity a b (fun t => Complex.I * m t)
      (fun t => Complex.I * dm t) := by
    simpa only [J, smul_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul] using hm.map J
  have hP := complex_time_inner hz hmI
  have hi : IntervalIntegrable (fun t => inner ℝ (dz t) (Complex.I * m t) +
      inner ℝ (z t) (Complex.I * dm t)) volume a b := by
    apply hP.ac.intervalIntegrable_deriv.congr_ae
    have hd := hP.derivative.filter_mono
      (ae_mono (Measure.restrict_mono uIoc_subset_uIcc le_rfl))
    filter_upwards [hd] with t ht
    exact ht.deriv
  have hbnd := intervalIntegral.integral_mono_ae_restrict hab hi
    ((hmi.const_mul (-(K / 4))).add (hqi.const_mul (K * (1 + 4 * L ^ 2)))) (by
      filter_upwards [hq, hzq, hde, herr, hA, hAL] with t hqt hzt hdt het hAt hALt
      rw [hdt]
      exact shear_moment_production_bound (z t) (m t) (dz t) (A t) K L (q t)
        hK.le hqt hAt hALt hzt het)
  rw [intervalIntegral.integral_add (hmi.const_mul (-(K / 4)))
    (hqi.const_mul (K * (1 + 4 * L ^ 2))),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    ← complex_time_inner_increment hz hmI] at hbnd
  have ha0 := (real_inner_le_norm (z a) (Complex.I * m a))
  have hb0 := (neg_le_abs (inner ℝ (z b) (Complex.I * m b))).trans
    (abs_real_inner_le_norm (z b) (Complex.I * m b))
  simp only [norm_mul, Complex.norm_I, one_mul] at ha0 hb0
  linarith only [hbnd, ha0, hb0, hea, heb]

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping

/-! Uniform bounds for the diffusion coefficients in the shear moment equation. -/

def realMetricSymbol (G : Matrix (Fin 2) (Fin 2) ℝ) (θ : Vec 2) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, θ i * G i j * θ j

theorem realMetricSymbol_complex (G : Matrix (Fin 2) (Fin 2) ℝ) (θ : Vec 2) :
    (∑ i : Fin 2, ∑ j : Fin 2, (θ j : ℂ) * (G i j : ℂ) * (θ i : ℂ)) =
      (realMetricSymbol G θ : ℂ) := by
  simp only [realMetricSymbol, Fin.sum_univ_two, Complex.ofReal_add, Complex.ofReal_mul]
  ring

theorem realMetricSymbol_bounds
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric (fun t _ => G t))
    (θ : Vec 2) (hθ : ∀ j, |θ j| ≤ Real.pi) (t : ℝ) :
    0 ≤ realMetricSymbol (G t) θ ∧ realMetricSymbol (G t) θ ≤ 4 * Real.pi ^ 2 := by
  have he := hG.2.2.2 t 0 θ
  have h0 := (sq_le_sq₀ (abs_nonneg (θ 0)) Real.pi_pos.le).mpr (hθ 0)
  have h1 := (sq_le_sq₀ (abs_nonneg (θ 1)) Real.pi_pos.le).mpr (hθ 1)
  rw [sq_abs] at h0 h1
  change (1 / 2) * (∑ i : Fin 2, θ i ^ 2) ≤ realMetricSymbol (G t) θ ∧
    realMetricSymbol (G t) θ ≤ 2 * (∑ i : Fin 2, θ i ^ 2) at he
  simp only [Fin.sum_univ_two] at he
  constructor <;> nlinarith only [he.1, he.2, h0, h1, sq_nonneg (θ 0), sq_nonneg (θ 1)]

theorem cosine_diffusion_diagonal_norm_le
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric (fun t _ => G t))
    (t : ℝ) (j : Fin 2) :
    ‖(2 * Real.pi : ℂ) ^ 2 * (G t j j : ℂ)‖ ≤ 8 * Real.pi ^ 2 := by
  have he := cellMetric_entry_bound hG t 0 j j
  rw [norm_mul, norm_pow, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, Complex.norm_real, Real.norm_eq_abs]
  nlinarith only [mul_le_mul_of_nonneg_left he (sq_nonneg (2 * Real.pi))]

theorem cosine_diffusion_cross_norm_le
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric (fun t _ => G t))
    (θ : Vec 2) (hθ : ∀ i, |θ i| ≤ Real.pi) (t : ℝ) (j : Fin 2) :
    ‖Complex.I * (2 * Real.pi : ℂ) *
      (∑ i : Fin 2, (θ i : ℂ) * ((G t i j : ℂ) + (G t j i : ℂ)))‖ ≤ 16 * Real.pi ^ 2 := by
  have hp (i : Fin 2) : ‖(θ i : ℂ) * ((G t i j : ℂ) + (G t j i : ℂ))‖ ≤ 4 * Real.pi := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hs := (norm_add_le (G t i j : ℂ) (G t j i : ℂ)).trans
      (add_le_add (by simpa only [Complex.norm_real, Real.norm_eq_abs] using cellMetric_entry_bound hG t 0 i j)
        (by simpa only [Complex.norm_real, Real.norm_eq_abs] using cellMetric_entry_bound hG t 0 j i))
    have hm := mul_le_mul (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hθ i)
      hs (norm_nonneg _) Real.pi_pos.le
    linarith only [hm]
  have hs := (norm_sum_le (Finset.univ : Finset (Fin 2)) _).trans (Finset.sum_le_sum (fun i _ => hp i))
  simp only [Fin.sum_univ_two] at hs
  rw [norm_mul, norm_mul, Complex.norm_I, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, one_mul]
  simp only [Fin.sum_univ_two]
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * Real.pi)
  nlinarith only [hm]

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping

/-! Literal scalar operations for spatially frozen metrics and bounded cell drifts. -/

theorem frozen_metric_entry_scalar {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric (fun t _ => G t)) (t : ℝ) (i j : Fin 2) (u : ComplexCellL2) :
    cellMetricEntryCLM hG t i j u = cellScalarCLM (G t i j : ℂ) u := by
  apply Lp.ext
  exact (cellMetricEntryCLM_ae hG t i j u).trans (cellScalarCLM_ae _ u).symm

theorem drift_entry_scalar (C : CellCoefficients) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (j : Fin 2) (c : ℂ) (u : ComplexCellL2) :
    cellDriftEntryCLM C V hv hb t j (cellScalarCLM c u) =
      cellScalarCLM c (cellDriftEntryCLM C V hv hb t j u) := by
  apply Lp.ext
  filter_upwards [cellDriftEntryCLM_ae C V hv hb t j (cellScalarCLM c u),
    cellScalarCLM_ae c u, cellScalarCLM_ae c (cellDriftEntryCLM C V hv hb t j u),
    cellDriftEntryCLM_ae C V hv hb t j u] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  ring

theorem drift_diagonal_pair_im_zero (C : CellCoefficients) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (j : Fin 2) (u : ComplexCellL2) :
    (cellComplexPair (cellDriftEntryCLM C V hv hb t j u) u).im = 0 := by
  have hp := Complex.imCLM.integral_comp_comm
    (cellComplex_pairing_integrable (cellDriftEntryCLM C V hv hb t j u) u)
  change (∫ x in AVenhance.unitCube,
    (cellDriftEntryCLM C V hv hb t j u x * star (u x)).im) = _ at hp
  change (∫ x in AVenhance.unitCube,
    cellDriftEntryCLM C V hv hb t j u x * star (u x)).im = 0
  change _ = (∫ x in AVenhance.unitCube,
    cellDriftEntryCLM C V hv hb t j u x * star (u x)).im at hp
  rw [← hp]
  apply integral_eq_zero_of_ae
  filter_upwards [cellDriftEntryCLM_ae C V hv hb t j u] with x hx
  rw [hx]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Pi.zero_apply]
  ring

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleDamping

/-! Literal cell and uniformly local L² bounds from pointwise size estimates. -/

theorem cellL2Norm_le_uniform_bound {E : Type*} [NormedAddCommGroup E]
    (f : Vec 2 → E) (hm : AEStronglyMeasurable f (volume.restrict AVenhance.unitCube))
    (A : ℝ) (hb : ∀ x, ‖f x‖ ≤ A) : cellL2Norm f ≤ ENNReal.ofReal A := by
  have h := eLpNorm_le_of_ae_bound (p := 2) hm (Filter.Eventually.of_forall hb)
  simpa only [cellL2Norm, Measure.restrict_apply_univ, CycleEvolution.cellCube_volume_one,
    ENNReal.one_rpow, one_mul] using h

theorem cellUlNorm_le_uniform_bound {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → Vec 2 → E)
    (hm : ∀ t, AEStronglyMeasurable (f t) (volume.restrict AVenhance.unitCube))
    (A : ℝ) (hb : ∀ t x, ‖f t x‖ ≤ A) :
    cellUlNorm Set.univ f ≤ ENNReal.ofReal A :=
  CycleEvolution.cellUlNorm_le_uniform_cellL2Norm _ _
    (fun t => cellL2Norm_le_uniform_bound _ (hm t) A (hb t))

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping

/-! Actual metric dissipation on arbitrary complex L² vectors. -/

def metricVectorDissipation {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) (t : ℝ) (U : Fin 2 → ComplexCellL2) : ℝ :=
  ∑ j : Fin 2, ∑ k : Fin 2, inner ℝ (cellMetricEntryCLM hG t j k (U j)) (U k)

theorem metricVectorDissipation_coercive {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) (t : ℝ) (U : Fin 2 → ComplexCellL2) :
    (1 / 2) * ∑ j, ‖U j‖ ^ 2 ≤ metricVectorDissipation hG t U := by
  let f := fun j k x => ((G t x j k : ℂ) * U j x * star (U k x)).re
  have hf (j k : Fin 2) := cellMetric_pairing_integrable hG t j k (U j) (U k)
  have hfs (j : Fin 2) : Integrable (fun x => ∑ k : Fin 2, f j k x)
      (volume.restrict AVenhance.unitCube) := by
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun k _ => hf j k)
  have hfss : Integrable (fun x => ∑ j : Fin 2, ∑ k : Fin 2, f j k x)
      (volume.restrict AVenhance.unitCube) := by
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun j _ => hfs j)
  have hd (j : Fin 2) := integrable_normSq_of_memLp (Lp.memLp (U j))
  have hds : Integrable (fun x => ∑ j : Fin 2, ‖U j x‖ ^ 2)
      (volume.restrict AVenhance.unitCube) := by
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun j _ => hd j)
  have hh := integral_mono_ae (hds.const_mul (1 / 2)) hfss (Filter.Eventually.of_forall (fun x => by
    simpa only [f, Fin.sum_univ_two, Complex.add_re] using
      cellMetric_complex_coercive hG t x (fun j => U j x)))
  have he : (∫ x in AVenhance.unitCube, ∑ j : Fin 2, ∑ k : Fin 2, f j k x) =
      metricVectorDissipation hG t U := by
    rw [integral_finsetSum Finset.univ (fun j _ => hfs j)]
    unfold metricVectorDissipation
    apply Finset.sum_congr rfl
    intro j _
    change (∫ x in AVenhance.unitCube, ∑ k : Fin 2, f j k x) = _
    rw [integral_finsetSum Finset.univ (fun k _ => hf j k)]
    apply Finset.sum_congr rfl
    intro k _
    exact (cellMetric_pairing_eq_integral hG t j k _ _).symm
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun j _ => hd j), he] at hh
  simp_rw [cellL2_norm_sq_integral] at hh
  exact hh

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleDamping

/-! Real Bloch shifts preserve the energy neutrality of the actual cell drift. -/

theorem real_shift_drift_energy_zero
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Vec 2) (t : ℝ) (u : TorusHk 1 ℂ) :
    (∑ j : Fin 2, cellComplexPair
      (cellDriftEntryCLM ⟨G, v, fun k => (θ k : ℂ), 0⟩ V hv.1 hb t j
        (cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j u)) (torusHkValueCLM u)).re = 0 := by
  let C : CellCoefficients := ⟨G, v, fun k => (θ k : ℂ), 0⟩
  have he (j : Fin 2) : (cellComplexPair
      (cellDriftEntryCLM C V hv.1 hb t j (cellShiftedDerivativeCLM C.θ j u))
      (torusHkValueCLM u)).re =
      inner ℝ (cellDriftEntryCLM C V hv.1 hb t j (cellDerivativeCLM j u)) (torusHkValueCLM u) := by
    have hd : cellShiftedDerivativeCLM C.θ j u = cellDerivativeCLM j u +
        cellScalarCLM (Complex.I * C.θ j) (torusHkValueCLM u) := rfl
    rw [hd, map_add, pair_add_left, drift_entry_scalar, pair_scalar_left,
      Complex.add_re, cellComplexPair_re]
    have hz := drift_diagonal_pair_im_zero C V hv.1 hb t j (torusHkValueCLM u)
    simp only [C, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, hz, sub_self, add_zero]
  have hzero := cellDriftForm_energy_zero hv V hb t u
  change (∑ j : Fin 2, inner ℝ
    (cellDriftEntryCLM C V hv.1 hb t j (cellDerivativeCLM j u)) (torusHkValueCLM u)) = 0 at hzero
  change (∑ j : Fin 2, cellComplexPair
    (cellDriftEntryCLM C V hv.1 hb t j (cellShiftedDerivativeCLM C.θ j u)) (torusHkValueCLM u)).re = 0
  simpa only [Fin.sum_univ_two, Complex.add_re, he] using hzero

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleDamping

/-! Bounded scalar multiples of a genuine fixed weak jet have finite all-time energy norm. -/

theorem fixed_mode_energy_finite (J : RawJet2 1 ℂ) (hJ : HasPeriodicOrderedWeakJet J)
    (a : ℝ → ℂ) (A : ℝ≥0∞) (hA : A < ⊤) (ha : ∀ t, ‖a t‖ₑ ≤ A) :
    cellEnergyNorm Set.univ (fun t => a t • J) < ⊤ := by
  have hv : MemLp (J (valueIndex2 1)) 2 (volume.restrict AVenhance.unitCube) :=
    hJ.2.1 (valueIndex2 1)
  have hg : MemLp (cellGradient J) 2 (volume.restrict AVenhance.unitCube) :=
    CycleEvolution.cellFiniteArray_memLp (fun x i => cellGradComp J i x)
      (fun i => hJ.2.1 ⟨⟨1, by decide⟩, fun _ => i⟩)
  have hvb (t : ℝ) : cellL2Norm (cellValue (fun t => a t • J) t) ≤
      A * cellL2Norm (J (valueIndex2 1)) := by
    change eLpNorm (a t • J (valueIndex2 1)) 2 _ ≤ _
    rw [eLpNorm_const_smul]
    gcongr
    · exact ha t
    · exact le_rfl
  have hgb (t : ℝ) : cellL2Norm (cellGradient (a t • J)) ≤
      A * cellL2Norm (cellGradient J) := by
    rw [CycleEvolution.cellGradient_complex_smul]
    change eLpNorm (a t • cellGradient J) 2 _ ≤ _
    rw [eLpNorm_const_smul]
    gcongr
    · exact ha t
    · exact le_rfl
  have hb : cellEnergyNorm Set.univ (fun t => a t • J) ≤
      A * cellL2Norm (J (valueIndex2 1)) + A * cellL2Norm (cellGradient J) := by
    exact add_le_add (iSup_le (fun t => iSup_le (fun _ => hvb t)))
      (CycleEvolution.cellUlNorm_le_uniform_cellL2Norm _ _ hgb)
  exact hb.trans_lt (ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top hA hv.eLpNorm_lt_top, ENNReal.mul_lt_top hA hg.eLpNorm_lt_top⟩)

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleDamping

/-! Exact real scale identities for the cell switching residual. -/

/-- The physical relaxation rate is exactly the cell spectral gap divided by cell length squared. -/
theorem ocMu_cell_rate {q : ℝ} {Λ m : ℕ} {ν : ℝ}
    (hΛ : 1 ≤ Λ) (hν : 0 < ν) :
    ocMu q Λ m ν * ocEll q Λ m ν ^ 2 = 4 * Real.pi ^ 2 := by
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  rw [CycleReference.ocEll_sq_eq hν, ocMu]
  field_simp

/-- The quiet-tail exponential in physical units is the intended cell exponential. -/
theorem ocMu_switch_exponent {α q : ℝ} {Λ m : ℕ} {ν : ℝ}
    (hΛ : 1 ≤ Λ) (hν : 0 < ν) :
    -(ocMu q Λ m ν) * ocTau α q Λ m / 12 =
      -(Real.pi ^ 2) * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2) := by
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hlen : ocEll q Λ m ν ^ 2 ≠ 0 := by
    rw [CycleReference.ocEll_sq_eq hν]
    positivity
  apply (eq_div_iff (mul_ne_zero (by norm_num) hlen)).2
  have hr := ocMu_cell_rate (q := q) (m := m) hΛ hν
  calc
    _ = -(ocMu q Λ m ν * ocEll q Λ m ν ^ 2) * ocTau α q Λ m / 4 := by ring
    _ = _ := by rw [hr]; ring

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance.Infra.Torus
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleDamping

/-! The projected weak Bloch derivative has its literal smooth Fourier representative. -/

theorem projected_shifted_derivative_ae (θ : Vec 2) (u : TorusHk 1 ℂ) (N : ℕ) (j : Fin 2) :
    CycleEvolution.cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j (galerkinProj N u) =ᵐ[
      volume.restrict AVenhance.unitCube]
      smoothShiftedDerivative θ j (smoothFourierJet (L := 1) N u (valueIndex2 1)) := by
  let p := galerkinProj N u
  let c : ℂ := Complex.I * (θ j : ℂ)
  have he : CycleEvolution.cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j p =
      CycleEvolution.cellDerivativeCLM j p + c • torusHkValueCLM p := rfl
  rw [he]
  have hv := galerkinProj_jet_ae_smooth N u (valueIndex2 1)
  have hd := galerkinProj_jet_ae_smooth N u ⟨⟨1, by decide⟩, fun _ => j⟩
  filter_upwards [hv, hd, Lp.coeFn_add (CycleEvolution.cellDerivativeCLM j p)
    (c • torusHkValueCLM p), Lp.coeFn_smul c (torusHkValueCLM p)] with x hx hdx ha hs
  rw [ha]
  simp only [Pi.add_apply]
  rw [hs]
  change CycleEvolution.cellDerivativeCLM j p x + c * torusHkValueCLM p x = _
  change CycleEvolution.cellDerivativeCLM j p x = _ at hdx
  change torusHkValueCLM p x = _ at hx
  rw [hdx, hx]
  have hc := (smoothFourierJet_fderiv (L := 1) N u (0 : Fin 1) Fin.elim0 j x).symm
  change _ = coordDeriv j (smoothFourierJet (L := 1) N u (valueIndex2 1)) x at hc
  change _ = coordDeriv j (smoothFourierJet (L := 1) N u (valueIndex2 1)) x +
    c * smoothFourierJet (L := 1) N u (valueIndex2 1) x
  apply congrArg (fun z : ℂ => z + c * smoothFourierJet (L := 1) N u (valueIndex2 1) x)
  convert hc using 1
  congr 2

theorem projected_shifted_gradient_energy (θ : Vec 2) (u : TorusHk 1 ℂ) (N : ℕ) :
    (∑ j : Fin 2, ∫ x in unitCell 2,
      ‖smoothShiftedDerivative θ j (smoothFourierJet (L := 1) N u (valueIndex2 1)) x‖ ^ 2) =
      ∑ j : Fin 2, ‖CycleEvolution.cellShiftedDerivativeCLM
        (fun k => (θ k : ℂ)) j (galerkinProj N u)‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_unitCell_eq_unitCube, ← CycleEvolution.cellL2_norm_sq_integral]
  apply integral_congr_ae
  exact (projected_shifted_derivative_ae θ u N j).mono
    (fun x hx => congrArg (fun z : ℂ => ‖z‖ ^ 2) hx.symm)

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleDamping

/-! Every band-chain level has arbitrarily small memory ratio at a sufficiently large base. -/

theorem bandChain_memory_ratio_small {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ M : ℕ, ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
      ∀ m : ℕ, 2 ≤ m → m ≤ M →
        ocEll q Λ m (κ m) ^ 2 / ocTau α q Λ m ≤ δ := by
  obtain ⟨C, hC, L, hL, hb⟩ := CycleReference.bandChain_memory_scale
    hα₀ hα₁ hs₀ hs₁ hq hζ
  have hCp : 0 < C := by linarith only [hC]
  have hp : 0 < 4 * ocDelta α q := mul_pos (by norm_num)
    (AVRegularity.Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  obtain ⟨K, hK, hk⟩ := CycleReference.exists_small_scale_error_budget hq.1 hp
    (div_pos hδ hCp)
  refine ⟨max L K, hL.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ M κ hκ m hm hmM
  have hΛL : L ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛK : K ≤ Λ := (le_max_right _ _).trans hΛ
  have h128 := hL.trans hΛL
  have he := CycleReference.epsilon_power_le_tail hq.1 hp h128 (show 1 ≤ m - 1 by omega)
  have hs := he.trans (hk Λ hΛK).2
  have hsmall := mul_le_mul_of_nonneg_left hs hCp.le
  rw [mul_div_cancel₀ δ hCp.ne'] at hsmall
  exact (hb Λ hΛL M (by omega) κ hκ m hm hmM).1.trans hsmall

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance.Infra.Torus Filter Topology
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleDamping

/-! Brillouin frequency coercivity for every actual periodic H¹ cell class. -/

theorem projected_shifted_frequency_gap (θ : Vec 2) (hθ : ∀ j, |θ j| ≤ Real.pi)
    (u : TorusHk 1 ℂ) (N : ℕ) :
    (∑ j, θ j ^ 2) * ‖torusHkValueCLM (galerkinProj N u)‖ ^ 2 ≤
      ∑ j : Fin 2, ‖CycleEvolution.cellShiftedDerivativeCLM
        (fun k => (θ k : ℂ)) j (galerkinProj N u)‖ ^ 2 := by
  let q := smoothFourierJet (L := 1) N u (valueIndex2 1)
  have hf : ContDiff ℝ 1 q := (smoothFourierJet_contDiff N u _).of_le (by simp)
  have hp : AVenhance.IsZ2Periodic q := smoothFourierJet_periodic N u _
  have hh := smoothShiftedGradient_frequency_gap θ hθ hf hp
  have hv : (∫ x in unitCell 2, ‖q x‖ ^ 2) =
      ‖torusHkValueCLM (galerkinProj N u)‖ ^ 2 := by
    rw [integral_unitCell_eq_unitCube, ← CycleEvolution.cellL2_norm_sq_integral]
    apply integral_congr_ae
    exact (galerkinProj_jet_ae_smooth N u (valueIndex2 1)).mono
      (fun x hx => congrArg (fun z : ℂ => ‖z‖ ^ 2) hx.symm)
  rw [hv, projected_shifted_gradient_energy θ u N] at hh
  exact hh

theorem cellH1_shifted_frequency_gap (θ : Vec 2) (hθ : ∀ j, |θ j| ≤ Real.pi)
    (u : TorusHk 1 ℂ) :
    (∑ j, θ j ^ 2) * ‖torusHkValueCLM u‖ ^ 2 ≤
      ∑ j : Fin 2, ‖CycleEvolution.cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j u‖ ^ 2 := by
  have hp := galerkinProj_tendsto u
  have hleft : Tendsto (fun N => (∑ j, θ j ^ 2) *
      ‖torusHkValueCLM (galerkinProj N u)‖ ^ 2) atTop
      (𝓝 ((∑ j, θ j ^ 2) * ‖torusHkValueCLM u‖ ^ 2)) := tendsto_const_nhds.mul
    ((torusHkValueCLM.continuous.norm.pow 2).continuousAt.tendsto.comp hp)
  have hright : Tendsto (fun N => ∑ j : Fin 2,
      ‖CycleEvolution.cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j (galerkinProj N u)‖ ^ 2)
      atTop (𝓝 (∑ j : Fin 2,
        ‖CycleEvolution.cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j u‖ ^ 2)) := by
    apply tendsto_finsetSum
    intro j _
    exact (((CycleEvolution.cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j).continuous.norm.pow 2).continuousAt.tendsto.comp hp)
  exact le_of_tendsto_of_tendsto' hleft hright (projected_shifted_frequency_gap θ hθ u)

end AVRegularity.CycleDamping
end
end
