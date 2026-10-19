-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Definitions.IsHolderDivFreeVelocity
public import AVRegularity.Applications.Torus.JointContinuityMain
public import AVRegularity.Applications.Construction
import AVRegularity.Applications.Torus.TraceIdent
import AVRegularity.Velocity.ExistsLimitVelocity
import AVRegularity.Applications.Microscopic.Main
import AVRegularity.Applications.TorusEnergy.LocalInt
public import AVRegularity.Applications.Parabolic.SliceGrad
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Monotonicity.Lemmas

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization AVenhance
namespace AVRegularity.Applications

/-! # Joint continuity of a Hölder velocity (restated here because the lemma of
`AVRegularity.Wellposed.Existence` is private). -/

theorem continuous_of_holder_bound {α : ℝ} (hα : 0 < α)
    {b : ℝ → Vec 2 → Vec 2}
    (hholder : ∃ C, ∀ t u : ℝ, ∀ x y : Vec 2,
      ‖b t x - b u y‖ ≤ C * (|t - u| + Real.sqrt (vecNormSq (x - y))) ^ α) :
    Continuous (fun p : ℝ × Vec 2 => b p.1 p.2) := by
  obtain ⟨C, hC⟩ := hholder
  have hC_nonneg : 0 ≤ C := by
    have h := hC 0 1 (0 : Vec 2) 0
    have hsqrt : Real.sqrt (vecNormSq (0 : Vec 2)) = 0 := by
      simp [Homogenization.vecNormSq, Homogenization.vecDot]
    have hbound : ‖b 0 0 - b 1 0‖ ≤ C := by
      simpa [hsqrt] using h
    exact le_trans (norm_nonneg _) hbound
  apply continuous_iff_continuousAt.mpr
  intro p
  have hd : ContinuousAt
      (fun q : ℝ × Vec 2 => |q.1 - p.1| + Real.sqrt (vecNormSq (q.2 - p.2))) p := by
    fun_prop [Homogenization.vecNormSq, Homogenization.vecDot]
  have hdp : |p.1 - p.1| + Real.sqrt (vecNormSq (p.2 - p.2)) = 0 := by
    simp [Homogenization.vecNormSq, Homogenization.vecDot]
  have hpow : ContinuousAt
      (fun q : ℝ × Vec 2 =>
        C * (|q.1 - p.1| + Real.sqrt (vecNormSq (q.2 - p.2))) ^ α) p := by
    have hpow' := hd.rpow_const (Or.inr hα.le)
    exact continuousAt_const.mul hpow'
  have hpow_zero :
      C * (|p.1 - p.1| + Real.sqrt (vecNormSq (p.2 - p.2))) ^ α = 0 := by
    have hdist0 : |p.1 - p.1| + Real.sqrt (vecNormSq (p.2 - p.2)) = 0 := by
      simp [Homogenization.vecNormSq, Homogenization.vecDot]
    rw [hdist0]
    simp [hα.ne']
  refine Metric.continuousAt_iff.mpr ?_
  intro ε hε
  obtain ⟨δ, hδ, hδbound⟩ := Metric.continuousAt_iff.mp hpow ε hε
  refine ⟨δ, hδ, ?_⟩
  intro q hq
  have hHolder := hC q.1 p.1 q.2 p.2
  have hle : dist (b q.1 q.2) (b p.1 p.2) ≤
      C * (|q.1 - p.1| + Real.sqrt (vecNormSq (q.2 - p.2))) ^ α := by
    simpa [dist_eq_norm] using hHolder
  have hpow_bound :
      C * (|q.1 - p.1| + Real.sqrt (vecNormSq (q.2 - p.2))) ^ α < ε := by
    have hd' := hδbound hq
    have hnonneg : 0 ≤ C * (|q.1 - p.1| + Real.sqrt (vecNormSq (q.2 - p.2))) ^ α := by
      exact mul_nonneg hC_nonneg
        (Real.rpow_nonneg (add_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) α)
    rw [hpow_zero] at hd'
    have hd0 : |C * (|q.1 - p.1| + Real.sqrt (vecNormSq (q.2 - p.2))) ^ α| < ε := by
      simpa [Real.dist_eq] using hd'
    rw [abs_of_nonneg hnonneg] at hd0
    exact hd0
  exact lt_of_le_of_lt hle hpow_bound

theorem IsHolderDivFreeVelocity.continuous {α : ℝ} (hα : 0 < α) {b : ℝ → Vec 2 → Vec 2}
    (hb : IsHolderDivFreeVelocity α b) : Continuous (fun p : ℝ × Vec 2 => b p.1 p.2) :=
  continuous_of_holder_bound hα hb.2.2.2.1

end AVRegularity.Applications
end
end
end

section
section
/-! # Statement of the all-distance transfer

For a bounded `C¹` stream `φ` (full velocity `b = σ∇φ`)
and a smooth stream `φ_L` (finite velocity `b_L = σ∇φ_L`, spatially Lipschitz with constant
`D_L`), energy solutions `u, v` with velocities `b, b_L`, the same diffusivity and datum: if the
finite solution has `‖v(t)‖_{C^s(𝕋²)} ≤ S F` on the enlarged window and the rescaled
coefficients are small, `ϑ + (R²/κ) D_L ≤ η`, `ϑ = ‖φ - φ_L‖_∞ / κ`, then
`‖u(t)‖_{C^s(𝕋²)} ≤ C (S + ϑ R^{-1-s}) F` on the observation window. Proposition 3.2 of the paper
follows from it. -/

@[expose] public section

open MeasureTheory Homogenization AVenhance

namespace AVRegularity.Applications

/-- The hypotheses on the full stream: jointly continuous, `C¹` in space, bounded continuous
velocity, spatially periodic. -/
def IsFullStream (φ : ℝ → Vec 2 → ℝ) : Prop :=
  Continuous (fun p : ℝ × Vec 2 => φ p.1 p.2) ∧ (∀ t, ContDiff ℝ 1 (φ t)) ∧
  Continuous (fun p : ℝ × Vec 2 => streamVel φ p.1 p.2) ∧
  (∃ B : ℝ, ∀ t x, ‖streamVel φ t x‖ ≤ B) ∧ ∀ t, IsZ2Periodic (φ t)

/-- The hypotheses on the finite stream: jointly smooth and spatially periodic. -/
def IsSmoothStream (φ : ℝ → Vec 2 → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2) ∧ ∀ t, IsZ2Periodic (φ t)

/-- **Statement of the all-distance transfer** for the exponent `s`. -/
def TransferStmt (s : ℝ) : Prop :=
  ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧
    ∀ (φ φL : ℝ → Vec 2 → ℝ), IsFullStream φ → IsSmoothStream φL →
    ∀ (DL κ ϑ R S F tS tE t₀ T : ℝ) (f : Vec 2 → ℝ) (u v : ℝ → Vec 2 → ℝ),
      (∀ t x y, eNorm (streamVel φL t x - streamVel φL t y) ≤ DL * eNorm (x - y)) →
      0 < κ → (∀ t x, |φ t x - φL t x| ≤ κ * ϑ) → 0 < R → R ≤ 1 / 8 →
      MemL2On unitCube f → Real.sqrt (l2NormSq f) ≤ F →
      IsWeakSolutionOn (streamVel φ) κ tS tE f u →
      IsWeakSolutionOn (streamVel φL) κ tS tE f v →
      tS ≤ t₀ - R ^ 2 / κ → t₀ ≤ T → T + R ^ 2 / κ ≤ tE → 0 ≤ S →
      (∀ t ∈ Set.Icc (t₀ - R ^ 2 / κ) (T + R ^ 2 / κ), ∃ Vt : Vec 2 → ℝ,
        IsZ2Periodic Vt ∧ Vt =ᵐ[volume.restrict unitCube] v t ∧ CsNormLe s Vt (S * F)) →
      ϑ + R ^ 2 / κ * DL ≤ η →
      ∀ t ∈ Set.Icc t₀ T, ∃ Θt : Vec 2 → ℝ,
        IsZ2Periodic Θt ∧ Θt =ᵐ[volume.restrict unitCube] u t ∧
        CsNormLe s Θt (C * (S + ϑ * R ^ (-1 - s)) * F)

end AVRegularity.Applications
end
end

section
/-! # The limit stream is a full stream

A differentiable stream whose velocity `σ∇φ` is a bounded continuous field has continuous
spatial derivative, hence satisfies `IsFullStream`. -/

@[expose] public section

noncomputable section

open Homogenization AVenhance

namespace AVRegularity.Applications

theorem fderiv_basis_of_streamVel {φ : ℝ → Vec 2 → ℝ} (t : ℝ) (x : Vec 2) :
    fderiv ℝ (φ t) x (basisVec 0) = streamVel φ t x 1 ∧
      fderiv ℝ (φ t) x (basisVec 1) = -streamVel φ t x 0 := by
  simp [streamVel, sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, spaceGrad]

theorem isFullStream_of {φ : ℝ → Vec 2 → ℝ} (hd : ∀ t, Differentiable ℝ (φ t))
    (hφc : Continuous (fun p : ℝ × Vec 2 => φ p.1 p.2))
    (hbc : Continuous (fun p : ℝ × Vec 2 => streamVel φ p.1 p.2))
    (hbb : ∃ B : ℝ, ∀ t x, ‖streamVel φ t x‖ ≤ B) (hper : ∀ t, IsZ2Periodic (φ t)) :
    IsFullStream φ := by
  refine ⟨hφc, fun t => ?_, hbc, hbb, hper⟩
  rw [contDiff_one_iff_fderiv]
  refine ⟨hd t, ?_⟩
  rw [continuous_clm_apply]
  intro v
  have hv : v = v 0 • basisVec 0 + v 1 • basisVec 1 := by
    funext i
    fin_cases i <;> simp [basisVec]
  have hslice : Continuous (fun x => streamVel φ t x) :=
    hbc.comp (continuous_const.prodMk continuous_id)
  have h0 : Continuous fun x => streamVel φ t x 1 := (continuous_apply 1).comp hslice
  have h1 : Continuous fun x => streamVel φ t x 0 := (continuous_apply 0).comp hslice
  have heq : (fun x => fderiv ℝ (φ t) x v) =
      fun x => v 0 * streamVel φ t x 1 + v 1 * -streamVel φ t x 0 := by
    funext x
    rw [hv, map_add, map_smul, map_smul, (fderiv_basis_of_streamVel t x).1,
      (fderiv_basis_of_streamVel t x).2, smul_eq_mul, smul_eq_mul]
    simp [basisVec]
  rw [heq]
  exact (continuous_const.mul h0).add (continuous_const.mul h1.neg)

end AVRegularity.Applications
end
end
end

section
/-! # The number of additional levels

Iterated rounded-scale bounds, the choice of `J` with
`p_J = q^J b_* - (β-γ)(3+s)/2 > 1`, and the price bound
`ϑ_L R_J^{-1-s} ≤ C_J c_s^{-1-s} x^{p_J}` for `x = ε_M`, `L = M+J`,
`R_J = c_s √κ ε_L^{(2-β)/2}`, `κ ≥ x^{β-γ}/2`, `ϑ_L ≤ C ε_{L+1}^β / κ`. -/

@[expose] public section

noncomputable section

namespace AVRegularity.Applications

open AVRegularity

theorem eps_pos {q : ℝ} {Λ m : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) : 0 < ocEpsilon q Λ m :=
  (Scales.epsilon_basic (m := m) hq hΛ).1

theorem eps_le_one {q : ℝ} {Λ m : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) : ocEpsilon q Λ m ≤ 1 :=
  (Scales.epsilon_basic (m := m) hq hΛ).2.1

/-- Iterated upper rounding bound: `ε_{m+j} ≤ A ε_m^{q^j}`. -/
theorem eps_iter_le {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) (j : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ m : ℕ, 1 ≤ m →
      ocEpsilon q Λ (m + j) ≤ A * ocEpsilon q Λ m ^ (q ^ j) := by
  induction j with
  | zero => exact ⟨1, one_pos, fun m _ => by simp⟩
  | succ j ih =>
    obtain ⟨A, hA, hAj⟩ := ih
    refine ⟨2 ^ q * A ^ q, by positivity, fun m hm => ?_⟩
    have hq0 : 0 ≤ q := by linarith
    have hstep := ocEpsilon_succ_le (m := m + j) hq hΛ (by omega)
    have hε := eps_pos (m := m) hq hΛ
    have hεj := eps_pos (m := m + j) hq hΛ
    have hmono : ocEpsilon q Λ (m + j) ^ q ≤ (A * ocEpsilon q Λ m ^ (q ^ j)) ^ q :=
      Real.rpow_le_rpow hεj.le (hAj m hm) hq0
    rw [show m + (j + 1) = m + j + 1 by omega]
    calc ocEpsilon q Λ (m + j + 1) ≤ 2 ^ q * ocEpsilon q Λ (m + j) ^ q := hstep
      _ ≤ 2 ^ q * (A * ocEpsilon q Λ m ^ (q ^ j)) ^ q := by gcongr
      _ = 2 ^ q * A ^ q * ocEpsilon q Λ m ^ (q ^ (j + 1)) := by
          rw [Real.mul_rpow hA.le (Real.rpow_nonneg hε.le _), ← Real.rpow_mul hε.le, pow_succ]
          ring

/-- Iterated lower rounding bound: `a ε_m^{q^j} ≤ ε_{m+j}`. -/
theorem eps_iter_ge {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) (j : ℕ) :
    ∃ a : ℝ, 0 < a ∧ ∀ m : ℕ, 1 ≤ m →
      a * ocEpsilon q Λ m ^ (q ^ j) ≤ ocEpsilon q Λ (m + j) := by
  induction j with
  | zero => exact ⟨1, one_pos, fun m _ => by simp⟩
  | succ j ih =>
    obtain ⟨a, ha, haj⟩ := ih
    refine ⟨a ^ q / 2, by positivity, fun m hm => ?_⟩
    have hq0 : 0 ≤ q := by linarith
    have hstep := ocEpsilon_succ_ge (m := m + j) hq hΛ (by omega)
    have hε := eps_pos (m := m) hq hΛ
    have hmono : (a * ocEpsilon q Λ m ^ (q ^ j)) ^ q ≤ ocEpsilon q Λ (m + j) ^ q :=
      Real.rpow_le_rpow (by positivity) (haj m hm) hq0
    rw [show m + (j + 1) = m + j + 1 by omega]
    calc a ^ q / 2 * ocEpsilon q Λ m ^ (q ^ (j + 1))
        = (a * ocEpsilon q Λ m ^ (q ^ j)) ^ q / 2 := by
          rw [Real.mul_rpow ha.le (Real.rpow_nonneg hε.le _), ← Real.rpow_mul hε.le, pow_succ]
          ring
      _ ≤ ocEpsilon q Λ (m + j) ^ q / 2 := by gcongr
      _ ≤ ocEpsilon q Λ (m + j + 1) := hstep

/-- The bracket `b_* = βq - (1+s)(2-β)/2` is positive. -/
theorem bstar_pos {α s q : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (hq : 1 < q) :
    0 < (1 + α) * q - (1 + s) * (2 - (1 + α)) / 2 := by
  nlinarith

/-- Choice of the number of additional levels: `p_J > 1`, `J ≥ 1`. -/
theorem exists_levels {α s q : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (hq : 1 < q) :
    ∃ J : ℕ, 1 ≤ J ∧ 1 < q ^ J * ((1 + α) * q - (1 + s) * (2 - (1 + α)) / 2) -
      ((1 + α) - ocGamma α q) * (3 + s) / 2 := by
  set B := (1 + α) * q - (1 + s) * (2 - (1 + α)) / 2
  have hB : 0 < B := bstar_pos hα₀ hα₁ hs₀ hs₁ hq
  set D := ((1 + α) - ocGamma α q) * (3 + s) / 2
  have ht := tendsto_pow_atTop_atTop_of_one_lt hq
  have hev := ht.eventually (Filter.eventually_gt_atTop ((1 + D) / B))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N + 1, by omega, ?_⟩
  have h := hN (N + 1) (by omega)
  rw [div_lt_iff₀ hB] at h
  linarith

/-- Abstract form of the price bound: all powers of the scales combined. -/
theorem price_abstract {x z w κ cs a A β g s qJ qJ1 : ℝ}
    (hx : 0 < x) (hz : 0 < z) (hw : 0 < w) (hκ : 0 < κ) (hcs : 0 < cs) (ha : 0 < a)
    (hA : 0 < A) (hβ : 0 < β) (hβ2 : β < 2) (hs : 0 < s)
    (hwA : w ≤ A * x ^ qJ1) (hza : a * x ^ qJ ≤ z) (hκx : x ^ (β - g) / 2 ≤ κ) :
    w ^ β / κ * (cs * Real.sqrt κ * z ^ ((2 - β) / 2)) ^ (-1 - s) ≤
      (A ^ β * 2 ^ ((3 + s) / 2) * a ^ (-((2 - β) * (1 + s) / 2))) * cs ^ (-1 - s) *
        x ^ (β * qJ1 - (β - g) * (3 + s) / 2 - qJ * ((2 - β) * (1 + s) / 2)) := by
  have hsqrt : Real.sqrt κ = κ ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow κ
  have hzpow : 0 < z ^ ((2 - β) / 2) := Real.rpow_pos_of_pos hz _
  -- expand the left side
  have hL : w ^ β / κ * (cs * Real.sqrt κ * z ^ ((2 - β) / 2)) ^ (-1 - s) =
      cs ^ (-1 - s) * w ^ β * κ ^ (-((3 + s) / 2)) * z ^ (-((2 - β) * (1 + s) / 2)) := by
    rw [hsqrt, Real.mul_rpow (by positivity) hzpow.le, Real.mul_rpow hcs.le (by positivity),
      ← Real.rpow_mul hκ.le, ← Real.rpow_mul hz.le, div_eq_mul_inv, ← Real.rpow_neg_one κ]
    have e1 : κ ^ (-1 : ℝ) * κ ^ (1 / 2 * (-1 - s)) = κ ^ (-((3 + s) / 2)) := by
      rw [← Real.rpow_add hκ]; congr 1; ring
    have e2 : (2 - β) / 2 * (-1 - s) = -((2 - β) * (1 + s) / 2) := by ring
    rw [e2]
    calc w ^ β * κ ^ (-1 : ℝ) * (cs ^ (-1 - s) * κ ^ (1 / 2 * (-1 - s)) *
          z ^ (-((2 - β) * (1 + s) / 2)))
        = cs ^ (-1 - s) * w ^ β * (κ ^ (-1 : ℝ) * κ ^ (1 / 2 * (-1 - s))) *
            z ^ (-((2 - β) * (1 + s) / 2)) := by ring
      _ = _ := by rw [e1]
  rw [hL]
  -- bound each factor
  have h1 : w ^ β ≤ (A * x ^ qJ1) ^ β := Real.rpow_le_rpow hw.le hwA hβ.le
  have h2 : κ ^ (-((3 + s) / 2)) ≤ (x ^ (β - g) / 2) ^ (-((3 + s) / 2)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hκx (by linarith)
  have h3 : z ^ (-((2 - β) * (1 + s) / 2)) ≤ (a * x ^ qJ) ^ (-((2 - β) * (1 + s) / 2)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hza (by nlinarith)
  have hc : 0 ≤ cs ^ (-1 - s) := Real.rpow_nonneg hcs.le _
  calc cs ^ (-1 - s) * w ^ β * κ ^ (-((3 + s) / 2)) * z ^ (-((2 - β) * (1 + s) / 2))
      ≤ cs ^ (-1 - s) * (A * x ^ qJ1) ^ β * (x ^ (β - g) / 2) ^ (-((3 + s) / 2)) *
          (a * x ^ qJ) ^ (-((2 - β) * (1 + s) / 2)) := by
        gcongr
    _ = (A ^ β * 2 ^ ((3 + s) / 2) * a ^ (-((2 - β) * (1 + s) / 2))) * cs ^ (-1 - s) *
          x ^ (β * qJ1 - (β - g) * (3 + s) / 2 - qJ * ((2 - β) * (1 + s) / 2)) := by
        rw [Real.mul_rpow hA.le (Real.rpow_nonneg hx.le _),
          Real.div_rpow (Real.rpow_nonneg hx.le _) (by norm_num),
          Real.mul_rpow ha.le (Real.rpow_nonneg hx.le _),
          ← Real.rpow_mul hx.le, ← Real.rpow_mul hx.le, ← Real.rpow_mul hx.le,
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        have hx3 : x ^ (qJ1 * β) * x ^ ((β - g) * -((3 + s) / 2)) *
            x ^ (qJ * -((2 - β) * (1 + s) / 2)) =
            x ^ (β * qJ1 - (β - g) * (3 + s) / 2 - qJ * ((2 - β) * (1 + s) / 2)) := by
          rw [← Real.rpow_add hx, ← Real.rpow_add hx]; congr 1; ring
        rw [← hx3]
        have h2pos : (0 : ℝ) < 2 ^ ((3 + s) / 2) := by positivity
        field_simp

end AVRegularity.Applications
end
end
end

section
/-! # Elementary facts for the large-terminal-index step

Monotonicity and decay of the rounded scales, smallness of powers, and monotonicity of
`CsNormLe` in its bound. -/

@[expose] public section

noncomputable section

namespace AVRegularity.Applications

open AVRegularity Homogenization

theorem eps_succ_le_half {q : ℝ} {Λ m : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) :
    ocEpsilon q Λ (m + 1) ≤ ocEpsilon q Λ m / 2 := by
  have h := Scales.epsilon_ratio_lower (m := m + 1) hq hΛ (by omega)
  simp only [Nat.add_sub_cancel] at h
  have hpos := eps_pos (m := m + 1) hq hΛ
  have hΛr : (2 : ℝ) ≤ Λ := by exact_mod_cast (by omega : 2 ≤ Λ)
  rw [ge_iff_le, le_div_iff₀ hpos] at h
  nlinarith

theorem eps_antitone {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) {m n : ℕ} (hmn : m ≤ n) :
    ocEpsilon q Λ n ≤ ocEpsilon q Λ m := by
  induction hmn with
  | refl => exact le_rfl
  | @step k _ ih =>
    have h := eps_succ_le_half (m := k) hq hΛ
    have hpos := eps_pos (m := k) hq hΛ
    linarith

theorem eps_le_half_pow {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) (m : ℕ) :
    ocEpsilon q Λ m ≤ (1 / 2) ^ m := by
  induction m with
  | zero => simpa using eps_le_one (m := 0) hq hΛ
  | succ m ih =>
    calc ocEpsilon q Λ (m + 1) ≤ ocEpsilon q Λ m / 2 := eps_succ_le_half hq hΛ
      _ ≤ (1 / 2) ^ m / 2 := by gcongr
      _ = (1 / 2) ^ (m + 1) := by ring

theorem eps_eventually_le {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ocEpsilon q Λ M ≤ δ := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨N, fun M hM => ?_⟩
  calc ocEpsilon q Λ M ≤ ocEpsilon q Λ N := eps_antitone hq hΛ hM
    _ ≤ (1 / 2) ^ N := eps_le_half_pow hq hΛ N
    _ ≤ δ := hN.le

/-- Smallness of a positive power. -/
theorem exists_small_pow {K e target : ℝ} (hK : 0 ≤ K) (he : 0 < e) (ht : 0 < target) :
    ∃ δ > 0, ∀ x : ℝ, 0 ≤ x → x ≤ δ → K * x ^ e ≤ target := by
  set δ := (target / (K + 1)) ^ (1 / e)
  have hδ : 0 < δ := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨δ, hδ, fun x hx hxδ => ?_⟩
  have h1 : x ^ e ≤ δ ^ e := Real.rpow_le_rpow hx hxδ he.le
  have h2 : δ ^ e = target / (K + 1) := by
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel he.ne', Real.rpow_one]
  calc K * x ^ e ≤ K * (target / (K + 1)) := by rw [← h2]; gcongr
    _ ≤ (K + 1) * (target / (K + 1)) := by gcongr; linarith
    _ = target := by field_simp

theorem csNormLe_mono {s K K' : ℝ} {g : Vec 2 → ℝ} (h : CsNormLe s g K) (hKK : K ≤ K') :
    CsNormLe s g K' := fun x y z hyz => (h x y z hyz).trans hKK

end AVRegularity.Applications
end
end
end

section
/-! # Smallness of the microscopic radius for large terminal indices

Abstract-real lemmas for the smallness caps at large terminal indices. -/

@[expose] public section

noncomputable section

namespace AVRegularity.Applications

/-- `R_J = c_s √κ z^{(2-β)/2} ≤ √(2X)` when `c_s ≤ 1`, `κ ≤ 2X`, `z ≤ 1`. -/
theorem radius_le {cs κ X z e : ℝ} (hcs1 : cs ≤ 1) (hκ : κ ≤ 2 * X)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (he : 0 ≤ e) :
    cs * Real.sqrt κ * z ^ e ≤ Real.sqrt (2 * X) := by
  have h1 : z ^ e ≤ 1 := Real.rpow_le_one hz0 hz1 he
  have h2 : Real.sqrt κ ≤ Real.sqrt (2 * X) := Real.sqrt_le_sqrt hκ
  have h3 : 0 ≤ Real.sqrt κ := Real.sqrt_nonneg _
  have h4 : 0 ≤ z ^ e := Real.rpow_nonneg hz0 e
  calc cs * Real.sqrt κ * z ^ e ≤ 1 * Real.sqrt κ * 1 := by gcongr
    _ ≤ Real.sqrt (2 * X) := by simpa using h2

/-- `R_J² / κ = c_s² z^{2-β}`. -/
theorem radius_sq_div {cs κ z β : ℝ} (hκ : 0 < κ) (hz : 0 < z) :
    (cs * Real.sqrt κ * z ^ ((2 - β) / 2)) ^ 2 / κ = cs ^ 2 * z ^ (2 - β) := by
  rw [mul_pow, mul_pow, Real.sq_sqrt hκ.le, ← Real.rpow_natCast (z ^ ((2 - β) / 2)) 2,
    ← Real.rpow_mul hz.le]
  field_simp
  congr 2
  push_cast
  ring

/-- `ϑ = C w^β / κ ≤ 2 C A^β x^{β qJ1 - (β-γ)}` from `w ≤ A x^{qJ1}`, `κ ≥ x^{β-γ}/2`. -/
theorem tail_le {C A w x κ β g qJ1 : ℝ} (hC : 0 ≤ C) (hA : 0 < A) (hw : 0 < w) (hx : 0 < x)
    (hβ : 0 < β) (hwA : w ≤ A * x ^ qJ1) (hκ : x ^ (β - g) / 2 ≤ κ) :
    C * w ^ β / κ ≤ (2 * C * A ^ β) * x ^ (β * qJ1 - (β - g)) := by
  have hκpos : 0 < κ := lt_of_lt_of_le (by positivity) hκ
  have h1 : w ^ β ≤ (A * x ^ qJ1) ^ β := Real.rpow_le_rpow hw.le hwA hβ.le
  rw [div_le_iff₀ hκpos]
  have h2 : (A * x ^ qJ1) ^ β = A ^ β * x ^ (β * qJ1) := by
    rw [Real.mul_rpow hA.le (Real.rpow_nonneg hx.le _), ← Real.rpow_mul hx.le, mul_comm qJ1]
  have h3 : x ^ (β * qJ1 - (β - g)) * x ^ (β - g) = x ^ (β * qJ1) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  have hxg : 0 < x ^ (β - g) := Real.rpow_pos_of_pos hx _
  calc C * w ^ β ≤ C * (A ^ β * x ^ (β * qJ1)) := by rw [← h2]; gcongr
    _ = (2 * C * A ^ β) * x ^ (β * qJ1 - (β - g)) * (x ^ (β - g) / 2) := by
        rw [← h3]; ring
    _ ≤ (2 * C * A ^ β) * x ^ (β * qJ1 - (β - g)) * κ := by
        gcongr

end AVRegularity.Applications
end
end
end

section
/-! # Large terminal indices

For `M ≥ M₀` and `κ ∈ 𝒦_M`, the full energy solution
obeys the global `C^s` bound, from the finite theorem (at `L = M + J`) through the transfer.
Both enter as explicit hypotheses: `OcFiniteStatement` and `TransferStmt s`. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Homogenization AVenhance

namespace AVRegularity.Applications

/-- The limit velocity of the construction is the Hölder velocity of `exists_limit_velocity`. -/
theorem limit_isHolderDivFree (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : IsOCStreamSeq α q Λ ζ Φ) (b : ℝ → Vec 2 → Vec 2)
    (hb : ∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) :
    IsHolderDivFreeVelocity α b := by
  obtain ⟨b', hb', hhold⟩ :=
    Velocity.exists_limit_velocity α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ
  have heq : b = b' := funext fun t => funext fun x => tendsto_nhds_unique (hb t x) (hb' t x)
  rw [heq]; exact hhold

theorem finite_velocity_continuous {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hζ : IsFastProfile ζ) (hΛ : 128 ≤ Λ) (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) :
    Continuous (fun p : ℝ × Vec 2 => streamVel (Φ m) p.1 p.2) :=
  ((AVenhance.Infra.Construction.smoothPeriodic_streamVel
    (Velocity.streamSeq_admissible hζ hΛ hΦ m)).smooth).continuous

theorem isSmoothStream_of_seq {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hζ : IsFastProfile ζ) (hΛ : 128 ≤ Λ) (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) :
    IsSmoothStream (Φ m) := by
  have h := Velocity.streamSeq_admissible hζ hΛ hΦ m
  refine ⟨h.1, fun t k x => ?_⟩
  simpa using h.2 0 k t x

end AVRegularity.Applications
end
end
end

section
/-! # Large terminal indices: the estimate -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Homogenization AVenhance

namespace AVRegularity.Applications

/-- The smallness constants for large terminal indices, chosen before the terminal index. -/
theorem large_index_caps {β g qJ1 Cφ A η t₀ : ℝ} (hβg : 0 < β - g) (hβ2 : β < 2)
    (hexp : 0 < β * qJ1 - (β - g)) (hCφ : 0 ≤ Cφ) (hA : 0 < A) (hη : 0 < η) (ht₀ : 0 < t₀) :
    ∃ δ > 0, δ ≤ 1 ∧ ∀ x : ℝ, 0 < x → x ≤ δ →
      Real.sqrt 2 * x ^ ((β - g) / 2) ≤ 1 / 8 ∧ x ^ (2 - β) ≤ min (t₀ / 2) 1 ∧
      (2 * Cφ * A ^ β) * x ^ (β * qJ1 - (β - g)) ≤ η / 2 := by
  obtain ⟨δ1, hδ1, h1⟩ := exists_small_pow (K := Real.sqrt 2) (e := (β - g) / 2)
    (target := 1 / 8) (Real.sqrt_nonneg _) (by linarith) (by norm_num)
  obtain ⟨δ2, hδ2, h2⟩ := exists_small_pow (K := 1) (e := 2 - β) (target := min (t₀ / 2) 1)
    zero_le_one (by linarith) (lt_min (by linarith) one_pos)
  obtain ⟨δ3, hδ3, h3⟩ := exists_small_pow (K := 2 * Cφ * A ^ β) (e := β * qJ1 - (β - g))
    (target := η / 2) (by positivity) hexp (by linarith)
  refine ⟨min (min δ1 δ2) (min δ3 1), by positivity, (min_le_right _ _).trans (min_le_right _ _),
    fun x hx hxδ => ⟨h1 x hx.le (hxδ.trans ((min_le_left _ _).trans (min_le_left _ _))), ?_,
      h3 x hx.le (hxδ.trans ((min_le_right _ _).trans (min_le_left _ _)))⟩⟩
  simpa using h2 x hx.le (hxδ.trans ((min_le_left _ _).trans (min_le_right _ _)))

theorem sqrt_two_mul_rpow {x e : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (2 * x ^ e) = Real.sqrt 2 * x ^ (e / 2) := by
  rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow (x ^ e), ← Real.rpow_mul hx]
  ring_nf

/-- **Large terminal indices**, conditional on the finite theorem
and the transfer. -/
theorem large_terminal_index (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (hfin : OcFiniteStatement α s q ζ)
    (htr : TransferStmt s) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
      ∀ b : ℝ → Vec 2 → Vec 2, (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) →
      ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ M₀ : ℕ, 1 ≤ M₀ ∧ ∃ C₁ : ℝ,
        ∀ M : ℕ, M₀ ≤ M →
        ∀ κ ∈ Set.Icc (ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q) / 2)
            (2 * ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q)),
        ∀ a : ℝ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
        ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ →
          ∀ t ∈ Set.Icc (a + t₀) (a + T), ∃ Θt : Vec 2 → ℝ,
            IsZ2Periodic Θt ∧ Θt =ᵐ[volume.restrict unitCube] θ t ∧
            CsNormLe s Θt (C₁ * Real.sqrt (l2NormSq f)) := by
  obtain ⟨Λf, -, hfinΛ⟩ := hfin
  refine ⟨max Λf 128, le_max_right _ _, ?_⟩
  intro Λ hΛ Φ hΦ b hb t₀ T ht₀ hT
  have hΛ128 : 128 ≤ Λ := (le_max_right _ _).trans hΛ
  have hΛf : Λf ≤ Λ := (le_max_left _ _).trans hΛ
  have hq1 : 1 < q := hq.1
  obtain ⟨η, Ctr, hη, hCtr, htrans⟩ := htr
  obtain ⟨φ, Cφ, hCφ, -, hφtail, -, hφd, hφb, hφc, hφper, -, hlip, hbm⟩ :=
    stream_tail_bounds α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ128 Φ hΦ b hb
  have hhold := limit_isHolderDivFree α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ128 Φ hΦ b hb
  have hbφ : streamVel φ = b := funext fun t => funext fun x => hφb t x
  have hfull : IsFullStream φ := by
    refine isFullStream_of hφd hφc ?_ ?_ hφper
    · rw [hbφ]; exact IsHolderDivFreeVelocity.continuous hα₀ hhold
    · obtain ⟨B, hB⟩ := hhold.2.2.1
      exact ⟨B, fun t x => by rw [hbφ]; exact hB t x⟩
  obtain ⟨J, hJ1, hpJ⟩ := exists_levels hα₀ hα₁ hs₀ hs₁ hq1
  obtain ⟨Mstar, S0, hS⟩ := hfinΛ Λ hΛf Φ hΦ J hJ1 (t₀ / 2) (T + 1) (by positivity) (by linarith)
  set S := max S0 0
  obtain ⟨A1, hA1, hA1b⟩ := eps_iter_le hq1 hΛ128 (J + 1)
  obtain ⟨a1, ha1, ha1b⟩ := eps_iter_ge hq1 hΛ128 J
  set β : ℝ := 1 + α
  set g : ℝ := ocGamma α q
  have hβg : 0 < β - g := by
    simp only [β, g, ocGamma]
    have hq0 : 0 < q + 1 := by linarith
    have heq : (1 + α) - (q - 1) * (1 + α) / (q + 1) = 2 * (1 + α) / (q + 1) := by
      rw [eq_div_iff hq0.ne', sub_mul, div_mul_cancel₀ _ hq0.ne']; ring
    rw [heq]
    positivity
  have hβ2 : β < 2 := by simp only [β]; linarith
  have hβ0 : 0 < β := by simp only [β]; linarith
  have hexp : 0 < β * q ^ (J + 1) - (β - g) := by
    have hqJ : 1 ≤ q ^ (J + 1) := one_le_pow₀ hq1.le
    have hg0 : 0 < g := by
      simp only [g, ocGamma]
      have : 0 < q - 1 := by linarith
      positivity
    nlinarith
  -- `c_s`
  set cs : ℝ := min 1 (Real.sqrt (η / (2 * (Cφ + 1))))
  have hcs0 : 0 < cs := lt_min one_pos (Real.sqrt_pos.mpr (by positivity))
  have hcs1 : cs ≤ 1 := min_le_left _ _
  have hcsC : cs ^ 2 * Cφ ≤ η / 2 := by
    have h1 : cs ^ 2 ≤ η / (2 * (Cφ + 1)) := by
      have := min_le_right 1 (Real.sqrt (η / (2 * (Cφ + 1))))
      calc cs ^ 2 ≤ (Real.sqrt (η / (2 * (Cφ + 1)))) ^ 2 := pow_le_pow_left₀ hcs0.le this 2
        _ = η / (2 * (Cφ + 1)) := Real.sq_sqrt (by positivity)
    calc cs ^ 2 * Cφ ≤ η / (2 * (Cφ + 1)) * Cφ := mul_le_mul_of_nonneg_right h1 hCφ
      _ ≤ η / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  obtain ⟨δ, hδ, hδ1, hcaps⟩ := large_index_caps hβg hβ2 hexp hCφ hA1 hη ht₀
  obtain ⟨M₁, hM₁⟩ := eps_eventually_le hq1 hΛ128 hδ
  set P : ℝ := A1 ^ β * 2 ^ ((3 + s) / 2) * a1 ^ (-((2 - β) * (1 + s) / 2))
  have hP : 0 ≤ P := by positivity
  refine ⟨max (max M₁ Mstar) 1, le_max_right _ _, Ctr * (S + Cφ * (P * cs ^ (-1 - s))), ?_⟩
  intro M hM κ hκ a0 f hf θ hθ t ht
  have hMM₁ : M₁ ≤ M := (le_max_left _ _).trans ((le_max_left _ _).trans hM)
  have hMst : Mstar ≤ M := (le_max_right _ _).trans ((le_max_left _ _).trans hM)
  have hM1 : 1 ≤ M := (le_max_right _ _).trans hM
  set x := ocEpsilon q Λ M
  set L := M + J
  set z := ocEpsilon q Λ L
  set w := ocEpsilon q Λ (L + 1)
  have hx0 : 0 < x := eps_pos hq1 hΛ128
  have hz0 : 0 < z := eps_pos hq1 hΛ128
  have hw0 : 0 < w := eps_pos hq1 hΛ128
  have hxδ : x ≤ δ := hM₁ M hMM₁
  have hx1 : x ≤ 1 := eps_le_one hq1 hΛ128
  have hzx : z ≤ x := eps_antitone hq1 hΛ128 (by omega)
  have hz1 : z ≤ 1 := hzx.trans hx1
  obtain ⟨hcR, hch, hcϑ⟩ := hcaps x hx0 hxδ
  have hκlo : x ^ (β - g) / 2 ≤ κ := hκ.1
  have hκhi : κ ≤ 2 * x ^ (β - g) := hκ.2
  have hκ0 : 0 < κ := lt_of_lt_of_le (by positivity) hκlo
  -- radius, time scale, tail
  set R := cs * Real.sqrt κ * z ^ ((2 - β) / 2)
  have hR0 : 0 < R := by positivity
  have hR8 : R ≤ 1 / 8 := by
    have h := radius_le (cs := cs) (e := (2 - β) / 2) hcs1 hκhi hz0.le hz1 (by linarith)
    rw [sqrt_two_mul_rpow hx0.le] at h
    exact h.trans hcR
  have hh : R ^ 2 / κ = cs ^ 2 * z ^ (2 - β) := radius_sq_div hκ0 hz0
  have hzβ : z ^ (2 - β) ≤ x ^ (2 - β) := Real.rpow_le_rpow hz0.le hzx (by linarith)
  have hhle : R ^ 2 / κ ≤ min (t₀ / 2) 1 := by
    rw [hh]
    have : cs ^ 2 ≤ 1 := by nlinarith
    calc cs ^ 2 * z ^ (2 - β) ≤ 1 * x ^ (2 - β) := by
          gcongr
      _ ≤ _ := by simpa using hch
  have hh0 : 0 ≤ R ^ 2 / κ := by positivity
  set ϑ := Cφ * w ^ β / κ
  have hwA : w ≤ A1 * x ^ (q ^ (J + 1)) := by
    have := hA1b M hM1
    rwa [show M + (J + 1) = L + 1 by omega] at this
  have hza : a1 * x ^ (q ^ J) ≤ z := ha1b M hM1
  have hϑ : ϑ ≤ η / 2 := (tail_le hCφ hA1 hw0 hx0 hβ0 hwA hκlo).trans hcϑ
  set DL := Cφ * z ^ (β - 2)
  have hsmall : ϑ + R ^ 2 / κ * DL ≤ η := by
    have hzz : z ^ (2 - β) * z ^ (β - 2) = 1 := by
      rw [← Real.rpow_add hz0]; simp
    have : R ^ 2 / κ * DL = cs ^ 2 * Cφ := by
      rw [hh]; simp only [DL]
      calc cs ^ 2 * z ^ (2 - β) * (Cφ * z ^ (β - 2)) =
          cs ^ 2 * Cφ * (z ^ (2 - β) * z ^ (β - 2)) := by ring
        _ = cs ^ 2 * Cφ := by rw [hzz, mul_one]
    rw [this]; linarith
  -- the two solutions on the longer window
  obtain ⟨θ', hθ', -⟩ :=
    Wellposed.exists_unique_isWeakSolutionOn_of_isHolderDivFreeVelocity α hα₀ b hhold κ hκ0
      a0 (a0 + (T + 1)) (by linarith) f hf
  have hagree := isWeakSolutionOn_extend_eq hα₀ hhold hκ0 (by linarith : a0 < a0 + T)
    (by linarith : a0 + T ≤ a0 + (T + 1)) hf hθ hθ'
  obtain ⟨v, hv, -⟩ := Wellposed.exists_unique_isWeakSolutionOn a0 (a0 + (T + 1))
    (streamVel (Φ L)) (finite_velocity_continuous hζ hΛ128 hΦ L).aestronglyMeasurable
    ⟨Cφ, fun t _ x => hbm L t x⟩
    (fun t _ => Velocity.streamSeq_velocity_spatial_periodic hζ hΛ128 hΦ L t) κ hκ0
    (by linarith) f hf
  have hvb := hS M hMst hM1 κ hκ a0 f hf v hv
  -- apply the transfer
  set F := Real.sqrt (l2NormSq f)
  have hθ'φ : IsWeakSolutionOn (streamVel φ) κ a0 (a0 + (T + 1)) f θ' := by rw [hbφ]; exact hθ'
  have hlipL : ∀ t x y, eNorm (streamVel (Φ L) t x - streamVel (Φ L) t y) ≤
      DL * eNorm (x - y) := fun t x y => by
    simpa [eNorm, DL] using hlip L (by omega) t x y
  have htail : ∀ t x, |φ t x - Φ L t x| ≤ κ * ϑ := fun t x => by
    have h := hφtail L t x
    calc |φ t x - Φ L t x| ≤ Cφ * w ^ β := h
      _ = κ * ϑ := by simp only [ϑ]; field_simp
  have hvwin : ∀ t ∈ Set.Icc (a0 + t₀ - R ^ 2 / κ) (a0 + T + R ^ 2 / κ), ∃ Vt : Vec 2 → ℝ,
      IsZ2Periodic Vt ∧ Vt =ᵐ[volume.restrict unitCube] v t ∧ CsNormLe s Vt (S * F) := by
    intro t ht
    have hmin1 : R ^ 2 / κ ≤ t₀ / 2 := hhle.trans (min_le_left _ _)
    have hmin2 : R ^ 2 / κ ≤ 1 := hhle.trans (min_le_right _ _)
    obtain ⟨Vt, h1, h2, h3⟩ := hvb t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact ⟨Vt, h1, h2, csNormLe_mono h3 (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.sqrt_nonneg _))⟩
  have hmin1 : R ^ 2 / κ ≤ t₀ / 2 := hhle.trans (min_le_left _ _)
  have hmin2 : R ^ 2 / κ ≤ 1 := hhle.trans (min_le_right _ _)
  obtain ⟨Θt, hΘp, hΘae, hΘb⟩ := htrans φ (Φ L) hfull (isSmoothStream_of_seq hζ hΛ128 hΦ L)
    DL κ ϑ R S F a0 (a0 + (T + 1)) (a0 + t₀) (a0 + T) f θ' v hlipL hκ0 htail hR0 hR8 hf le_rfl
    hθ'φ hv (by linarith) (by linarith) (by linarith) (le_max_right _ _) hvwin hsmall t ht
  refine ⟨Θt, hΘp, hΘae.trans (hagree t ⟨by linarith [ht.1], ht.2⟩), ?_⟩
  -- the price of the stream tail
  have hprice : ϑ * R ^ (-1 - s) ≤ Cφ * (P * cs ^ (-1 - s)) := by
    have h := price_abstract (s := s) hx0 hz0 hw0 hκ0 hcs0 ha1 hA1 hβ0 hβ2 hs₀ hwA hza hκlo
    have hexpeq : β * q ^ (J + 1) - (β - g) * (3 + s) / 2 - q ^ J * ((2 - β) * (1 + s) / 2) =
        q ^ J * ((1 + α) * q - (1 + s) * (2 - (1 + α)) / 2) -
          ((1 + α) - ocGamma α q) * (3 + s) / 2 := by
      simp only [β, g]; rw [pow_succ]; ring
    rw [hexpeq] at h
    have hxp : x ^ (q ^ J * ((1 + α) * q - (1 + s) * (2 - (1 + α)) / 2) -
        ((1 + α) - ocGamma α q) * (3 + s) / 2) ≤ 1 :=
      Real.rpow_le_one hx0.le hx1 (by linarith)
    have hPc : 0 ≤ P * cs ^ (-1 - s) := mul_nonneg hP (Real.rpow_nonneg hcs0.le _)
    calc ϑ * R ^ (-1 - s) = Cφ * (w ^ β / κ * R ^ (-1 - s)) := by simp only [ϑ]; ring
      _ ≤ Cφ * (P * cs ^ (-1 - s) * 1) :=
          mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left hxp hPc)) hCφ
      _ = Cφ * (P * cs ^ (-1 - s)) := by ring
  refine csNormLe_mono hΘb ?_
  have hF : 0 ≤ F := Real.sqrt_nonneg _
  gcongr

end AVRegularity.Applications
end
end
end

section
/-! # The global statement from the finite one

Large terminal indices by the transfer, the finitely many remaining bands by the compact-range
estimate, and joint continuity of the representatives, as in the proof of Theorem A of the paper.
`CompactRangeStmt` is the statement of the compact-range estimate. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Homogenization AVenhance

namespace AVRegularity.Applications

/-- **The compact-range estimate** for a Hölder velocity: on a compact range of
diffusivities `[κ_min, 2]` the energy solutions obey the `C^s(𝕋²)` bound after a waiting time. -/
def CompactRangeStmt (α s : ℝ) : Prop :=
  ∀ b : ℝ → Vec 2 → Vec 2, IsHolderDivFreeVelocity α b → ∀ κmin : ℝ, 0 < κmin →
  ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C₂ : ℝ,
    ∀ κ ∈ Set.Icc κmin 2, ∀ a : ℝ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
    ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ →
      ∀ t ∈ Set.Icc (a + t₀) (a + T), ∃ Θt : Vec 2 → ℝ,
        IsZ2Periodic Θt ∧ Θt =ᵐ[volume.restrict unitCube] θ t ∧
        CsNormLe s Θt (C₂ * Real.sqrt (l2NormSq f))

theorem rpow_band_antitone {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) {e : ℝ} (he : 0 ≤ e)
    {m n : ℕ} (hmn : m ≤ n) : ocEpsilon q Λ n ^ e ≤ ocEpsilon q Λ m ^ e :=
  Real.rpow_le_rpow (eps_pos hq hΛ).le (eps_antitone hq hΛ hmn) he

/-- **finite ⇒ global**, given the transfer and the
compact-range estimate. -/
theorem oc_global_of_finite_transfer_compact (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (hfin : OcFiniteStatement α s q ζ)
    (htr : TransferStmt s) (hcomp : CompactRangeStmt α s) : OcGlobalStatement α s q ζ := by
  obtain ⟨Λ₀, hΛ₀, hlarge⟩ :=
    large_terminal_index α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ hfin htr
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ Φ hΦ b hb t₀ T ht₀ hT
  have hΛ128 : 128 ≤ Λ := hΛ₀.trans hΛ
  have hq1 : 1 < q := hq.1
  have hhold := limit_isHolderDivFree α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ128 Φ hΦ b hb
  obtain ⟨M₀, hM₀, C₁, hC₁⟩ := hlarge Λ hΛ Φ hΦ b hb t₀ T ht₀ hT
  set e : ℝ := (1 + α) - ocGamma α q
  have he : 0 < e := by
    simp only [e, ocGamma]
    have hq0 : 0 < q + 1 := by linarith
    have heq : (1 + α) - (q - 1) * (1 + α) / (q + 1) = 2 * (1 + α) / (q + 1) := by
      rw [eq_div_iff hq0.ne', sub_mul, div_mul_cancel₀ _ hq0.ne']; ring
    rw [heq]; positivity
  set κmin : ℝ := ocEpsilon q Λ M₀ ^ e / 2
  have hκmin : 0 < κmin := by have := eps_pos (m := M₀) hq1 hΛ128; positivity
  obtain ⟨C₂, hC₂⟩ := hcomp b hhold κmin hκmin t₀ T ht₀ hT
  set C := max (max C₁ C₂) 0
  refine ⟨C, ?_⟩
  intro a κ hκ f hf θ hθ
  -- the per-time representatives
  have hrep : ∀ t ∈ Set.Icc (a + t₀) (a + T), ∃ Θt : Vec 2 → ℝ,
      IsZ2Periodic Θt ∧ Θt =ᵐ[volume.restrict unitCube] θ t ∧
      CsNormLe s Θt (C * Real.sqrt (l2NormSq f)) := by
    intro t ht
    have hF : 0 ≤ Real.sqrt (l2NormSq f) := Real.sqrt_nonneg _
    obtain ⟨M, hM, hκM⟩ : ∃ M : ℕ, 1 ≤ M ∧ κ ∈ Set.Icc (ocEpsilon q Λ M ^ e / 2)
        (2 * ocEpsilon q Λ M ^ e) := by
      simp only [ocBandSet, Set.mem_iUnion] at hκ
      obtain ⟨M, hM, hκ⟩ := hκ
      exact ⟨M, hM, hκ⟩
    by_cases hMM : M₀ ≤ M
    · obtain ⟨Θt, h1, h2, h3⟩ := hC₁ M hMM κ hκM a f hf θ hθ t ht
      exact ⟨Θt, h1, h2, csNormLe_mono h3 (mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_left _ _)) hF)⟩
    · push Not at hMM
      have hlo : κmin ≤ κ := by
        have := rpow_band_antitone hq1 hΛ128 he.le hMM.le
        simp only [κmin]
        linarith [hκM.1]
      have hhi : κ ≤ 2 := by
        have h1 : ocEpsilon q Λ M ^ e ≤ 1 :=
          Real.rpow_le_one (eps_pos hq1 hΛ128).le (eps_le_one hq1 hΛ128) he.le
        linarith [hκM.2]
      obtain ⟨Θt, h1, h2, h3⟩ := hC₂ κ ⟨hlo, hhi⟩ a f hf θ hθ t ht
      exact ⟨Θt, h1, h2, csNormLe_mono h3 (mul_le_mul_of_nonneg_right
        ((le_max_right _ _).trans (le_max_left _ _)) hF)⟩
  classical
  set Θ : ℝ → Vec 2 → ℝ := fun t =>
    if ht : t ∈ Set.Icc (a + t₀) (a + T) then Classical.choose (hrep t ht) else 0
  have hΘ : ∀ t ∈ Set.Icc (a + t₀) (a + T), IsZ2Periodic (Θ t) ∧
      Θ t =ᵐ[volume.restrict unitCube] θ t ∧ CsNormLe s (Θ t) (C * Real.sqrt (l2NormSq f)) := by
    intro t ht
    simp only [Θ, ht, ↓reduceDIte]
    exact Classical.choose_spec (hrep t ht)
  refine ⟨Θ, ?_, hΘ⟩
  exact continuousOn_of_csNormLe_slices hθ hs₀
    (Set.Icc_subset_Icc (by linarith) le_rfl) hΘ

end AVRegularity.Applications
end
end
end

section
/-! # Compact diffusivity ranges

On `[κ_min, 2]` the full-velocity tube consequence of the
microscopic lemma, with radius `r = min{1/8, c κ_min^{1/(1+α)}, √(κ_min t₀/2)}` and the scalar
energy bound `A ≤ ‖f‖₂`, gives `‖θ(t)‖_{C^s} ≤ C r^{-1-s} ‖f‖₂` after the waiting time `t₀`.
The periodic lift of a weak solution and the energy bound enter as explicit hypotheses. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Homogenization AVenhance Set

namespace AVRegularity.Applications

/-- Local weak solutions only depend on the values in the open set. -/
theorem isLocalWeakSolution_congr {v : ℝ → Vec 2 → Vec 2} {κ : ℝ} {O : Set (ℝ × Vec 2)}
    (hO : MeasurableSet O) {u u' : ℝ × Vec 2 → ℝ} {Du : ℝ × Vec 2 → Vec 2}
    (heq : ∀ p ∈ O, u p = u' p) (h : IsLocalWeakSolution v κ O u Du) :
    IsLocalWeakSolution v κ O u' Du := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun Kc hKc hcpt => ?_, h2, ?_, fun φ hφ => ?_⟩
  · refine (h1 Kc hKc hcpt).ae_eq ?_
    exact (ae_restrict_iff' hcpt.isClosed.measurableSet).2
      (Eventually.of_forall fun p hp => heq p (hKc hp))
  · filter_upwards [h3] with t ht
    intro i ψ hψ hcs hts
    have hmeas : MeasurableSet (timeSection O t) := hO.preimage measurable_prodMk_left
    rw [← ht i ψ hψ hcs hts]
    refine setIntegral_congr_fun hmeas fun x hx => ?_
    simp only [heq (t, x) hx]
  · rw [← h4 φ hφ]
    refine setIntegral_congr_fun hO fun p hp => ?_
    simp only [heq p hp]

/-- **Compact diffusivity ranges**, from the periodic lift and the energy bound. -/
theorem compactRange_of_tools {α s : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) (hs₀ : 0 < s) (hs₁ : s < 1)
    (hlift : ∀ (b : ℝ → Vec 2 → Vec 2), IsHolderDivFreeVelocity α b →
      ∀ (κ t₁ t₂ : ℝ) (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ), 0 < κ → t₁ < t₂ →
      MemL2On unitCube f → IsWeakSolutionOn b κ t₁ t₂ f θ →
      ∃ Dθ : ℝ × Vec 2 → Vec 2,
        IsLocalWeakSolution b κ (Set.Ioo t₁ t₂ ×ˢ Set.univ) (fun p => θ p.1 p.2) Dθ)
    (henergy : ∀ (b : ℝ → Vec 2 → Vec 2), IsHolderDivFreeVelocity α b →
      ∀ (κ t₁ t₂ : ℝ) (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ), 0 < κ → t₁ < t₂ →
      MemL2On unitCube f → IsWeakSolutionOn b κ t₁ t₂ f θ →
      ∀ t ∈ Set.Icc t₁ t₂, l2NormSq (θ t) ≤ l2NormSq f) :
    CompactRangeStmt α s := by
  intro b hb κmin hκmin t₀ T ht₀ hT
  set a' : ℝ := (1 + s) / 2
  obtain ⟨c, C, hc, hC, H⟩ := tube_regularity_periodic ocMicroscopicStatement_holds hα₀ hα₁ hb
    hs₀ (show s < a' by simp only [a']; linarith) (show a' < 1 by simp only [a']; linarith)
  set r : ℝ := min (1 / 8) (min (c * κmin ^ (1 / (1 + α))) (Real.sqrt (κmin * t₀ / 2)))
  have hr0 : 0 < r := lt_min (by norm_num) (lt_min (by positivity) (Real.sqrt_pos.2 (by positivity)))
  have hr8 : r ≤ 1 / 8 := min_le_left _ _
  refine ⟨C * r ^ (-1 - s), ?_⟩
  intro κ hκ a f hf θ hθ t ht
  have hκ0 : 0 < κ := lt_of_lt_of_le hκmin hκ.1
  obtain ⟨θ', hθ', -⟩ :=
    Wellposed.exists_unique_isWeakSolutionOn_of_isHolderDivFreeVelocity α hα₀ b hb κ hκ0
      a (a + T + 1) (by linarith) f hf
  have hagree := isWeakSolutionOn_extend_eq hα₀ hb hκ0 (by linarith : a < a + T)
    (by linarith : a + T ≤ a + T + 1) hf hθ hθ'
  obtain ⟨Dθ, hlocal⟩ := hlift b hb κ a (a + T + 1) f θ' hκ0 (by linarith) hf hθ'
  set O : Set (ℝ × Vec 2) := Set.Ioo a (a + T + 1) ×ˢ Set.univ
  have hOo : IsOpen O := isOpen_Ioo.prod isOpen_univ
  -- a representative periodic at every time
  have hθ'' := hθ'
  obtain ⟨Dθ', hsl, -⟩ := hθ''
  set w : ℝ × Vec 2 → ℝ := fun p => if p.1 ∈ Set.Icc a (a + T + 1) then θ' p.1 p.2 else 0
  have hw : IsLocalWeakSolution b κ O w Dθ := by
    refine isLocalWeakSolution_congr hOo.measurableSet (fun p hp => ?_) hlocal
    simp only [w, show p.1 ∈ Set.Icc a (a + T + 1) from ⟨hp.1.1.le, hp.1.2.le⟩, ↓reduceIte]
  have hwper : ∀ τ y (n : Fin 2 → ℤ), w (τ, y + AVenhance.latticeShift n) = w (τ, y) := by
    intro τ y n
    by_cases hτ : τ ∈ Set.Icc a (a + T + 1)
    · simp only [w, hτ, ↓reduceIte]; exact (hsl τ hτ).1 n y
    · simp only [w, hτ, ↓reduceIte]
  have hOper : ∀ p ∈ O, ∀ n : Fin 2 → ℤ, (p.1, p.2 + AVenhance.latticeShift n) ∈ O :=
    fun p hp n => ⟨hp.1, trivial⟩
  set A := Real.sqrt (l2NormSq f)
  have hA : ∀ᵐ τ ∂(volume : Measure ℝ), (∃ x, (τ, x) ∈ O) →
      IntegrableOn (fun y => w (τ, y) ^ 2) unitCube ∧ ∫ y in unitCube, w (τ, y) ^ 2 ≤ A ^ 2 := by
    refine Eventually.of_forall fun τ ⟨x, hx⟩ => ?_
    have hτ : τ ∈ Set.Icc a (a + T + 1) := ⟨hx.1.1.le, hx.1.2.le⟩
    have hwτ : (fun y => w (τ, y) ^ 2) = fun y => θ' τ y ^ 2 := by
      funext y; simp only [w, hτ, ↓reduceIte]
    rw [hwτ]
    refine ⟨(hsl τ hτ).2.integrable_sq, ?_⟩
    have he := henergy b hb κ a (a + T + 1) f θ' hκ0 (by linarith) hf hθ' τ hτ
    have hl : 0 ≤ l2NormSq f := setIntegral_nonneg_of_ae_restrict
      (Eventually.of_forall fun _ => sq_nonneg _)
    simp only [A, Real.sq_sqrt hl]
    exact he
  have hrc : r ≤ c * κ ^ (1 / (1 + α)) := by
    refine (min_le_right _ _).trans ((min_le_left _ _).trans ?_)
    gcongr
    exact hκ.1
  have hr2 : r ^ 2 / κ ≤ t₀ / 2 := by
    have h1 : r ≤ Real.sqrt (κmin * t₀ / 2) := (min_le_right _ _).trans (min_le_right _ _)
    have h2 : r ^ 2 ≤ κmin * t₀ / 2 := by
      calc r ^ 2 ≤ Real.sqrt (κmin * t₀ / 2) ^ 2 := pow_le_pow_left₀ hr0.le h1 2
        _ = κmin * t₀ / 2 := Real.sq_sqrt (by positivity)
    rw [div_le_iff₀ hκ0]
    nlinarith [hκ.1]
  have htube : ∀ x : Vec 2, ∀ X : ℝ → Vec 2, IsBackwardTrajectory b X t (r ^ 2 / κ) →
      X t = x → closedTube X t r κ ⊆ O := by
    intro x X _ _ p hp
    obtain ⟨⟨hp1, hp2⟩, -⟩ := hp
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, trivial⟩
  obtain ⟨W, hWp, hWc, hWtr, hWb⟩ := H κ hκ0 O hOo hOper w Dθ hw hwper A (Real.sqrt_nonneg _) hA
    r hr0 hr8 hrc t htube
  refine ⟨W, hWp, ?_, fun x y z hyz => hWb x y z hyz⟩
  have hWθ' : W =ᵐ[volume.restrict unitCube] θ' t := by
    refine ae_eq_of_trace_from_below hθ' (by linarith [ht.1]) (by linarith [ht.2])
      (by positivity : (0 : ℝ) < r / 4) (by linarith) hWc fun x => ?_
    refine (hWtr x).congr' ?_
    have hnear : Set.Ioo a t ∈ 𝓝[<] t := Ioo_mem_nhdsLT (by linarith [ht.1])
    filter_upwards [mem_inf_of_left hnear] with σ hσ
    have hσ' : σ ∈ Set.Icc a (a + T + 1) := ⟨hσ.1.le, by linarith [hσ.2, ht.2]⟩
    simp only [w, hσ', ↓reduceIte]
  exact hWθ'.trans (hagree t ⟨by linarith [ht.1], ht.2⟩)

end AVRegularity.Applications
end
end
end

section
/-! # Compact diffusivity ranges, unconditionally -/

@[expose] public section

open MeasureTheory Homogenization AVenhance

namespace AVRegularity.Applications

/-- **Compact diffusivity ranges**. -/
theorem compactRange_holds {α s : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) (hs₀ : 0 < s) (hs₁ : s < 1) :
    CompactRangeStmt α s := by
  refine compactRange_of_tools hα₀ hα₁ hs₀ hs₁ ?_ ?_
  · intro b hb κ t₁ t₂ f θ _ _ _ hθ
    obtain ⟨Dθ, -, h⟩ := isLocalWeakSolution_of_isWeakSolutionOn (fun t _ => hb.1 t) hθ
    exact ⟨fun p => Dθ p.1 p.2, h⟩
  · intro b hb κ t₁ t₂ f θ hκ h12 hf hθ
    exact (l2NormSq_le_of_isHolderDivFreeVelocity hα₀ hb hκ h12 hf hθ).1

end AVRegularity.Applications
end
end
end
