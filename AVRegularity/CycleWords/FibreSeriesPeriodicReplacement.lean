-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CoupledEnergyPlane.ActionODE
public import AVRegularity.Definitions.CycleEvolution.IsFibreGraph
import AVRegularity.Analysis.Schur.Finite
public import AVRegularity.CycleEvolution.TimeEnergy
public import AVRegularity.CycleWords.QuietDurationAlgebra
public import AVRegularity.CoupledEnergyPlane.Fourier.DistributionDerivative
import AVRegularity.CycleWords.ShearFrequencyAlgebra
public import AVRegularity.Statements.Intermediate.CycleComparison.IsBoxSmooth
public import AVRegularity.Definitions.CycleWords.IsGeometryCover
import AVRegularity.CycleWords.FinitePiLpStrongMeasurable
import AVenhance.Infra.ODE.Linear.Energy
import Homogenization.Sobolev.H1.BasicLemmas
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Dynamics.Ergodic.Action.Regular

section
@[expose] public section
namespace AVRegularity.CycleWords

/-! One last short window retains the full elapsed-time gap and smoothing singularity. -/

theorem shortSmoothingTail_price (J : ℕ) (C δ₀ τ : ℝ)
    (hC : 0 ≤ C) (hδ₀ : 0 < δ₀) (hτ : 0 < τ) :
    (C / (min δ₀ τ / ((J : ℝ) + 1))) ^ J ≤
      (C * ((J : ℝ) + 1) / δ₀) ^ J + (C * ((J : ℝ) + 1) / τ) ^ J := by
  by_cases h : δ₀ ≤ τ
  · rw [min_eq_left h, div_div_eq_mul_div]
    exact le_add_of_nonneg_right (pow_nonneg (div_nonneg (mul_nonneg hC (by positivity)) hτ.le) J)
  · rw [min_eq_right (le_of_not_ge h), div_div_eq_mul_div]
    exact le_add_of_nonneg_left (pow_nonneg (div_nonneg (mul_nonneg hC (by positivity)) hδ₀.le) J)

theorem shortSmoothingTail_gap (γ τ d : ℝ) (hγ : 0 ≤ γ) (hd : d ≤ 1) :
    Real.exp (-γ * (τ - d)) ≤ Real.exp γ * Real.exp (-γ * τ) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hd hγ
  linarith only [hh]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleWords

/-! Compact smooth coefficients have uniform finite jet bounds under every contracting spatial rescale. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_smoothCompact_rescale_jet_bound (f : Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => f (ρ • y)) x‖ ≤ C := by
  have hcont : Continuous (iteratedFDeriv ℝ j f) :=
    hf.continuous_iteratedFDeriv (by simp)
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support (hc.iteratedFDeriv (𝕜 := ℝ) j)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (0 : Vec 2))
  refine ⟨C, hC0, ?_⟩
  intro ρ hρ hρ1 x
  have hfj : ContDiff ℝ (j : ℕ) f := hf.of_le (by simp)
  have hd := congrFun (iteratedFDeriv_comp_const_smul ρ hfj) x
  rw [hd, norm_smul, Real.norm_of_nonneg (pow_nonneg hρ j)]
  calc
    _ ≤ ρ ^ j * C := mul_le_mul_of_nonneg_left (hC _) (pow_nonneg hρ j)
    _ ≤ C := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (pow_le_one₀ hρ hρ1) hC0

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! Classical coordinate derivatives supply the vector-valued weak identities. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

theorem smoothVector_weak_coordinate {f : Vec 2 → E} (hf : ContDiff ℝ 1 f)
    (i : Fin 2) (e : E) :
    HasWeakPartialDerivOn Set.univ i (fun x => inner ℝ e (f x))
      (fun x => inner ℝ e ((fderiv ℝ f x) (basisVec i))) := by
  let A := InnerProductSpace.toDual ℝ E e
  have h := HasWeakPartialDerivOn.of_contDiff (A.contDiff.comp hf) (i := i) (U := Set.univ)
  have hd (x : Vec 2) : (fderiv ℝ (A ∘ f) x) (basisVec i) =
      inner ℝ e ((fderiv ℝ f x) (basisVec i)) := by
    rw [fderiv_comp x A.differentiableAt (hf.differentiable (by norm_num) x),
      A.fderiv]
    rfl
  simp_rw [hd] at h
  exact h
end

/-! A continuous classical derivative is identified by the native weak identity, without first assuming global integrability. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem weakDerivative_unique_continuous {i : Fin 2} {u g h : Vec 2 → E}
    (hg : MemLp g 2 volume) (hh : Continuous h)
    (hgw : ∀ e : E, HasWeakPartialDerivOn Set.univ i (fun x => inner ℝ e (u x))
      (fun x => inner ℝ e (g x)))
    (hhw : ∀ e : E, HasWeakPartialDerivOn Set.univ i (fun x => inner ℝ e (u x))
      (fun x => inner ℝ e (h x))) : g =ᵐ[volume] h := by
  let b := stdOrthonormalBasis ℝ E
  have hp : ∀ a, (fun x => inner ℝ (b a) (g x)) =ᵐ[volume]
      (fun x => inner ℝ (b a) (h x)) := by
    intro a
    have hg' : MemLp (fun x => inner ℝ (b a) (g x)) 2 volume :=
      (InnerProductSpace.toDual ℝ E (b a)).comp_memLp' hg
    have hh' : Continuous (fun x => inner ℝ (b a) (h x)) :=
      continuous_const.inner hh
    simpa only [Measure.restrict_univ] using HasWeakPartialDerivOn.ae_eq isOpen_univ
      (locallyIntegrableOn_univ.mpr (hg'.locallyIntegrable (by norm_num)))
      (locallyIntegrableOn_univ.mpr hh'.locallyIntegrable) (hgw (b a)) (hhw (b a))
  have hpall : ∀ᵐ x ∂volume, ∀ a, inner ℝ (b a) (g x) = inner ℝ (b a) (h x) :=
    ae_all_iff.mpr hp
  filter_upwards [hpall] with x hx
  apply b.repr.injective
  ext a
  simpa only [b.repr_apply_apply] using hx a
end

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Polynomial weight transfer uses a pointwise weight comparison and exact spatial measure transport. -/

variable {E : Type*} [NormedAddCommGroup E]

theorem weighted_pullback_nonnegative_integral_le (X : Vec 2 ≃ₜ Vec 2)
    (hX : MeasurePreserving X volume volume) (W W' f : Vec 2 → ℝ)
    (hf : ∀ z, 0 ≤ f z) (C : ℝ) (hC : 0 ≤ C)
    (hW : ∀ z, W' z ≤ C * W (X z)) :
    (∫⁻ z, ENNReal.ofReal (W' z * f (X z))) ≤
      ENNReal.ofReal C * ∫⁻ z, ENNReal.ofReal (W z * f z) := by
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal (C * (W (X z) * f (X z))) := by
      apply lintegral_mono
      intro z
      apply ENNReal.ofReal_le_ofReal
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hW z) (hf (X z))
    _ = ENNReal.ofReal C * ∫⁻ z, ENNReal.ofReal (W (X z) * f (X z)) := by
      simp_rw [ENNReal.ofReal_mul hC]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
      congr 1
      exact hX.lintegral_comp_emb X.measurableEmbedding
        (fun z => ENNReal.ofReal (W z * f z))

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory TopologicalSpace
namespace AVRegularity.CycleWords

/-! Measurability of native L2 slices over general measures. -/

variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem bochnerL2Slice_dist (ν : Measure Y) (f : Y → E) (hf : MemLp f 2 ν)
    (g : Lp E 2 ν) :
    dist (hf.toLp f) g = Real.sqrt (∫ y, ‖f y - g y‖ ^ 2 ∂ν) := by
  have hn : ‖hf.toLp f - g‖ ^ 2 = ∫ y, ‖f y - g y‖ ^ 2 ∂ν := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (hf.toLp f) g, hf.coeFn_toLp] with y hy hf'
    rw [hy]
    change inner ℝ ((hf.toLp f) y - g y) ((hf.toLp f) y - g y) = _
    rw [hf', real_inner_self_eq_norm_sq]
  rw [dist_eq_norm, ← hn, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem bochnerL2Slice_stronglyMeasurable (ν : Measure Y) [SFinite ν]
    [SecondCountableTopology (Lp E 2 ν)] (f : X → Y → E)
    (hf : StronglyMeasurable (Function.uncurry f)) (hmem : ∀ x, MemLp (f x) 2 ν) :
    StronglyMeasurable (fun x => (hmem x).toLp (f x)) := by
  let : MeasurableSpace (Lp E 2 ν) := borel _
  let : BorelSpace (Lp E 2 ν) := ⟨rfl⟩
  apply Measurable.stronglyMeasurable
  apply AVRegularity.CoupledEnergyPlane.measurable_of_all_dist
  intro g
  have hd : StronglyMeasurable (fun p : X × Y => f p.1 p.2 - g p.2) :=
    hf.sub ((Lp.stronglyMeasurable g).comp_measurable measurable_snd)
  have hi : StronglyMeasurable (fun x => ∫ y, ‖f x y - g y‖ ^ 2 ∂ν) :=
    (hd.norm.pow 2).integral_prod_right
  have he : (fun x => dist ((hmem x).toLp (f x)) g) =
      (fun x => Real.sqrt (∫ y, ‖f x y - g y‖ ^ 2 ∂ν)) :=
    funext (fun x => bochnerL2Slice_dist ν (f x) (hmem x) g)
  rw [he]
  exact hi.measurable.sqrt

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleWords

/-! Uniform cell ellipticity on arbitrary finite Hilbert fibers. -/

/-- Expand a Hilbert fiber in an orthonormal basis to use the actual cell ellipticity. -/
theorem cellMetric_hilbert_quadratic_lower {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric G)
    (t : ℝ) (z : Vec 2) (u : Fin 2 → E) :
    (1 / 2 : ℝ) * (∑ k : Fin 2, ‖u k‖ ^ 2) ≤
      ∑ k : Fin 2, ∑ j : Fin 2, G t z k j * inner ℝ (u k) (u j) := by
  let b := stdOrthonormalBasis ℝ E
  have he (k : Fin 2) : ‖u k‖ ^ 2 =
      ∑ a : Fin (Module.finrank ℝ E), inner ℝ (b a) (u k) ^ 2 :=
    (b.sum_sq_inner_right (u k)).symm
  have hp (k j : Fin 2) : inner ℝ (u k) (u j) =
      ∑ a : Fin (Module.finrank ℝ E), inner ℝ (b a) (u k) * inner ℝ (b a) (u j) := by
    rw [← b.sum_inner_mul_inner]
    simp only [real_inner_comm (u k)]
  have hE : (1 / 2 : ℝ) * (∑ k : Fin 2, ‖u k‖ ^ 2) =
      ∑ a : Fin (Module.finrank ℝ E), (1 / 2 : ℝ) *
        (∑ k : Fin 2, inner ℝ (b a) (u k) ^ 2) := by
    simp_rw [he, Finset.mul_sum]
    exact Finset.sum_comm
  have hQ : (∑ k : Fin 2, ∑ j : Fin 2, G t z k j * inner ℝ (u k) (u j)) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ k : Fin 2, ∑ j : Fin 2,
        G t z k j * (inner ℝ (b a) (u k) * inner ℝ (b a) (u j)) := by
    simp_rw [hp, Finset.mul_sum]
    calc
      (∑ k : Fin 2, ∑ j : Fin 2, ∑ a : Fin (Module.finrank ℝ E),
          G t z k j * (inner ℝ (b a) (u k) * inner ℝ (b a) (u j))) =
          ∑ k : Fin 2, ∑ a : Fin (Module.finrank ℝ E), ∑ j : Fin 2,
            G t z k j * (inner ℝ (b a) (u k) * inner ℝ (b a) (u j)) := by
              apply Finset.sum_congr rfl
              intro k _
              exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hE, hQ]
  apply Finset.sum_le_sum
  intro a _
  have h := (hG.2.2.2 t z (fun k => inner ℝ (b a) (u k))).1
  convert h using 1
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open scoped BigOperators
namespace AVRegularity.CycleWords

/-! A constant positive complex frequency controls every frequency in its Pi norm ball. -/

theorem fibreNorm_le_constant_of_norm_le (ξ : Fin 2 → ℂ) {R : ℝ}
    (hR : 0 ≤ R) (hξ : ‖ξ‖ ≤ R) :
    fibreNorm ξ ≤ fibreNorm (fun _ : Fin 2 => (R : ℂ)) := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR]
  exact pow_le_pow_left₀ (norm_nonneg _) ((norm_le_pi_norm ξ i).trans hξ) 2

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleWords

/-! A positive row and column budget controls the full inverse-mass quadratic flux norm. -/

variable {ι : Type*} [Fintype ι]

theorem finite_mass_schur_square_le (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (b : ι → ι → ℝ) (hb : ∀ v u, 0 ≤ b v u) (θ : ℝ) (hθ : 0 ≤ θ)
    (hrow : ∀ v, ∑ u, Real.sqrt (π u / π v) * b v u ≤ θ)
    (hcol : ∀ u, ∑ v, Real.sqrt (π u / π v) * b v u ≤ θ)
    (x f : ι → ℝ) (hf : ∀ v, 0 ≤ f v)
    (hbound : ∀ v, f v ≤ ∑ u, b v u * x u) :
    (∑ v, (π v)⁻¹ * f v ^ 2) ≤ θ ^ 2 * ∑ u, (π u)⁻¹ * x u ^ 2 := by
  classical
  let S := ∑ v, (π v)⁻¹ * f v ^ 2
  let G := ∑ u, (π u)⁻¹ * x u ^ 2
  change S ≤ θ ^ 2 * G
  have hS : 0 ≤ S := Finset.sum_nonneg (fun v _ => mul_nonneg (inv_pos.mpr (hπ v)).le (sq_nonneg _))
  have hG : 0 ≤ G := Finset.sum_nonneg (fun u _ => mul_nonneg (inv_pos.mpr (hπ u)).le (sq_nonneg _))
  have hi : S ≤ ∑ v, ∑ u, (π v)⁻¹ * b v u * f v * x u := by
    dsimp only [S]
    apply Finset.sum_le_sum
    intro v _
    have hh := mul_le_mul_of_nonneg_left (hbound v)
      (mul_nonneg (inv_pos.mpr (hπ v)).le (hf v))
    have he : (π v)⁻¹ * f v * (∑ u, b v u * x u) =
        ∑ u, (π v)⁻¹ * b v u * f v * x u := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    simpa only [pow_two, mul_assoc, he] using hh
  have hs := Analysis.Schur.massSchurBilinear Finset.univ π b f x θ
    (fun i _ => hπ i) (fun v _ u _ => hb v u) hθ
    (fun v _ => hrow v) (fun u _ => hcol u)
  have hsg : S ≤ θ * Real.sqrt S * Real.sqrt G := hi.trans hs
  by_cases hz : Real.sqrt S = 0
  · have hsz : S = 0 := (Real.sqrt_eq_zero hS).mp hz
    rw [hsz]
    exact mul_nonneg (sq_nonneg θ) hG
  · have hp : 0 < Real.sqrt S := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
    have hc : Real.sqrt S * Real.sqrt S ≤ Real.sqrt S * (θ * Real.sqrt G) := by
      rw [Real.mul_self_sqrt hS]
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hsg
    have hr := le_of_mul_le_mul_left hc hp
    have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) hr 2
    simpa only [Real.sq_sqrt hS, mul_pow, Real.sq_sqrt hG, S, G] using hh

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set AVRegularity.CycleEvolution AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! Finite ODE observables have genuine scalar energy derivatives. -/

theorem strongTime_scalar_norm_energy {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {a b : ℝ} {u du : ℝ → H}
    (h : StrongTimeRegularity a b u du) :
    StrongTimeRegularity a b (fun t => ‖u t‖ ^ 2)
      (fun t => 2 * inner ℝ (du t) (u t)) := by
  refine ⟨h.norm_sq_ac, ?_⟩
  filter_upwards [h.derivative] with t ht
  simpa only [real_inner_comm] using ht.norm_sq_inner

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleWords

/-! True positivity and resolvent bound of the future integral. -/

theorem futureMemory_nonneg (μ : ℝ) (p : ℝ → ℝ) (hp : ∀ s, 0 ≤ p s) (t : ℝ) :
    0 ≤ futureMemory μ p t := by
  unfold futureMemory
  exact mul_nonneg (Real.exp_pos _).le (integral_nonneg (fun s =>
    mul_nonneg (hp s) (Real.exp_pos _).le))

theorem futureMemory_le_inv {μ : ℝ} (hμ : 0 < μ) (p : ℝ → ℝ)
    (hp : Continuous p) (hc : HasCompactSupport p) (hb : ∀ s, p s ≤ 1) (t : ℝ) :
    futureMemory μ p t ≤ μ⁻¹ := by
  have hg : IntegrableOn (fun s => p s * Real.exp (-μ * s)) (Set.Ici t) :=
    (hp.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right |>.integrableOn
  have he : IntegrableOn (fun s => Real.exp (-μ * s)) (Set.Ici t) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_exp_mul_Ioi (by linarith) t
  have hm : (∫ s in Set.Ici t, p s * Real.exp (-μ * s)) ≤
      ∫ s in Set.Ici t, Real.exp (-μ * s) := integral_mono hg he (fun s => by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hb s) (Real.exp_pos _).le)
  have hi : (∫ s in Set.Ici t, Real.exp (-μ * s)) = Real.exp (-μ * t) / μ := by
    rw [integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi (by linarith : -μ < 0) t]
    ring
  unfold futureMemory
  calc
    _ ≤ Real.exp (μ * t) * (Real.exp (-μ * t) / μ) :=
      mul_le_mul_of_nonneg_left (hm.trans_eq hi) (Real.exp_pos _).le
    _ = μ⁻¹ := by
      rw [div_eq_mul_inv, ← mul_assoc, ← Real.exp_add,
        show μ * t + -μ * t = 0 by ring, Real.exp_zero, one_mul]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open scoped ContDiff
namespace AVRegularity.CycleWords

/-! Smooth pulse data give smooth adjoint memories by the proved scalar ODE. -/

theorem futureMemory_contDiff_nat (μ : ℝ) (p : ℝ → ℝ)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hc : HasCompactSupport p) (n : ℕ) :
    ContDiff ℝ n (futureMemory μ p) := by
  have hd (t : ℝ) := futureMemory_hasDerivAt μ p hp.continuous hc t
  have hdiff : Differentiable ℝ (futureMemory μ p) := fun t => (hd t).differentiableAt
  have he : deriv (futureMemory μ p) = fun t => μ * futureMemory μ p t - p t :=
    funext (fun t => (hd t).deriv)
  induction n with
  | zero => exact contDiff_zero.mpr hdiff.continuous
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp, contDiff_succ_iff_deriv]
    refine ⟨hdiff, ?_, ?_⟩
    · intro hn
      simp at hn
    · rw [he]
      exact (contDiff_const.mul ih).sub (hp.of_le (by simp))

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory AVRegularity.CoupledEnergyPlane.Fourier
open scoped FourierTransform SchwartzMap RealInnerProductSpace
namespace AVRegularity.CycleWords

/-! Exact Fourier frequency translation by multiplication with a real Hilbert character. -/

local instance hilbertCharacterRealComplexSpace : NormedSpace ℝ ℂ :=
  NormedSpace.complexToReal

def hilbertModulationCharacter (v x : HilbertTwo) : ℂ := 𝐞 (inner ℝ x v)

theorem hilbertModulationCharacter_temperate (v : HilbertTwo) :
    (hilbertModulationCharacter v).HasTemperateGrowth := by
  let L : HilbertTwo →L[ℝ] ℝ := (2 * Real.pi) • (innerSL ℝ).flip v
  have h := Complex.hasTemperateGrowth_exp_mul_I.comp L.hasTemperateGrowth
  have he : hilbertModulationCharacter v =
      (fun t : ℝ => Complex.exp (t * Complex.I)) ∘ L := by
    funext x
    simp only [hilbertModulationCharacter, Real.fourierChar_apply, Function.comp_apply,
      L, smul_apply, ContinuousLinearMap.flip_apply, innerSL_apply_apply, smul_eq_mul]
  rw [he]
  exact h

def hilbertSchwartzModulation (v : HilbertTwo) : 𝓢(HilbertTwo, ℂ) →L[ℂ] 𝓢(HilbertTwo, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (hilbertModulationCharacter v)

theorem hilbertSchwartzModulation_apply (v x : HilbertTwo) (f : 𝓢(HilbertTwo, ℂ)) :
    hilbertSchwartzModulation v f x = hilbertModulationCharacter v x * f x := by
  exact SchwartzMap.smulLeftCLM_apply_apply (hilbertModulationCharacter_temperate v) f x

theorem hilbertModulation_fourier (v : HilbertTwo) (f : HilbertTwo → ℂ) (ξ : HilbertTwo) :
    𝓕 (fun x => hilbertModulationCharacter v x * f x) ξ = 𝓕 f (ξ - v) := by
  simp only [Real.fourier_eq, Circle.smul_def, hilbertModulationCharacter, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← mul_assoc, ← Circle.coe_mul, ← Real.fourierChar.map_add_eq_mul]
  congr 2
  rw [inner_sub_right]
  congr 1
  ring

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace AVRegularity.CycleWords

/-! Finite coordinate remainders vanish in the actual L2 seminorm. -/

section
variable {X I E : Type*} [MeasurableSpace X] [Countable I] [DecidableEq I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X}

def lpCoordinateProjection (s : Finset I) :
    lp (fun _ : I => E) 2 →L[ℝ] lp (fun _ : I => E) 2 :=
  ∑ i ∈ s, (lp.singleContinuousLinearMap ℝ (fun _ : I => E) 2 i).comp
    (lp.evalCLM ℝ (fun _ : I => E) 2 i)

omit [Countable I] in
theorem lpCoordinateProjection_apply (s : Finset I) (f : lp (fun _ : I => E) 2) :
    lpCoordinateProjection s f = ∑ i ∈ s, lp.single 2 i (f i) := by
  simp [lpCoordinateProjection, sum_apply, ContinuousLinearMap.comp_apply, lp.evalCLM,
    lp.evalₗ]
  rfl

omit [Countable I] in
theorem lp_coordinate_remainder_memLp (f : X → lp (fun _ : I => E) 2)
    (hf : MemLp f 2 μ) (s : Finset I) :
    MemLp (fun x => f x - ∑ i ∈ s, lp.single 2 i (f x i)) 2 μ := by
  have hh := (ContinuousLinearMap.id ℝ (lp (fun _ : I => E) 2) -
    lpCoordinateProjection s).comp_memLp' hf
  simpa only [Function.comp_def, sub_apply, ContinuousLinearMap.id_apply,
    lpCoordinateProjection_apply] using hh

theorem tendsto_lpNorm_coordinate_remainder (f : X → lp (fun _ : I => E) 2)
    (hf : MemLp f 2 μ) :
    Tendsto (fun s : Finset I => lpNorm
      (fun x => f x - ∑ i ∈ s, lp.single 2 i (f x i)) 2 μ) atTop (𝓝 0) := by
  apply tendsto_lpNorm_two_of_dominated _ f (lp_coordinate_remainder_memLp f hf) hf
  · intro s
    exact Eventually.of_forall (fun x => lp_coordinate_remainder_norm_le (f x) s)
  · exact Eventually.of_forall fun x => by
      have hc : Tendsto (fun _ : Finset I => f x) atTop (𝓝 (f x)) := tendsto_const_nhds
      have hh := hc.sub (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (f x))
      simpa only [sub_self] using hh
end

/-! Remove a vanishing measurable cutoff budget beside an arbitrary literal forcing. -/

theorem lower_integral_cutoff_removal {μ : Measure ℝ}
    (force mass : ℝ → ℝ) (hf : ∀ t, 0 ≤ force t) (hm : ∀ t, 0 ≤ mass t)
    (hmi : Integrable mass μ)
    (c E D I : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    {e d i A : ℝ}
    (hclim : Tendsto c atTop (𝓝 0))
    (hE : Tendsto E atTop (𝓝 e)) (hD : Tendsto D atTop (𝓝 d))
    (hI : Tendsto I atTop (𝓝 i))
    (hbound : ∀ n, ENNReal.ofReal (E n + D n) ≤
      (ENNReal.ofReal (I n) + ∫⁻ s, ENNReal.ofReal (force s + c n * mass s) ∂μ) *
        ENNReal.ofReal A) :
    ENNReal.ofReal (e + d) ≤
      (ENNReal.ofReal i + ∫⁻ s, ENNReal.ofReal (force s) ∂μ) * ENNReal.ofReal A := by
  have hmfin : (∫⁻ s, ENNReal.ofReal (mass s) ∂μ) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hmi (Filter.Eventually.of_forall hm)]
    exact ENNReal.ofReal_ne_top
  have hcn := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hclim) (Or.inr hmfin)
  have hl := ENNReal.tendsto_ofReal (hE.add hD)
  have hr := ENNReal.Tendsto.mul_const (b := ENNReal.ofReal A)
    ((ENNReal.tendsto_ofReal hI).add
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ∫⁻ s, ENNReal.ofReal (force s) ∂μ)
        atTop (𝓝 (∫⁻ s, ENNReal.ofReal (force s) ∂μ))).add hcn))
    (Or.inr ENNReal.ofReal_ne_top)
  apply le_of_tendsto_of_tendsto hl (by
    simpa only [ENNReal.ofReal_zero, zero_mul, add_zero] using hr)
  exact Eventually.of_forall (fun n => by
    have hh := hbound n
    have heq := lintegral_ofReal_sum_with_measurable_right μ force mass hf hm
      hmi.aestronglyMeasurable.aemeasurable 1 (c n) (by norm_num) (hc n)
    simp only [one_mul, ENNReal.ofReal_one] at heq
    rw [heq] at hh
    simpa only [one_mul] using hh)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! A finite literal forcing integral gives an ordinary real energy budget. -/

theorem lower_integral_real_energy_budget {μ : Measure ℝ}
    (f d : ℝ → ℝ) (hf : ∀ t, 0 ≤ f t) (hd : ∀ t, 0 ≤ d t)
    (hdi : Integrable d μ) (hfin : (∫⁻ t, ENNReal.ofReal (f t) ∂μ) < ⊤)
    (a c I A E : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hI : 0 ≤ I) (hA : 0 ≤ A)
    (h : ENNReal.ofReal E ≤ (ENNReal.ofReal I +
      ∫⁻ t, ENNReal.ofReal (a * f t + c * d t) ∂μ) * ENNReal.ofReal A) :
    E ≤ (I + a * (∫⁻ t, ENNReal.ofReal (f t) ∂μ).toReal + c * (∫ t, d t ∂μ)) * A := by
  have hs := lintegral_ofReal_sum_with_measurable_right μ f d hf hd
    hdi.aestronglyMeasurable.aemeasurable a c ha hc
  rw [hs, ← ofReal_integral_eq_lintegral_ofReal hdi (Filter.Eventually.of_forall hd)] at h
  have hfn : (∫⁻ t, ENNReal.ofReal (f t) ∂μ) ≠ ⊤ := ne_of_lt hfin
  have hfreal := ENNReal.ofReal_toReal hfn
  have hdn : 0 ≤ ∫ t, d t ∂μ := integral_nonneg hd
  have hsum : 0 ≤ a * (∫⁻ t, ENNReal.ofReal (f t) ∂μ).toReal + c * (∫ t, d t ∂μ) :=
    add_nonneg (mul_nonneg ha ENNReal.toReal_nonneg) (mul_nonneg hc hdn)
  have htotal := add_nonneg hI hsum
  rw [← hfreal, ← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hc,
    ← ENNReal.ofReal_add (mul_nonneg ha ENNReal.toReal_nonneg) (mul_nonneg hc hdn),
    ← ENNReal.ofReal_add hI hsum, ← ENNReal.ofReal_mul htotal] at h
  have hh := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg htotal hA)).mp h
  simpa only [add_assoc] using hh

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleWords

/-! Fixed output maps preserve actual mixed operator jet bounds. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem mixedJet_postcomposition_norm_le {p q : ℕ} (f : Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth p q f) (L : E →L[ℝ] F) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (fun y => L (f Y y)) z) X‖ ≤
      ‖L‖ * ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (f Y) z) X‖ := by
  let A := ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin q => Vec 2) E F L
  have he : (fun Y => iteratedFDeriv ℝ q (fun y => L (f Y y)) z) =
      A ∘ (fun Y => iteratedFDeriv ℝ q (f Y) z) := by
    funext Y
    exact L.iteratedFDeriv_comp_left (hf.1 Y).contDiffAt le_rfl
  rw [he]
  have hA : ‖A‖ ≤ ‖L‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
    intro g
    exact L.norm_compContinuousMultilinearMap_le g
  exact (A.norm_iteratedFDeriv_comp_left (hf.2.1 q le_rfl z).contDiffAt le_rfl).trans
    (mul_le_mul_of_nonneg_right hA (norm_nonneg _))

theorem mixedJet_coordinate_norm_le {p q : ℕ} (f : Vec 2 → Vec 2 → Vec 2)
    (hf : IsBoxSmooth p q f) (k : Fin 2) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (fun y => f Y y k) z) X‖ ≤
      ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (f Y) z) X‖ := by
  have hh := mixedJet_postcomposition_norm_le f hf (ContinuousLinearMap.proj k) X z
  have hp : ‖(ContinuousLinearMap.proj k : Vec 2 →L[ℝ] ℝ)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [ContinuousLinearMap.proj_apply, one_mul] using norm_le_pi_norm x k
  exact hh.trans (mul_le_of_le_one_left (norm_nonneg _) hp)

theorem mixedJet_fast_shift_coordinate_norm_le {p q : ℕ} (f : Vec 2 → Vec 2 → Vec 2)
    (hf : IsBoxSmooth p q f) (φ : Vec 2) (k : Fin 2) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => f Y (y + φ) k) z) X‖ ≤
      ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (f Y) (z + φ)) X‖ := by
  have he : (fun Y => iteratedFDeriv ℝ q (fun y => f Y (y + φ) k) z) =
      (fun Y => iteratedFDeriv ℝ q (fun y => f Y y k) (z + φ)) := by
    funext Y
    exact iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := fun y => f Y y k) q φ z
  rw [he]
  exact mixedJet_coordinate_norm_le f hf k X (z + φ)

theorem iteratedJet_coordinate_norm_le {N j : ℕ} (f : Vec 2 → Vec 2)
    (hf : ContDiff ℝ (N : ℕ) f) (hj : j ≤ N) (k : Fin 2) (z : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun y => f y k) z‖ ≤ ‖iteratedFDeriv ℝ j f z‖ := by
  let L : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj k
  have hp : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [L, ContinuousLinearMap.proj_apply, one_mul] using norm_le_pi_norm x k
  exact (L.norm_iteratedFDeriv_comp_left hf.contDiffAt (by exact_mod_cast hj)).trans
    (mul_le_of_le_one_left (norm_nonneg _) hp)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Classical/native finite jet readout prices are finite real constants. -/

def nativeSobolevWordPrice (J : ℕ) : ℝ :=
  ∑ b ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 b) : ℝ)

theorem nativeSobolevWordPrice_nonneg (J : ℕ) : 0 ≤ nativeSobolevWordPrice J := by
  unfold nativeSobolevWordPrice
  exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

theorem nativeSobolevWordPrice_ofReal (J : ℕ) :
    ENNReal.ofReal (nativeSobolevWordPrice J) =
      ∑ b ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 b) : ℝ≥0∞) := by
  unfold nativeSobolevWordPrice
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => Nat.cast_nonneg _)]
  simp only [ENNReal.ofReal_natCast]

theorem nativeSobolevWordPrice_mul_ofReal (J : ℕ) (C : ℝ) :
    (∑ b ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 b) : ℝ≥0∞)) *
      ENNReal.ofReal C = ENNReal.ofReal (nativeSobolevWordPrice J * C) := by
  rw [← nativeSobolevWordPrice_ofReal,
    ENNReal.ofReal_mul (nativeSobolevWordPrice_nonneg J)]

theorem nativeSobolevReadoutPrice_ofReal (J : ℕ) (C : ℝ) :
    (∑ b ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 b) : ℝ≥0∞)) *
      ENNReal.ofReal C * (Fintype.card (JetIndex2 J) : ℝ≥0∞) =
      ENNReal.ofReal (nativeSobolevWordPrice J * C * (Fintype.card (JetIndex2 J) : ℝ)) := by
  rw [nativeSobolevWordPrice_mul_ofReal, ← ENNReal.ofReal_natCast,
    ENNReal.ofReal_mul' (Nat.cast_nonneg _)]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Filter
namespace AVRegularity.CycleWords

/-! Almost-everywhere lattice-cell facts determine whole-plane facts. -/

theorem planeFrequency_ae_of_cell_shifts (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (p : Vec 2 → Prop)
    (hp : ∀ᵐ θ ∂volume.restrict (planeFrequencyCell a P),
      ∀ n : Fin 2 → ℤ, p (planeLatticeEmbedding P n + θ)) :
    ∀ᵐ x ∂(volume : Measure (Vec 2)), p x := by
  have hc := (ae_restrict_iff' (planeFrequencyCell_measurable a P)).mp hp
  have hn (n : Fin 2 → ℤ) : ∀ᵐ x ∂(volume : Measure (Vec 2)),
      x - planeLatticeEmbedding P n ∈ planeFrequencyCell a P → p x := by
    have ht := (measurePreserving_add_right volume (-planeLatticeEmbedding P n)).quasiMeasurePreserving.ae hc
    filter_upwards [ht] with x hx
    intro hmem
    have hh := hx (by simpa only [sub_eq_add_neg] using hmem) n
    have he : planeLatticeEmbedding P n + (x + -planeLatticeEmbedding P n) = x := by abel
    rwa [he] at hh
  filter_upwards [ae_all_iff.mpr hn] with x hx
  obtain ⟨n, hn, _⟩ := planeFrequencyCell_unique_shift a x P hP
  apply hx (-n)
  have he : x - planeLatticeEmbedding P (-n) = planeLatticeEmbedding P n + x := by
    rw [map_neg]
    abel
  rwa [he]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleWords

/-! A single lattice coordinate realized by a function supported on one cell. -/

variable {E : Type*} [NormedAddCommGroup E]

theorem planeFrequencyCell_shift_iff (a θ : Vec 2) (P : ℝ) (hP : 0 < P)
    (hθ : θ ∈ planeFrequencyCell a P) (n : Fin 2 → ℤ) :
    planeLatticeEmbedding P n + θ ∈ planeFrequencyCell a P ↔ n = 0 := by
  obtain ⟨m, hm, hu⟩ := planeFrequencyCell_unique_shift a θ P hP
  have hz : planeLatticeEmbedding P 0 + θ ∈ planeFrequencyCell a P := by
    simpa using hθ
  constructor
  · intro hn
    exact (hu n hn).trans (hu 0 hz).symm
  · rintro rfl
    exact hz

theorem planeFrequencyCell_indicator_coeff (a θ : Vec 2) (P : ℝ) (hP : 0 < P)
    (hθ : θ ∈ planeFrequencyCell a P) (g : Vec 2 → E) (n : Fin 2 → ℤ) :
    (planeFrequencyCell a P).indicator g (planeLatticeEmbedding P n + θ) =
      (Pi.single 0 (g θ) : (Fin 2 → ℤ) → E) n := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [hθ]
  · rw [Set.indicator_of_notMem]
    · simp [hn]
    · exact fun h => hn ((planeFrequencyCell_shift_iff a θ P hP hθ n).mp h)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Function
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The plane frequency integral is exactly the sum over translated half-open cells. -/

def planeLatticeEquiv (P : ℝ) (hP : 0 < P) :
    (Fin 2 → ℤ) ≃ (planeLatticeEmbedding P).range :=
  Equiv.ofInjective (planeLatticeEmbedding P) (planeLatticeEmbedding_injective P hP)

theorem planeFrequencyCell_fundamental (a : Vec 2) (P : ℝ) (hP : 0 < P) :
    IsAddFundamentalDomain (planeLatticeEmbedding P).range (planeFrequencyCell a P) volume := by
  apply IsAddFundamentalDomain.mk' (planeFrequencyCell_measurable a P).nullMeasurableSet
  intro x
  obtain ⟨n, hn, hu⟩ := planeFrequencyCell_unique_shift a x P hP
  let e := planeLatticeEquiv P hP
  refine ⟨e n, hn, ?_⟩
  intro g hg
  have hg' : planeLatticeEmbedding P (e.symm g) + x ∈ planeFrequencyCell a P := by
    change (e (e.symm g) : Vec 2) + x ∈ planeFrequencyCell a P
    rw [e.apply_symm_apply]
    exact hg
  have he : e.symm g = n := hu _ hg'
  exact (e.apply_symm_apply g).symm.trans (congrArg e he)

theorem planeFrequency_lintegral_tiling (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (f : Vec 2 → ℝ≥0∞) :
    (∫⁻ x, f x) = ∑' g : (planeLatticeEmbedding P).range,
      ∫⁻ θ in planeFrequencyCell a P, f ((g : Vec 2) + θ) := by
  let e := planeLatticeEquiv P hP
  have : Countable (planeLatticeEmbedding P).range := e.symm.injective.countable
  exact (planeFrequencyCell_fundamental a P hP).lintegral_eq_tsum'' f

end AVRegularity.CycleWords
end
end

section
@[expose] public section
open scoped Classical
namespace AVRegularity.CycleWords

/-! Summing the preceding response levels leaves precisely the terminal
response as the unmatched metric insertion. -/

variable {E : Type*} [AddCommGroup E]

theorem responsePreviousLevel_sum_telescope (J : ℕ) (f : Fin (J + 1) → E) :
    (∑ j : Fin (J + 1), ∑ j' : Fin (J + 1), if j.val = j'.val + 1 then f j' else 0) =
      (∑ j : Fin (J + 1), f j) - f (Fin.last J) := by
  rw [Fin.sum_univ_succ]
  rw [responsePreviousLevel_sum_zero 0 rfl, zero_add]
  have he (j : Fin J) :
      (∑ j' : Fin (J + 1), if j.succ.val = j'.val + 1 then f j' else 0) = f j.castSucc := by
    rw [responsePreviousLevel_sum_eq j.succ (by simp only [Fin.val_succ]; omega)]
    congr 1
  simp_rw [he]
  rw [Fin.sum_univ_castSucc f]
  abel

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleWords

/-! The full Taylor polynomial is the constant term plus its positive-degree
part, with no smoothness premise needed for this exact algebraic identity. -/

theorem taylorSlow_zero_eq_constant_add_positive (K : ℕ) (f : Vec 2 → ℝ)
    (X Δ : Vec 2) : taylorSlow 0 K f X Δ = f X + taylorSlow 1 K f X Δ := by
  classical
  have he : Finset.Icc 0 K = insert 0 (Finset.Icc 1 K) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hn : 0 ∉ Finset.Icc 1 K := by simp only [Finset.mem_Icc]; omega
  unfold taylorSlow
  rw [he, Finset.sum_insert hn]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, iteratedFDeriv_zero_apply]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Filter TopologicalSpace
namespace AVRegularity.CycleWords

/-! Measurable total L2 slice classes, with zero on exceptional nonintegrable slices. -/

variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
def bochnerL2TotalSlice (ν : Measure Y) (f : X → Y → E) (x : X) : Lp E 2 ν := by
  classical
  exact if h : MemLp (f x) 2 ν then h.toLp (f x) else 0

omit [InnerProductSpace ℝ E] [MeasurableSpace X] in
theorem bochnerL2TotalSlice_ae (ν : Measure Y) (f : X → Y → E) (x : X)
    (hx : MemLp (f x) 2 ν) : bochnerL2TotalSlice ν f x =ᵐ[ν] f x := by
  classical
  simp only [bochnerL2TotalSlice, dite_eq_left hx]
  exact hx.coeFn_toLp

theorem bochnerL2TotalSlice_stronglyMeasurable (ν : Measure Y) [SFinite ν]
    [SecondCountableTopology (Lp E 2 ν)] (f : X → Y → E)
    (hf : StronglyMeasurable (Function.uncurry f)) :
    StronglyMeasurable (bochnerL2TotalSlice ν f) := by
  classical
  let s : Set X := {x | MemLp (f x) 2 ν}
  have hs : MeasurableSet s := by
    have hp : StronglyMeasurable (Function.uncurry (fun x y => ‖f x y‖ ^ 2)) :=
      hf.norm.pow 2
    have hi := measurableSet_integrable (μ := ν) hp
    convert hi using 1
    ext x
    exact memLp_two_iff_integrable_sq_norm (hf.of_uncurry_left.aestronglyMeasurable)
  let g : X → Y → E := fun x y => if x ∈ s then f x y else 0
  have hg : StronglyMeasurable (Function.uncurry g) := by
    have hm : StronglyMeasurable ((Prod.fst ⁻¹' s).piecewise
        (Function.uncurry f) (fun _ : X × Y => (0 : E))) :=
      hf.piecewise (hs.preimage measurable_fst) stronglyMeasurable_const
    exact hm
  have hgm (x : X) : MemLp (g x) 2 ν := by
    by_cases hx : x ∈ s
    · have hx' : MemLp (f x) 2 ν := hx
      simpa only [g, ite_eq_left hx] using hx'
    · change MemLp (fun y => if x ∈ s then f x y else 0) 2 ν
      simp only [ite_eq_right hx]
      exact MemLp.zero
  have hm := bochnerL2Slice_stronglyMeasurable ν g hg hgm
  convert hm using 1
  funext x
  by_cases hx : MemLp (f x) 2 ν
  · simp only [bochnerL2TotalSlice, dite_eq_left hx]
    have he : g x = f x := by funext y; simp only [g, s, mem_ofPred_eq, ite_eq_left hx]
    exact hx.toLp_congr (hgm x) (Eventually.of_forall (fun y => (congrFun he y).symm))
  · simp only [bochnerL2TotalSlice, dite_eq_right hx]
    have he : g x = 0 := by funext y; simp only [g, s, mem_ofPred_eq, ite_eq_right hx, Pi.zero_apply]
    apply Lp.ext
    filter_upwards [(hgm x).coeFn_toLp, Lp.coeFn_zero E 2 ν] with y hy hz
    rw [hy, he, Pi.zero_apply, hz]
    rfl

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization Filter AVRegularity.Sobolev
open scoped Topology
namespace AVRegularity.CycleWords

/-! Local agreement of coefficients propagates through the literal ordered jets. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem orderedCoefficientDerivative_eventuallyEq
    {C D : Vec 2 → E →L[ℝ] F} {x : Vec 2} (h : C =ᶠ[𝓝 x] D)
    (j : ℕ) (w : DerivativeWord2 j) :
    orderedCoefficientDerivative C j w =ᶠ[𝓝 x] orderedCoefficientDerivative D j w := by
  induction j with
  | zero => exact h
  | succ j ih =>
    have hd := (ih (Fin.init w)).fderiv (𝕜 := ℝ)
    filter_upwards [hd] with y hy
    change fderiv ℝ (orderedCoefficientDerivative C j (Fin.init w)) y _ =
      fderiv ℝ (orderedCoefficientDerivative D j (Fin.init w)) y _
    rw [hy]

theorem orderedCoefficientDerivative_eq_of_eventuallyEq
    {C D : Vec 2 → E →L[ℝ] F} {x : Vec 2} (h : C =ᶠ[𝓝 x] D)
    (j : ℕ) (w : DerivativeWord2 j) :
    orderedCoefficientDerivative C j w x = orderedCoefficientDerivative D j w x :=
  (orderedCoefficientDerivative_eventuallyEq h j w).eq_of_nhds

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Complex Metric Set
open scoped NNReal
namespace AVRegularity.CycleWords

/-! Bounded holomorphic line discs give geometric prices for normalized directional Taylor jets. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem complexDirectionalTaylor_norm_le (f : E → F) (Ω : Set E) (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℂ (⊤ : ℕ∞) f Ω) (h0 : (0 : E) ∈ Ω)
    (ν : E) (R : ℝ≥0) (hR : 0 < R) (M : ℝ)
    (hline : ∀ z ∈ closedBall (0 : ℂ) (R : ℝ), z • ν ∈ Ω)
    (hb : ∀ x ∈ Ω, ‖f x‖ ≤ M) (n : ℕ) :
    ‖((n.factorial : ℂ)⁻¹) • iteratedFDeriv ℂ n f 0 (fun _ => ν)‖ ≤ M * (R : ℝ)⁻¹ ^ n := by
  let g := fun z : ℂ => f (z • ν)
  have hd : DifferentiableOn ℂ g (closedBall (0 : ℂ) (R : ℝ)) := by
    intro z hz
    have hc := (hf _ (hline z hz)).contDiffAt (hΩ.mem_nhds (hline z hz))
    exact ((hc.comp z (contDiffAt_id.smul contDiffAt_const)).differentiableAt (by simp)).differentiableWithinAt
  have hp := hd.hasFPowerSeriesOnBall hR
  have hjet := hp.factorial_smul (1 : ℂ) n
  rw [complexLinearLine_iteratedFDeriv f Ω hΩ hf h0 ν n] at hjet
  have he : ((n.factorial : ℂ)⁻¹) • iteratedFDeriv ℂ n f 0 (fun _ => ν) =
      cauchyPowerSeries g 0 R n (fun _ => 1) := by
    rw [← hjet, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), one_smul]
  rw [he]
  exact complexCauchy_coefficient_norm_le g R M hR
    (fun z hz => hb _ (hline z (sphere_subset_closedBall hz))) n

end AVRegularity.CycleWords
end
end

section
@[expose] public section
open AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! At radius at most one the factorial coefficients decrease with derivative order. -/

theorem factorialWeight_order_antitone {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    {j k : ℕ} (hjk : j ≤ k) : factorialWeight r k ≤ factorialWeight r j := by
  unfold factorialWeight
  have hp : r ^ (2 * k) ≤ r ^ (2 * j) := by
    have hs : r ^ (2 * (k - j)) ≤ 1 := pow_le_one₀ hr hr1
    calc
      r ^ (2 * k) = r ^ (2 * j) * r ^ (2 * (k - j)) := by
        rw [← pow_add]
        congr 1
        omega
      _ ≤ r ^ (2 * j) * 1 := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := mul_one _
  have hf : (j.factorial : ℝ) ≤ (k.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hjk
  have hfsq : (j.factorial : ℝ) ^ 2 ≤ (k.factorial : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hf 2
  apply div_le_div₀ (by positivity) hp (by positivity) hfsq

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! Literal periodic Taylor families stay periodic and preserve their cell classes term by term. -/

theorem fibreSeriesFun_periodic (a : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (ha : ∀ p t, AVenhance.IsZ2Periodic (a p t)) (ξ : Fin 2 → ℂ) (t : ℝ) :
    AVenhance.IsZ2Periodic (fibreSeriesFun a ξ t) := by
  intro n x
  unfold fibreSeriesFun
  apply tsum_congr
  intro p
  rw [ha p t n x]

theorem fibreSeriesFun_congr_ae (a b : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (ha : ∀ p t, a p t =ᵐ[volume.restrict AVenhance.unitCube] b p t)
    (ξ : Fin 2 → ℂ) (t : ℝ) :
    fibreSeriesFun a ξ t =ᵐ[volume.restrict AVenhance.unitCube] fibreSeriesFun b ξ t := by
  filter_upwards [ae_all_iff.mpr (fun p => ha p t)] with x hx
  unfold fibreSeriesFun
  apply tsum_congr
  intro p
  rw [hx p]

end AVRegularity.CycleWords
end
end
