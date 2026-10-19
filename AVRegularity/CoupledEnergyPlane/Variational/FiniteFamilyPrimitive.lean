-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import Mathlib.Analysis.Calculus.Deriv.Slope
public import Homogenization.Ambient.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

section
@[expose] public section
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! A spectral band source pairing is bounded by the two single-cutoff tails. -/

variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup J] [InnerProductSpace ℝ J]

theorem inner_band_source_of_adjoint (dN dM hN hM c : H) (sN sM g : J)
    (hdN : inner ℝ dN c = -inner ℝ sN g)
    (hdM : inner ℝ dM c = -inner ℝ sM g) :
    inner ℝ ((dN + hN) - (dM + hM)) c =
      inner ℝ (hN - hM) c - inner ℝ (sN - sM) g := by
  rw [inner_sub_left, inner_add_left, inner_add_left, hdN, hdM,
    inner_sub_left, inner_sub_left]
  ring

theorem norm_band_le_tails (P Q : H →L[ℝ] H) (x : H) :
    ‖P x - Q x‖ ≤ ‖P x - x‖ + ‖Q x - x‖ := by
  calc
    ‖P x - Q x‖ = ‖(P x - x) - (Q x - x)‖ := by congr 1; abel
    _ ≤ ‖P x - x‖ + ‖Q x - x‖ := norm_sub_le _ _

theorem norm_band_sq_le_tails (P Q : H →L[ℝ] H) (x : H) :
    ‖P x - Q x‖ ^ 2 ≤ 2 * ‖P x - x‖ ^ 2 + 2 * ‖Q x - x‖ ^ 2 := by
  have hn := norm_band_le_tails P Q x
  nlinarith [norm_nonneg (P x - Q x), norm_nonneg (P x - x), norm_nonneg (Q x - x),
    sq_nonneg (‖P x - x‖ - ‖Q x - x‖)]

theorem bandSourcePairing_abs_le (P Q : H →L[ℝ] H) (S T : J →L[ℝ] J)
    (f u : H) (F w : J) (R : ℝ)
    (hu : ‖u‖ ≤ R) (hP : ‖P u‖ ≤ ‖u‖) (hQ : ‖Q u‖ ≤ ‖u‖)
    (hS : ‖S w‖ ≤ ‖w‖) (hT : ‖T w‖ ≤ ‖w‖) :
    |2 * inner ℝ (P f - Q f) (P u - Q u) -
      2 * inner ℝ (S F - T F) (S w - T w)| ≤
      4 * R * (‖P f - f‖ + ‖Q f - f‖) +
        4 * (‖S F - F‖ + ‖T F - F‖) * ‖w‖ := by
  have hcu : ‖P u - Q u‖ ≤ 2 * R := by
    exact (norm_sub_le _ _).trans (by linarith)
  have hcw : ‖S w - T w‖ ≤ 2 * ‖w‖ := by
    exact (norm_sub_le _ _).trans (by linarith)
  have hf := norm_band_le_tails P Q f
  have hF := norm_band_le_tails S T F
  have hp := abs_real_inner_le_norm (P f - Q f) (P u - Q u)
  have hq := abs_real_inner_le_norm (S F - T F) (S w - T w)
  calc
    _ ≤ |2 * inner ℝ (P f - Q f) (P u - Q u)| +
        |2 * inner ℝ (S F - T F) (S w - T w)| := abs_sub _ _
    _ = 2 * |inner ℝ (P f - Q f) (P u - Q u)| +
        2 * |inner ℝ (S F - T F) (S w - T w)| := by rw [abs_mul, abs_mul]; norm_num
    _ ≤ 2 * ((‖P f - f‖ + ‖Q f - f‖) * (2 * R)) +
        2 * ((‖S F - F‖ + ‖T F - F‖) * (2 * ‖w‖)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hp.trans
          (mul_le_mul hf hcu (norm_nonneg _) (by positivity))) (by norm_num))
        (mul_le_mul_of_nonneg_left (hq.trans
          (mul_le_mul hF hcw (norm_nonneg _) (by positivity))) (by norm_num))
    _ = _ := by ring

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Continuous tested identities extend from almost every time to the entire closed interval. -/

variable {H : Type*} [NormedAddCommGroup H]

theorem eqOn_Icc_of_ae_eq_and_initial {a b : ℝ} (_hab : a ≤ b)
    (f g : ℝ → H)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hae : f =ᵐ[volume.restrict (Set.Icc a b)] g) (ha : f a = g a) :
    Set.EqOn f g (Set.Icc a b) := by
  by_cases he : a = b
  · intro t ht
    have ht' : t = a := le_antisymm (he ▸ ht.2) ht.1
    exact ht' ▸ ha
  · exact Measure.eqOn_Icc_of_ae_eq volume he hae hf hg

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization Filter
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Spatial directional derivatives of jointly measurable, spatially differentiable fields are jointly measurable. -/

variable {T F : Type*} [MeasurableSpace T]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology F]

theorem measurable_directionalDerivative (C : T → Vec 2 → F)
    (hC : Measurable (Function.uncurry C))
    (hc : ∀ t, Differentiable ℝ (C t)) (e : Vec 2) :
    Measurable (fun p : T × Vec 2 => fderiv ℝ (C p.1) p.2 e) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let q : ℕ → T × Vec 2 → F := fun n p => (ε n)⁻¹ •
    (C p.1 (p.2 + ε n • e) - C p.1 p.2)
  have hq (n : ℕ) : Measurable (q n) := by
    exact ((hC.comp (measurable_fst.prodMk (measurable_snd.add measurable_const))).sub hC).const_smul _
  have hε : Tendsto ε atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall ?_⟩
    intro n
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, ε]
    positivity
  apply measurable_of_tendsto_metrizable hq
  apply tendsto_pi_nhds.mpr
  intro p
  have hpath : HasDerivAt (fun r : ℝ => p.2 + r • e) e 0 := by
    convert (hasDerivAt_const (0 : ℝ) p.2).add
      ((hasDerivAt_id (0 : ℝ)).smul_const e) using 1 <;> simp
    ext r
    rfl
  have hfd : HasFDerivAt (C p.1) (fderiv ℝ (C p.1) p.2) (p.2 + (0 : ℝ) • e) := by
    simpa only [zero_smul, add_zero] using (hc p.1 p.2).hasFDerivAt
  have hd : HasDerivAt (fun r : ℝ => C p.1 (p.2 + r • e))
      (fderiv ℝ (C p.1) p.2 e) 0 := hfd.comp_hasDerivAt 0 hpath
  simpa only [q, Function.comp_def, zero_add, zero_smul, add_zero] using
    hd.tendsto_slope_zero.comp hε

end AVRegularity.CoupledEnergyPlane.Variational
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CoupledEnergyPlane.Variational

/-! Assemble finitely many genuine continuous Bochner primitives. -/

variable {ι : Type*} [Fintype ι] {H : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, NormedSpace ℝ (H i)] [∀ i, CompleteSpace (H i)]

def finiteFamilyCurve {a b : ℝ} (U : ∀ i, C(Set.Icc a b, H i)) : C(Set.Icc a b, PiLp 2 H) :=
  ⟨fun t => WithLp.toLp 2 (fun i => U i t),
    (PiLp.continuous_toLp 2 H).comp (continuous_pi (fun i => (U i).continuous))⟩

omit [Fintype ι] [∀ i, NormedSpace ℝ (H i)] [∀ i, CompleteSpace (H i)] in
@[simp] theorem finiteFamilyCurve_component {a b : ℝ}
    (U : ∀ i, C(Set.Icc a b, H i)) (t : Set.Icc a b) (i : ι) :
    finiteFamilyCurve U t i = U i t := rfl

omit [∀ i, NormedSpace ℝ (H i)] [∀ i, CompleteSpace (H i)] in
theorem finiteFamilyRhs_intervalIntegrable {a b : ℝ} (hab : a ≤ b)
    (R : ∀ i, ℝ → H i) (hR : ∀ i, IntervalIntegrable (R i) volume a b) :
    IntervalIntegrable (fun s => WithLp.toLp 2 (fun i => R i s)) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  apply integrable_piLp_iff.mpr
  intro i
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp (hR i)

theorem finiteFamilyCurve_eq_primitive_of_components {a b : ℝ} (hab : a ≤ b)
    (U : ∀ i, C(Set.Icc a b, H i)) (f : ∀ i, H i) (R : ∀ i, ℝ → H i)
    (hR : ∀ i, IntervalIntegrable (R i) volume a b)
    (hU : ∀ i, ∀ t : Set.Icc a b, U i t = f i + ∫ s in a..t.val, R i s)
    (t : Set.Icc a b) :
    finiteFamilyCurve U t = WithLp.toLp 2 f +
      ∫ s in a..t.val, WithLp.toLp 2 (fun i => R i s) := by
  have hs : Set.uIcc a t.val ⊆ Set.uIcc a b := by
    rw [Set.uIcc_of_le t.property.1, Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc le_rfl t.property.2
  have hi := (finiteFamilyRhs_intervalIntegrable hab R hR).mono_set hs
  apply PiLp.ext
  intro i
  have hp := (PiLp.proj (𝕜 := ℝ) 2 H i).intervalIntegral_comp_comm hi
  change U i t = f i + (PiLp.proj (𝕜 := ℝ) 2 H i)
    (∫ s in a..t.val, WithLp.toLp 2 (fun j => R j s))
  rw [← hp]
  exact hU i t

end AVRegularity.CoupledEnergyPlane.Variational
end
end
