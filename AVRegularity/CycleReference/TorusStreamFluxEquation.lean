-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleReference.ChartTestTransport
import AVRegularity.CycleReference.ChartCorrectionIntegrability
import AVRegularity.Construction.Scales.Times
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleReference.MeanEnhancementScale
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Algebra.Order.Star.Real
import Mathlib.CategoryTheory.Countable
import Mathlib.Tactic.Monotonicity.Lemmas

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory
open scoped Matrix ENNReal
namespace AVRegularity.CycleReference

/-! Integrable periodic weak-gradient pairings over a finite time slab. -/

 theorem cellSlab_continuous_memL2 (a c : ℝ) {u : ℝ × Vec 2 → ℝ} (hu : Continuous u) :
    MemLp u 2 (volume.restrict (Set.Ioo a c ×ˢ unitCube)) := by
  let K : Set (ℝ × Vec 2) := Set.Icc a c ×ˢ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_univ_pi (fun _ => isCompact_Icc))
  have hsub : Set.Ioo a c ×ˢ unitCube ⊆ K := by
    intro p hp
    exact ⟨⟨hp.1.1.le, hp.1.2.le⟩, fun i hi => ⟨(hp.2 i hi).1.le, (hp.2 i hi).2.le⟩⟩
  let : IsFiniteMeasure (volume.restrict (Set.Ioo a c ×ˢ unitCube)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (measure_mono hsub).trans_lt hK.measure_lt_top⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hu.continuousOn
  have ht : MemLp u ⊤ (volume.restrict (Set.Ioo a c ×ˢ unitCube)) := by
    apply memLp_top_of_bound hu.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod
      (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)))] with p hp
    exact hC p (hsub hp)
  exact ht.mono_exponent (by norm_num)

 theorem cellSlab_gradient_pair_integrable (a c : ℝ) {D V : ℝ × Vec 2 → Vec 2}
    (hD : ∀ i : Fin 2, MemLp (fun p => D p i) 2 (volume.restrict (Set.Ioo a c ×ˢ unitCube)))
    (hV : ∀ i : Fin 2, Continuous (fun p => V p i)) :
    Integrable (fun p => Homogenization.vecDot (D p) (V p))
      (volume.restrict (Set.Ioo a c ×ˢ unitCube)) := by
  have hi (i : Fin 2) : Integrable (fun p => D p i * V p i)
      (volume.restrict (Set.Ioo a c ×ˢ unitCube)) :=
    (hD i).integrable_mul (cellSlab_continuous_memL2 a c (hV i))
  exact integrable_finsetSum Finset.univ (fun i _ => hi i)

 theorem cellSlab_integral_eq_iterated {f : ℝ × Vec 2 → ℝ} {a c : ℝ}
    (hf : Integrable f (volume.restrict (Set.Ioo a c ×ˢ unitCube))) :
    (∫ p in Set.Ioo a c ×ˢ unitCube, f p) =
      ∫ t in Set.Ioo a c, ∫ x in unitCube, f (t, x) := by
  rw [cellSlab_measure_eq_prod] at hf ⊢
  exact integral_prod _ hf

 theorem cellSlab_divFree_drift_pairing (a c : ℝ)
    {u η : ℝ → Vec 2 → ℝ} {Du B : ℝ → Vec 2 → Vec 2}
    (hDu : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Du p.1 p.2 i) 2
      (volume.restrict (Set.Ioo a c ×ˢ unitCube)))
    (hw : ∀ᵐ t ∂(volume.restrict (Set.Ioo a c)), IsPeriodicH1With (u t) (Du t))
    (hB : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => B p.1 p.2))
    (hpB : ∀ t, IsZ2Periodic (B t)) (hdiv : ∀ t x, vecDiv (B t) x = 0)
    (hη : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => η p.1 p.2))
    (hpη : ∀ t, IsZ2Periodic (η t))
    (hi : Integrable (fun p : ℝ × Vec 2 => u p.1 p.2 * Homogenization.vecDot (B p.1 p.2)
      (spaceGrad (η p.1) p.2)) (volume.restrict (Set.Ioo a c ×ˢ unitCube))) :
    Integrable (fun p : ℝ × Vec 2 => Homogenization.vecDot (B p.1 p.2) (Du p.1 p.2) * η p.1 p.2)
      (volume.restrict (Set.Ioo a c ×ˢ unitCube)) ∧
    (∫ p in Set.Ioo a c ×ˢ unitCube, Homogenization.vecDot (B p.1 p.2) (Du p.1 p.2) * η p.1 p.2) =
      -∫ p in Set.Ioo a c ×ˢ unitCube, u p.1 p.2 * Homogenization.vecDot (B p.1 p.2)
        (spaceGrad (η p.1) p.2) := by
  have hd := cellSlab_gradient_pair_integrable a c hDu
    (fun i => (((continuous_apply i).comp hB.continuous).mul hη.continuous))
  have hdrift : Integrable (fun p : ℝ × Vec 2 => Homogenization.vecDot (B p.1 p.2) (Du p.1 p.2) * η p.1 p.2)
      (volume.restrict (Set.Ioo a c ×ˢ unitCube)) := by
    convert hd using 1
    funext p
    simp [Homogenization.vecDot, Fin.sum_univ_two]
    ring
  refine ⟨hdrift, ?_⟩
  rw [cellSlab_integral_eq_iterated hdrift, cellSlab_integral_eq_iterated hi, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hw] with t ht
  exact periodicH1_divFree_cell_pairing ht
    (hB.comp (contDiff_const.prodMk contDiff_id)) (hpB t) (hdiv t)
    (hη.comp (contDiff_const.prodMk contDiff_id)) (hpη t)

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance
namespace AVRegularity.CycleReference

/-! Energy-space transport in the named chart-pullback notation. -/

theorem chartPull_energySpace {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a c : ℝ) {θ₀ : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    (hθ : PlaneEnergySpace a c θ₀ θ Dθ) :
    PlaneEnergySpace a c (fun y => θ₀ (AVRegularity.streamFlow φ hφ a y s))
      (chartPull hφ s θ) (chartGradient hφ s Dθ) :=
  streamFlow_energy_space hφ s a c hθ.1 hθ.2.1 hθ.2.2.1 hθ.2.2.2.1 hθ.2.2.2.2

theorem chartUnpull_energySpace {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a c : ℝ) {θ₀ : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    (hθ : PlaneEnergySpace a c θ₀ θ Dθ) :
    PlaneEnergySpace a c (fun x => θ₀ (AVRegularity.streamFlow φ hφ s x a))
      (chartUnpull hφ s θ) (chartUnpullGradient hφ s Dθ) :=
  inverseStreamFlow_energy_space hφ s a c hθ.1 hθ.2.1 hθ.2.2.1 hθ.2.2.2.1 hθ.2.2.2.2

end AVRegularity.CycleReference
end
end

section
@[expose] public section
namespace AVRegularity.CycleReference

/-! Cell-corrector length relative to both preparation radii. -/

theorem bandChain_prepared_cell_length {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ M : ℕ, 1 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
        ∀ m : ℕ, 2 ≤ m → m ≤ M →
          ocDStar q Λ m (κ m) (κ (m - 1)) / ocRhoPar α q Λ m ≤
            C * ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q) ∧
          ocDStar q Λ m (κ m) (κ (m - 1)) / ocRh α q Λ m (κ (m - 1)) ≤
            C * ocEpsilon q Λ (m - 1) ^ (3 * ocDelta α q) ∧
          (m < M → ocAsymp C
            (ocDStar q Λ m (κ m) (κ (m - 1)) / ocRhoPar α q Λ m)
            (ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q)) ∧
            ocAsymp C (ocDStar q Λ m (κ m) (κ (m - 1)) / ocRh α q Λ m (κ (m - 1)))
            (ocEpsilon q Λ (m - 1) ^ (3 * ocDelta α q))) := by
  obtain ⟨Cd, hCd, Ld, hLd, hd⟩ := bandChain_cell_length hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Cr, hCr, Lr, hLr, hr⟩ := bandChain_renewal_radius hα0 hα1 hs0 hs1 hq hζ
  have hCdp : 0 < Cd := by linarith
  have hCrp : 0 < Cr := by linarith
  have hC : 1 ≤ Cd * Cr := by nlinarith
  have hCdC : Cd ≤ Cd * Cr := by nlinarith
  refine ⟨Cd * Cr, hC, max Ld Lr, hLd.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ M hM κ hκ m hm hmM
  have hΛd : Ld ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛr : Lr ≤ Λ := (le_max_right _ _).trans hΛ
  have h128 := hLd.trans hΛd
  have hΛ1 : 1 ≤ Λ := by omega
  let E := ocEpsilon q Λ (m - 1)
  let d := ocDStar q Λ m (κ m) (κ (m - 1))
  let r := ocRh α q Λ m (κ (m - 1))
  let a := ocGamma α q / 2 + 4 * ocDelta α q
  have hE : 0 < E := (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128).1
  have hB := bandChain_pos hΛ1 hζ hκ (show m - 1 ≤ M by omega)
  have hτ := AVRegularity.Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) hΛ1
  have hrp : 0 < r := Real.sqrt_pos.2 (mul_pos hB hτ)
  have hdr := hd Λ hΛd M hM κ hκ m hm hmM
  change d / E ≤ Cd * E ^ a ∧ (m < M → ocAsymp Cd (d / E) (E ^ a)) at hdr
  have hrr := hr Λ hΛr M hM κ hκ m hm hmM
  change ocAsymp Cr r (E ^ (1 + ocC α q)) at hrr
  have hrE : ocAsymp Cr (r / E) (E ^ ocC α q) := by
    have h := asymp_div hCrp (by norm_num : (0 : ℝ) < 1)
      (Real.rpow_pos_of_pos hE _).le hE hE hrr (asymp_one_self E)
    have heq : E ^ (1 + ocC α q) / E = E ^ ocC α q := by
      rw [← Real.rpow_sub_one hE.ne']
      congr 1
      ring
    simpa only [mul_one, heq] using h
  have hPar : ocRhoPar α q Λ m = E * E ^ (ocGamma α q / 2) := by
    unfold ocRhoPar
    rw [Real.rpow_add hE, Real.rpow_one]
  have hParRatio : d / ocRhoPar α q Λ m = (d / E) / E ^ (ocGamma α q / 2) := by
    rw [hPar]
    ring
  have hRhRatio : d / r = (d / E) / (r / E) := by field_simp
  have hPowPar : E ^ a / E ^ (ocGamma α q / 2) = E ^ (4 * ocDelta α q) := by
    rw [← Real.rpow_sub hE]
    congr 1
    dsimp [a]
    ring
  have hPowRh : E ^ a / E ^ ocC α q = E ^ (3 * ocDelta α q) := by
    rw [← Real.rpow_sub hE]
    congr 1
    dsimp [a, ocC]
    ring
  have hParUpper : d / ocRhoPar α q Λ m ≤ Cd * E ^ (4 * ocDelta α q) := by
    rw [hParRatio]
    have h := div_le_div_of_nonneg_right hdr.1 (Real.rpow_pos_of_pos hE (ocGamma α q / 2)).le
    have heq : (Cd * E ^ a) / E ^ (ocGamma α q / 2) = Cd * (E ^ a / E ^ (ocGamma α q / 2)) := by ring
    rw [heq, hPowPar] at h
    exact h
  have hRhUpper : d / r ≤ (Cd * Cr) * E ^ (3 * ocDelta α q) := by
    rw [hRhRatio]
    have h := quotient_upper_bound hCdp hCrp (Real.rpow_pos_of_pos hE a).le
      (Real.rpow_pos_of_pos hE _) (div_pos hrp hE) hdr.1 hrE.1
    simpa only [hPowRh] using h
  refine ⟨hParUpper.trans (mul_le_mul_of_nonneg_right hCdC (Real.rpow_pos_of_pos hE _).le), hRhUpper, ?_⟩
  intro hlt
  have hParAsymp : ocAsymp Cd (d / ocRhoPar α q Λ m) (E ^ (4 * ocDelta α q)) := by
    have h := asymp_div hCdp (by norm_num : (0 : ℝ) < 1) (Real.rpow_pos_of_pos hE a).le
      (Real.rpow_pos_of_pos hE _) (Real.rpow_pos_of_pos hE _) (hdr.2 hlt)
      (asymp_one_self (E ^ (ocGamma α q / 2)))
    simpa only [mul_one, ← hParRatio, hPowPar] using h
  have hRhAsymp : ocAsymp (Cd * Cr) (d / r) (E ^ (3 * ocDelta α q)) := by
    have h := asymp_div hCdp hCrp (Real.rpow_pos_of_pos hE a).le
      (Real.rpow_pos_of_pos hE _) (div_pos hrp hE) (hdr.2 hlt) hrE
    simpa only [← hRhRatio, hPowRh] using h
  exact ⟨asymp_mono_constant hCdp hCdC (Real.rpow_pos_of_pos hE _).le hParAsymp, hRhAsymp⟩

end AVRegularity.CycleReference
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory
namespace AVRegularity.CycleReference

/-! Periodic stream flux identity on the complete time slab. -/

theorem cellSlab_stream_flux_pairing (a b : ℝ)
    {u ψ η : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hDu : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Du p.1 p.2 i) 2
      (volume.restrict (Set.Ioo a b ×ˢ unitCube)))
    (hw : ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)), IsPeriodicH1With (u t) (Du t))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ψ p.1 p.2))
    (hpψ : ∀ t, IsZ2Periodic (ψ t))
    (hη : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => η p.1 p.2))
    (hpη : ∀ t, IsZ2Periodic (η t)) :
    Integrable (fun p : ℝ × Vec 2 =>
      Homogenization.vecDot ((ψ p.1 p.2 • sigmaMat).mulVec (Du p.1 p.2)) (spaceGrad (η p.1) p.2))
      (volume.restrict (Set.Ioo a b ×ˢ unitCube)) ∧
    Integrable (fun p : ℝ × Vec 2 =>
      Homogenization.vecDot (streamVel ψ p.1 p.2) (Du p.1 p.2) * η p.1 p.2)
      (volume.restrict (Set.Ioo a b ×ˢ unitCube)) ∧
    (∫ p in Set.Ioo a b ×ˢ unitCube,
      Homogenization.vecDot ((ψ p.1 p.2 • sigmaMat).mulVec (Du p.1 p.2)) (spaceGrad (η p.1) p.2)) =
    ∫ p in Set.Ioo a b ×ˢ unitCube,
      Homogenization.vecDot (streamVel ψ p.1 p.2) (Du p.1 p.2) * η p.1 p.2 := by
  have hi := cellSlab_gradient_pair_integrable a b hDu
    (fun i => hψ.continuous.mul (joint_rotated_gradient_smooth hη i).continuous)

  have hflux : Integrable (fun p : ℝ × Vec 2 =>
      Homogenization.vecDot ((ψ p.1 p.2 • sigmaMat).mulVec (Du p.1 p.2)) (spaceGrad (η p.1) p.2))
      (volume.restrict (Set.Ioo a b ×ˢ unitCube)) := by
    convert hi.neg using 1
    funext p
    simp [Homogenization.vecDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two, sigmaMat]
    ring
  have hd := cellSlab_gradient_pair_integrable a b hDu
    (fun i => ((joint_rotated_gradient_smooth hψ i).continuous.mul hη.continuous))

  have hdrift : Integrable (fun p : ℝ × Vec 2 =>
      Homogenization.vecDot (streamVel ψ p.1 p.2) (Du p.1 p.2) * η p.1 p.2)
      (volume.restrict (Set.Ioo a b ×ˢ unitCube)) := by
    convert hd using 1
    funext p
    simp [streamVel, Homogenization.vecDot, Fin.sum_univ_two, Matrix.mulVec, dotProduct]
    ring
  refine ⟨hflux, hdrift, ?_⟩
  rw [cellSlab_integral_eq_iterated hflux, cellSlab_integral_eq_iterated hdrift]
  apply integral_congr_ae
  filter_upwards [hw] with t ht
  exact periodicH1_stream_flux_cell_pairing ht
    (hψ.comp (contDiff_const.prodMk contDiff_id)) (hpψ t)
    (hη.comp (contDiff_const.prodMk contDiff_id)) (hpη t)

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance MeasureTheory
open scoped Matrix
namespace AVRegularity.CycleReference

/-! Equivalence of a weak stream drift and its antisymmetric divergence-form coefficient. -/

theorem planeWeakEquation_stream_flux_iff (a c : ℝ) (ψ : ℝ → Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ψ p.1 p.2))
    (A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (q : ℝ → Vec 2 → Vec 2)
    (f θ : ℝ → Vec 2 → ℝ) (θ₀ : Vec 2 → ℝ) (D : ℝ → Vec 2 → Vec 2)
    (hs : PlaneEnergySpace a c θ₀ θ D) :
    PlaneWeakEquation (streamVel ψ) A a c q f θ₀ θ D ↔
      PlaneWeakEquation (fun _ _ => 0) (fun t x => A t x + ψ t x • sigmaMat) a c q f θ₀ θ D := by
  have htest (η : ℝ → Vec 2 → ℝ)
      (hη : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => η p.1 p.2))
      (hc : HasCompactSupport (fun p : ℝ × Vec 2 => η p.1 p.2)) :
      (Integrable (planeWeakIntegrand (streamVel ψ) A q f θ D η)
        (volume.restrict (Set.Ioo a c ×ˢ Set.univ)) ∧
        (∫ p in Set.Ioo a c ×ˢ Set.univ, planeWeakIntegrand (streamVel ψ) A q f θ D η p) =
          ∫ x, θ₀ x * η a x) ↔
      (Integrable (planeWeakIntegrand (fun _ _ => 0) (fun t x => A t x + ψ t x • sigmaMat) q f θ D η)
        (volume.restrict (Set.Ioo a c ×ˢ Set.univ)) ∧
        (∫ p in Set.Ioo a c ×ˢ Set.univ, planeWeakIntegrand (fun _ _ => 0)
          (fun t x => A t x + ψ t x • sigmaMat) q f θ D η p) = ∫ x, θ₀ x * η a x) := by
    let μ : Measure (ℝ × Vec 2) := volume.restrict (Set.Ioo a c ×ˢ Set.univ)
    let Ip := planeWeakIntegrand (streamVel ψ) A q f θ D η
    let I0 := planeWeakIntegrand (fun _ _ => 0) (fun t x => A t x + ψ t x • sigmaMat) q f θ D η
    let K := fun p : ℝ × Vec 2 =>
      vecDot ((ψ p.1 p.2 • sigmaMat).mulVec (D p.1 p.2)) (spaceGrad (η p.1) p.2) -
        vecDot (streamVel ψ p.1 p.2) (D p.1 p.2) * η p.1 p.2
    obtain ⟨hf, hd, he⟩ := spacetime_stream_flux_pairing a c hs.1 hs.2.2.2.1 hs.2.2.2.2 hψ hη hc
    have hK : Integrable K μ := hf.sub hd
    have hK0 : ∫ p, K p ∂μ = 0 := by
      rw [integral_sub hf hd, he, sub_self]
    have hp : I0 = Ip + K := by
      funext p
      exact planeWeakIntegrand_stream_flux ψ A q f θ D η p
    change (Integrable Ip μ ∧ (∫ p, Ip p ∂μ) = _) ↔
      (Integrable I0 μ ∧ (∫ p, I0 p ∂μ) = _)
    constructor
    · rintro ⟨hi, he⟩
      rw [hp]
      refine ⟨hi.add hK, ?_⟩
      simp only [Pi.add_apply]
      rw [integral_add hi hK, hK0, add_zero]
      exact he
    · rintro ⟨hi, he⟩
      have hpi : Ip = I0 - K := by rw [hp]; abel
      rw [hpi]
      refine ⟨hi.sub hK, ?_⟩
      simp only [Pi.sub_apply]
      rw [integral_sub hi hK, hK0, sub_zero]
      exact he
  constructor
  · intro h η hη hc hz
    exact (htest η hη hc).mp (h η hη hc hz)
  · intro h η hη hc hz
    exact (htest η hη hc).mpr (h η hη hc hz)

theorem isPlaneEnergySolution_stream_flux_iff (a c : ℝ) (ψ : ℝ → Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ψ p.1 p.2))
    (A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (q : ℝ → Vec 2 → Vec 2)
    (f θ : ℝ → Vec 2 → ℝ) (θ₀ : Vec 2 → ℝ) :
    IsPlaneEnergySolution (streamVel ψ) A a c q f θ₀ θ ↔
      IsPlaneEnergySolution (fun _ _ => 0) (fun t x => A t x + ψ t x • sigmaMat) a c q f θ₀ θ := by
  rw [isPlaneEnergySolution_iff_energySpace_weakEquation,
    isPlaneEnergySolution_iff_energySpace_weakEquation]
  constructor
  · rintro ⟨D, hs, hw⟩
    exact ⟨D, hs, (planeWeakEquation_stream_flux_iff a c ψ hψ A q f θ θ₀ D hs).mp hw⟩
  · rintro ⟨D, hs, hw⟩
    exact ⟨D, hs, (planeWeakEquation_stream_flux_iff a c ψ hψ A q f θ θ₀ D hs).mpr hw⟩

end AVRegularity.CycleReference
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Filter Topology
namespace AVRegularity.CycleReference

/-! Separating the periodic energy space from the tested equation. -/

def TorusEnergySpace (a c : ℝ) (θ₀ : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
    (Dθ : ℝ → Vec 2 → Vec 2) : Prop :=
  (∀ t ∈ Set.Icc a c, IsZ2Periodic (θ t) ∧ MemL2On unitCube (θ t)) ∧
  (∀ t ∈ Set.Icc a c, Tendsto (fun s => eLpNorm (fun x => θ s x - θ t x) 2
    (volume.restrict unitCube)) (𝓝[Set.Icc a c] t) (𝓝 0)) ∧
  θ a =ᵐ[volume.restrict unitCube] θ₀ ∧
  (∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Dθ p.1 p.2 i) 2
    (volume.restrict (Set.Ioo a c ×ˢ unitCube))) ∧
  (∀ᵐ t ∂(volume.restrict (Set.Ioo a c)), IsPeriodicH1With (θ t) (Dθ t))

def TorusWeakEquation (b : ℝ → Vec 2 → Vec 2)
    (A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (a c : ℝ)
    (q : ℝ → Vec 2 → Vec 2) (f : ℝ → Vec 2 → ℝ)
    (θ₀ : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ) (Dθ : ℝ → Vec 2 → Vec 2) : Prop :=
  ∀ η : ℝ → Vec 2 → ℝ, IsWindowTestFunction c η →
    Integrable (planeWeakIntegrand b A q f θ Dθ η) (volume.restrict (Set.Ioo a c ×ˢ unitCube)) ∧
    (∫ p in Set.Ioo a c ×ˢ unitCube, planeWeakIntegrand b A q f θ Dθ η p) =
      ∫ x in unitCube, θ₀ x * η a x

 theorem isTorusEnergySolution_iff_energySpace_weakEquation
    (b : ℝ → Vec 2 → Vec 2) (A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (a c : ℝ)
    (q : ℝ → Vec 2 → Vec 2) (f : ℝ → Vec 2 → ℝ)
    (θ₀ : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ) :
    IsTorusEnergySolution b A a c q f θ₀ θ ↔
      ∃ Dθ, TorusEnergySpace a c θ₀ θ Dθ ∧ TorusWeakEquation b A a c q f θ₀ θ Dθ := by
  constructor
  · rintro ⟨D, hu, ht, hi, hD, hw, he⟩
    exact ⟨D, ⟨hu, ht, hi, hD, hw⟩, he⟩
  · rintro ⟨D, ⟨hu, ht, hi, hD, hw⟩, he⟩
    exact ⟨D, hu, ht, hi, hD, hw, he⟩

 theorem chartPull_torusEnergySpace {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a c : ℝ) (hac : a ≤ c)
    {θ₀ : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    (hp₀ : IsZ2Periodic θ₀) (hspace : TorusEnergySpace a c θ₀ θ Dθ) :
    TorusEnergySpace a c (fun x => θ₀ (AVRegularity.streamFlow φ hφ a x s))
      (chartPull hφ s θ) (chartGradient hφ s Dθ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    refine ⟨?_, streamFlow_cell_memL2 hφ t s (hspace.1 t ht).1 (hspace.1 t ht).2⟩
    intro k x
    change θ t (AVRegularity.streamFlow φ hφ t (x + latticeShift k) s) = _
    rw [streamFlow_lattice_equivariant, (hspace.1 t ht).1]
    rfl
  · exact streamFlow_cell_L2_trace_on hφ s (Set.Icc a c) θ
      (fun t ht => (hspace.1 t ht).1) (fun t ht => (hspace.1 t ht).2) hspace.2.1
  · exact streamFlow_cell_ae_eq hφ a s (hspace.1 a ⟨le_rfl, hac⟩).1 hp₀ hspace.2.2.1
  · exact streamFlow_cell_joint_gradient_memL2 hφ s a c
      (hspace.2.2.2.2.mono (fun _ ht => ht.2.1)) hspace.2.2.2.1
  · filter_upwards [hspace.2.2.2.2] with t ht
    exact streamFlow_periodicH1 hφ t s ht

 theorem chartUnpull_torusEnergySpace {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a c : ℝ) (hac : a ≤ c)
    {θ₀ : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    (hp₀ : IsZ2Periodic θ₀) (hspace : TorusEnergySpace a c θ₀ θ Dθ) :
    TorusEnergySpace a c (fun x => θ₀ (AVRegularity.streamFlow φ hφ s x a))
      (chartUnpull hφ s θ) (chartUnpullGradient hφ s Dθ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    refine ⟨?_, streamFlow_cell_memL2 hφ s t (hspace.1 t ht).1 (hspace.1 t ht).2⟩
    intro k x
    change θ t (AVRegularity.streamFlow φ hφ s (x + latticeShift k) t) = _
    rw [streamFlow_lattice_equivariant, (hspace.1 t ht).1]
    rfl
  · exact inverseStreamFlow_cell_L2_trace_on hφ s (Set.Icc a c) θ
      (fun t ht => (hspace.1 t ht).1) (fun t ht => (hspace.1 t ht).2) hspace.2.1
  · exact streamFlow_cell_ae_eq hφ s a (hspace.1 a ⟨le_rfl, hac⟩).1 hp₀ hspace.2.2.1
  · exact inverseStreamFlow_cell_joint_gradient_memL2 hφ s a c
      (hspace.2.2.2.2.mono (fun _ ht => ht.2.1)) hspace.2.2.2.1
  · filter_upwards [hspace.2.2.2.2] with t ht
    exact streamFlow_periodicH1 hφ s t ht

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance MeasureTheory
namespace AVRegularity.CycleReference

/-! Only coefficient values inside the time slab enter its weak equation. -/

theorem torusWeakEquation_coefficients_congr (a c : ℝ)
    (b b' : ℝ → Vec 2 → Vec 2)
    (A A' : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hb : ∀ t ∈ Set.Ioo a c, ∀ x, b t x = b' t x)
    (hA : ∀ t ∈ Set.Ioo a c, ∀ x, A t x = A' t x)
    (q : ℝ → Vec 2 → Vec 2) (f θ : ℝ → Vec 2 → ℝ)
    (θ₀ : Vec 2 → ℝ) (D : ℝ → Vec 2 → Vec 2) :
    TorusWeakEquation b A a c q f θ₀ θ D ↔ TorusWeakEquation b' A' a c q f θ₀ θ D := by
  have he (η : ℝ → Vec 2 → ℝ) : planeWeakIntegrand b A q f θ D η =ᵐ[
      volume.restrict (Set.Ioo a c ×ˢ unitCube)] planeWeakIntegrand b' A' q f θ D η := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod (MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Ioo)))] with p hp
    unfold planeWeakIntegrand
    rw [hb p.1 hp.1 p.2, hA p.1 hp.1 p.2]
  constructor
  · intro h η hη
    obtain ⟨hi, heq⟩ := h η hη
    exact ⟨hi.congr (he η), (integral_congr_ae (he η)).symm.trans heq⟩
  · intro h η hη
    obtain ⟨hi, heq⟩ := h η hη
    exact ⟨hi.congr (he η).symm, (integral_congr_ae (he η)).trans heq⟩

theorem isTorusEnergySolution_coefficients_congr (a c : ℝ)
    (b b' : ℝ → Vec 2 → Vec 2)
    (A A' : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hb : ∀ t ∈ Set.Ioo a c, ∀ x, b t x = b' t x)
    (hA : ∀ t ∈ Set.Ioo a c, ∀ x, A t x = A' t x)
    (q : ℝ → Vec 2 → Vec 2) (f θ : ℝ → Vec 2 → ℝ) (θ₀ : Vec 2 → ℝ) :
    IsTorusEnergySolution b A a c q f θ₀ θ ↔ IsTorusEnergySolution b' A' a c q f θ₀ θ := by
  rw [isTorusEnergySolution_iff_energySpace_weakEquation,
    isTorusEnergySolution_iff_energySpace_weakEquation]
  constructor
  · rintro ⟨D, hs, hw⟩
    exact ⟨D, hs, (torusWeakEquation_coefficients_congr a c b b' A A' hb hA q f θ θ₀ D).mp hw⟩
  · rintro ⟨D, hs, hw⟩
    exact ⟨D, hs, (torusWeakEquation_coefficients_congr a c b b' A A' hb hA q f θ θ₀ D).mpr hw⟩

end AVRegularity.CycleReference
end
end

section
@[expose] public section
namespace AVRegularity.CycleReference

/-! Covariance at every level of a permitted diffusivity chain. -/

theorem bandChain_covariance_bound {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ M : ℕ, 1 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
        ∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ (s t : ℝ) (i j : Fin 2),
          |ocCovariance α q Λ ζ m (κ m) (κ (m - 1)) s t i j| ≤
            C * κ (m - 1) * ocTauP α q Λ m := by
  obtain ⟨Ce, hCe, Le, hLe, he⟩ := bandChain_enhancement_bound hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Cm, hCm, Lm, hLm, hm⟩ := bandChain_memory_scale hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨K, hK, hc⟩ := refFlux_covariance_primitive hζ
  let D := 80 + 144 * K * Cm
  have hD : 1 ≤ D := by
    have ha : 0 ≤ K * Cm := mul_nonneg hK (by linarith)
    dsimp [D]
    linarith only [ha]
  have hDp : 0 ≤ D := by linarith
  have hCep : 0 < Ce := by linarith
  have hCmp : 0 < Cm := by linarith
  refine ⟨D * Ce, by nlinarith, max Le Lm, hLe.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ M hM κ hκ m h2 hMle s t i j
  have hΛe : Le ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛm : Lm ≤ Λ := (le_max_right _ _).trans hΛ
  have h128 := hLe.trans hΛe
  have hΛ1 : 1 ≤ Λ := by omega
  have hν := bandChain_pos hΛ1 hζ hκ hMle
  have hB := bandChain_pos hΛ1 hζ hκ (show m - 1 ≤ M by omega)
  have hE := AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128
  have hd := (AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).2.1
  let H := ocHStar α q Λ m (κ m)
  let τ := ocTau α q Λ m
  let h := ocTauPP α q Λ m
  let P := ocTauP α q Λ m
  let R := (ocMu q Λ m (κ m) * τ)⁻¹
  have hH : 0 < H := ocHStar_pos hΛ1 hν
  have hτ : 0 < τ := AVRegularity.Construction.Stream.ocTau_pos hΛ1
  have hh : 0 < h := AVRegularity.Construction.Stream.ocTauPP_pos hΛ1
  have hτP : τ ≤ P := (pulse_time_scale_relations hΛ1).1
  have hP : 0 < P := hτ.trans_le hτP
  have hR0 : 0 ≤ R := (inv_pos.mpr (mul_pos (ocMu_pos hΛ1 hν) hτ)).le
  have hR : R ≤ Cm * ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q) :=
    (inverse_memory_rate_time_le hΛ1 hν hτ).trans (hm Λ hΛm M hM κ hκ m h2 hMle).1
  have hmem : h * R ≤ 9 * Cm * P := by
    have ha := mul_le_mul_of_nonneg_left hR hh.le
    have hb := mul_le_mul_of_nonneg_left
      (renewal_memory_scale_le_quiet_margin hΛ1 hE.1 hE.2.1 hd.le) hCmp.le
    calc
      h * R ≤ h * (Cm * ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q)) := ha
      _ = Cm * (h * ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q)) := by ring
      _ ≤ Cm * (9 * P) := hb
      _ = 9 * Cm * P := by ring
  have hHup : H ≤ Ce * κ (m - 1) := by
    have hhH : H ≤ ocEpsilon q Λ m ^ (2 * (1 + α)) / κ m := by
      dsimp [H, ocHStar]
      rw [show ocEpsilon q Λ m ^ (2 * (1 + α)) / (2 * κ m) =
        (ocEpsilon q Λ m ^ (2 * (1 + α)) / κ m) / 2 by ring]
      have hx : 0 ≤ ocEpsilon q Λ m ^ (2 * (1 + α)) / κ m :=
        div_nonneg (Real.rpow_pos_of_pos
          (AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ1) _).le hν.le
      linarith only [hx]
    exact hhH.trans ((by linarith only [hν] : ocEpsilon q Λ m ^ (2 * (1 + α)) / κ m ≤
      κ m + ocEpsilon q Λ m ^ (2 * (1 + α)) / κ m).trans (he Λ hΛe M hM κ hκ m h2 hMle))
  have hmean := hκ.2 m (by omega) hMle
  have hcov := hc α q Λ m hΛ1 (κ m) hν s t i j
  rw [← hmean] at hcov
  have hform : 16 * H * τ + 4 * H * (4 * h * (K / (ocMu q Λ m (κ m) * τ)) + 16 * P) =
      16 * H * τ + 16 * H * K * (h * R) + 64 * H * P := by
    dsimp [R]
    rw [div_eq_mul_inv]
    ring
  change |ocCovariance α q Λ ζ m (κ m) (κ (m - 1)) s t i j| ≤
    16 * H * τ + 4 * H * (4 * h * (K / (ocMu q Λ m (κ m) * τ)) + 16 * P) at hcov
  rw [hform] at hcov
  have ha := mul_le_mul_of_nonneg_left hτP (by positivity : 0 ≤ 16 * H)
  have hb := mul_le_mul_of_nonneg_left hmem (by positivity : 0 ≤ 16 * H * K)
  have hup : 16 * H * τ + 16 * H * K * (h * R) + 64 * H * P ≤ D * H * P := by
    dsimp [D]
    nlinarith only [ha, hb]
  have hf := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hHup hDp) hP.le
  exact hcov.trans (hup.trans (by convert hf using 1; ring))

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance MeasureTheory
open scoped Matrix
namespace AVRegularity.CycleReference

/-! Forward transport of the physical weak equation to the material chart. -/

theorem chartPull_weakEquation {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s ν a c : ℝ)
    (b q : ℝ → Vec 2 → Vec 2) (f θ : ℝ → Vec 2 → ℝ) (θ₀ : Vec 2 → ℝ)
    (Dθ : ℝ → Vec 2 → Vec 2) (hspace : PlaneEnergySpace a c θ₀ θ Dθ)
    (hweak : PlaneWeakEquation b (fun _ _ => ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a c q f θ₀ θ Dθ) :
    PlaneWeakEquation (chartVector hφ s (fun t x => b t x - streamVel φ t x))
      (fun t y => ν • chartMetric hφ s t y) a c (chartVector hφ s q) (chartPull hφ s f)
      (fun y => θ₀ (AVRegularity.streamFlow φ hφ a y s)) (chartPull hφ s θ) (chartGradient hφ s Dθ) := by
  intro ζ hζ hcζ hzζ
  let η := chartUnpull hφ s ζ
  have hη : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => η p.1 p.2) :=
    inverseStreamFlow_test_smooth hφ s hζ
  have hcη : HasCompactSupport (fun p : ℝ × Vec 2 => η p.1 p.2) :=
    inverseStreamFlow_test_compact hφ s hcζ
  have hzη : ∀ t, c ≤ t → ∀ x, η t x = 0 := fun t ht x => hzζ t ht _
  have hI := fun η hη hcη hzη => (hweak η hη hcη hzη).1
  have hi := tested_integrability_implies_drift_correction_integrability b
    (fun _ _ => ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) q f θ Dθ a c hI (streamVel φ)
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ).smooth η hη hcη hzη
  have ht := chart_test_transport_of_drift_correction_integrable hφ s ν a c b q f θ Dθ
    hspace.1 hspace.2.2.2.1 hspace.2.2.2.2 η hη hcη hi
  obtain ⟨hip, hep⟩ := hweak η hη hcη hzη
  have hm := ht.1.mpr hip
  have he := (ht.2 hip).trans hep
  have hp : chartPull hφ s η = ζ := chartPull_chartUnpull hφ s ζ
  rw [hp] at hm he
  refine ⟨hm, he.trans ?_⟩
  symm
  calc
    (∫ y, θ₀ (AVRegularity.streamFlow φ hφ a y s) * ζ a y) =
        ∫ y, θ₀ (AVRegularity.streamFlow φ hφ a y s) * η a (AVRegularity.streamFlow φ hφ a y s) := by
          rw [← hp]
          rfl
    _ = ∫ x, θ₀ x * η a x := integral_streamFlow hφ a s (fun x => θ₀ x * η a x)

end AVRegularity.CycleReference
end
end

section
@[expose] public section
namespace AVRegularity.CycleReference

/-! All four covariance estimates with a common uniform constant. -/

theorem bandChain_covariance_estimates {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ M : ℕ, 1 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
        ∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ (s t : ℝ) (i j : Fin 2),
          |ocCovariance α q Λ ζ m (κ m) (κ (m - 1)) s t i j| ≤
            C * κ (m - 1) * ocTauP α q Λ m ∧
          |ocCovariance α q Λ ζ m (κ m) (κ (m - 1)) s t i j| /
            ocEpsilon q Λ (m - 1) ^ 2 ≤ C * ocEpsilon q Λ (m - 1) ^
              (ocGamma α q + 3 * ocDelta α q) ∧
          |ocCovariance α q Λ ζ m (κ m) (κ (m - 1)) s t i j| /
              ocRhoPar α q Λ m ^ 2 + ocA α q Λ (m - 1) *
              |ocCovariance α q Λ ζ m (κ m) (κ (m - 1)) s t i j| / κ (m - 1) ≤
            C * ocEpsilon q Λ (m - 1) ^ (3 * ocDelta α q) ∧
          |ocCovariance α q Λ ζ m (κ m) (κ (m - 1)) s t i j| /
            ocRh α q Λ m (κ (m - 1)) ^ 2 ≤
              C * ocEpsilon q Λ (m - 1) ^ ocDelta α q := by
  obtain ⟨Cv, hCv, Lv, hLv, hv⟩ := bandChain_covariance_bound hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Cp, hCp, Lp, hLp, hp⟩ := bandChain_parent_comparisons hα0 hα1 hs0 hs1 hq hζ
  let T : ℝ := 2 ^ (26 : ℕ) * 9
  have hT : 1 ≤ T := by dsimp [T]; norm_num
  have hTp : 0 < T := by linarith
  have hCvp : 0 < Cv := by linarith
  have hCpp : 0 < Cp := by linarith
  let C := Cv + Cv * Cp * T + Cv * T + Cv * T ^ 2
  have h0 : 0 ≤ Cv * Cp * T := by positivity
  have h1 : 0 ≤ Cv * T := by positivity
  have h2 : 0 ≤ Cv * T ^ 2 := by positivity
  have hCvC : Cv ≤ C := by dsimp [C]; linarith only [h0, h1, h2]
  have hPowC : Cv * Cp * T ≤ C := by dsimp [C]; linarith only [hCv, h1, h2]
  have hParC : Cv * Cp * T + Cv * T ≤ C := by dsimp [C]; linarith only [hCv, h2]
  have hRhC : Cv * T ^ 2 ≤ C := by dsimp [C]; linarith only [hCv, h0, h1]
  refine ⟨C, hCv.trans hCvC, max Lv Lp, hLv.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ M hM κ hκ m hm hmM s t i j
  have hΛv : Lv ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛp : Lp ≤ Λ := (le_max_right _ _).trans hΛ
  have h128 := hLv.trans hΛv
  have hΛ1 : 1 ≤ Λ := by omega
  have hE := (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128).1
  have hB := bandChain_pos hΛ1 hζ hκ (show m - 1 ≤ M by omega)
  have hh := AVRegularity.Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) hΛ1
  have hP := (AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ1).trans_le
    (pulse_time_scale_relations hΛ1).1
  have hcov := hv Λ hΛv M hM κ hκ m hm hmM s t i j
  have hBu := (hp Λ hΛp M hM κ hκ m hm hmM).1.2
  have hPu := (ocTauP_asymp hα0 hα1 hs0 hs1 hq h128 (m := m)).2
  have hhl := (ocTauPP_asymp hα0 hα1 hs0 hs1 hq h128 (m := m)).1
  have hTsmall : (2 ^ (26 : ℕ) : ℝ) ≤ T := by dsimp [T]; norm_num
  have hhl' : T⁻¹ * ocEpsilon q Λ (m - 1) ^ (2 - (1 + α) + 2 * ocDelta α q) ≤
      ocTauPP α q Λ m := (mul_le_mul_of_nonneg_right
        ((inv_le_inv₀ hTp (by norm_num : (0 : ℝ) < 2 ^ (26 : ℕ))).2 hTsmall)
          (Real.rpow_pos_of_pos hE _).le).trans hhl
  have hn := covariance_power_normalizations (β := 1 + α) hE hCvp.le hCpp hTp
    (abs_nonneg _) hB hh hP hcov hBu hPu hhl'
  have hfirst := hcov.trans (by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCvC hB.le) hP.le
    exact h)
  refine ⟨hfirst, ?_, ?_, ?_⟩
  · exact hn.1.trans (mul_le_mul_of_nonneg_right hPowC (Real.rpow_pos_of_pos hE _).le)
  · change _ / (ocEpsilon q Λ (m - 1) ^ (1 + ocGamma α q / 2)) ^ 2 +
      ocEpsilon q Λ (m - 1) ^ ((1 + α) - 2) * _ / κ (m - 1) ≤ _
    exact hn.2.1.trans (mul_le_mul_of_nonneg_right hParC (Real.rpow_pos_of_pos hE _).le)
  · exact hn.2.2.trans (mul_le_mul_of_nonneg_right hRhC (Real.rpow_pos_of_pos hE _).le)

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance MeasureTheory
open scoped Matrix
namespace AVRegularity.CycleReference

/-! Equivalence of a weak stream drift and its antisymmetric divergence-form coefficient. -/

theorem torusWeakEquation_stream_flux_iff (a c : ℝ) (ψ : ℝ → Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ψ p.1 p.2))
    (hpψ : ∀ t, IsZ2Periodic (ψ t))
    (A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (q : ℝ → Vec 2 → Vec 2)
    (f θ : ℝ → Vec 2 → ℝ) (θ₀ : Vec 2 → ℝ) (D : ℝ → Vec 2 → Vec 2)
    (hs : TorusEnergySpace a c θ₀ θ D) :
    TorusWeakEquation (streamVel ψ) A a c q f θ₀ θ D ↔
      TorusWeakEquation (fun _ _ => 0) (fun t x => A t x + ψ t x • sigmaMat) a c q f θ₀ θ D := by
  have htest (η : ℝ → Vec 2 → ℝ)
      (hη : IsWindowTestFunction c η) :
      (Integrable (planeWeakIntegrand (streamVel ψ) A q f θ D η)
        (volume.restrict (Set.Ioo a c ×ˢ unitCube)) ∧
        (∫ p in Set.Ioo a c ×ˢ unitCube, planeWeakIntegrand (streamVel ψ) A q f θ D η p) =
          ∫ x in unitCube, θ₀ x * η a x) ↔
      (Integrable (planeWeakIntegrand (fun _ _ => 0) (fun t x => A t x + ψ t x • sigmaMat) q f θ D η)
        (volume.restrict (Set.Ioo a c ×ˢ unitCube)) ∧
        (∫ p in Set.Ioo a c ×ˢ unitCube, planeWeakIntegrand (fun _ _ => 0)
          (fun t x => A t x + ψ t x • sigmaMat) q f θ D η p) = ∫ x in unitCube, θ₀ x * η a x) := by
    let μ : Measure (ℝ × Vec 2) := volume.restrict (Set.Ioo a c ×ˢ unitCube)
    let Ip := planeWeakIntegrand (streamVel ψ) A q f θ D η
    let I0 := planeWeakIntegrand (fun _ _ => 0) (fun t x => A t x + ψ t x • sigmaMat) q f θ D η
    let K := fun p : ℝ × Vec 2 =>
      vecDot ((ψ p.1 p.2 • sigmaMat).mulVec (D p.1 p.2)) (spaceGrad (η p.1) p.2) -
        vecDot (streamVel ψ p.1 p.2) (D p.1 p.2) * η p.1 p.2
    obtain ⟨hf, hd, he⟩ := cellSlab_stream_flux_pairing a c hs.2.2.2.1 hs.2.2.2.2 hψ hpψ hη.1 hη.2.1
    have hK : Integrable K μ := hf.sub hd
    have hK0 : ∫ p, K p ∂μ = 0 := by
      rw [integral_sub hf hd, he, sub_self]
    have hp : I0 = Ip + K := by
      funext p
      exact planeWeakIntegrand_stream_flux ψ A q f θ D η p
    change (Integrable Ip μ ∧ (∫ p, Ip p ∂μ) = _) ↔
      (Integrable I0 μ ∧ (∫ p, I0 p ∂μ) = _)
    constructor
    · rintro ⟨hi, he⟩
      rw [hp]
      refine ⟨hi.add hK, ?_⟩
      simp only [Pi.add_apply]
      rw [integral_add hi hK, hK0, add_zero]
      exact he
    · rintro ⟨hi, he⟩
      have hpi : Ip = I0 - K := by rw [hp]; abel
      rw [hpi]
      refine ⟨hi.sub hK, ?_⟩
      simp only [Pi.sub_apply]
      rw [integral_sub hi hK, hK0, sub_zero]
      exact he
  constructor
  · intro h η hη
    exact (htest η hη).mp (h η hη)
  · intro h η hη
    exact (htest η hη).mpr (h η hη)

theorem isTorusEnergySolution_stream_flux_iff (a c : ℝ) (ψ : ℝ → Vec 2 → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ψ p.1 p.2))
    (hpψ : ∀ t, IsZ2Periodic (ψ t))
    (A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (q : ℝ → Vec 2 → Vec 2)
    (f θ : ℝ → Vec 2 → ℝ) (θ₀ : Vec 2 → ℝ) :
    IsTorusEnergySolution (streamVel ψ) A a c q f θ₀ θ ↔
      IsTorusEnergySolution (fun _ _ => 0) (fun t x => A t x + ψ t x • sigmaMat) a c q f θ₀ θ := by
  rw [isTorusEnergySolution_iff_energySpace_weakEquation,
    isTorusEnergySolution_iff_energySpace_weakEquation]
  constructor
  · rintro ⟨D, hs, hw⟩
    exact ⟨D, hs, (torusWeakEquation_stream_flux_iff a c ψ hψ hpψ A q f θ θ₀ D hs).mp hw⟩
  · rintro ⟨D, hs, hw⟩
    exact ⟨D, hs, (torusWeakEquation_stream_flux_iff a c ψ hψ hpψ A q f θ θ₀ D hs).mpr hw⟩

end AVRegularity.CycleReference
end
end
