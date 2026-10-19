-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleReference.ChartIntegrandAlgebra
public import AVRegularity.Statements.Intermediate.CycleJoint.OcQuietTimes
public import AVRegularity.Statements.Construction.IsFastProfile
import AVRegularity.Construction.Stream.NextAdmissible
public import AVRegularity.CycleJoint.PeriodicMultiplicationJetEnergy
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyDomainOnWindow

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! Even fast-grid centers have fixed quiet margins on both sides. -/

theorem even_fast_center_quiet_margin {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (j : ℤ) (hj : Even j) :
    Set.Icc (((j : ℝ) - 1 / 3) * ocTau α q Λ m)
      (((j : ℝ) + 1 / 3) * ocTau α q Λ m) ⊆ ocQuietTimes α q Λ ζ m := by
  intro t ht
  apply CycleReference.pulseStreamVel_eq_zero_of_quiet
  intro k hk
  by_contra hp
  have hd := CycleReference.pulse_nonzero_center_distance hΛ hζ hp
  have hτ := Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  obtain ⟨a, ha⟩ := hj
  obtain ⟨b, hb⟩ := hk
  have hne : j ≠ k := by omega
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · have hgap : (j : ℝ) + 1 ≤ k := by exact_mod_cast (show j + 1 ≤ k by omega)
    have hm := mul_le_mul_of_nonneg_right hgap hτ.le
    nlinarith [hd.1, ht.2]
  · have hgap : (k : ℝ) + 1 ≤ j := by exact_mod_cast (show k + 1 ≤ j by omega)
    have hm := mul_le_mul_of_nonneg_right hgap hτ.le
    nlinarith [hd.2, ht.1]

/-! Slow envelopes supply quiet margins at the exact renewal boundaries. -/

theorem slowEnvelope_zero_on_renewal_quiet_margin {α q : ℝ} {Λ m : ℕ}
    (hΛ : 1 ≤ Λ) (l : ℤ) {t : ℝ}
    (ht : t ∈ Set.Icc (((l : ℝ) + 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m)
      (((l : ℝ) + 1 / 2) * ocTauPP α q Λ m + ocTauP α q Λ m)) (j : ℤ) :
    slowEnvelope α q Λ m j t = 0 := by
  have hPP := Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) hΛ
  have hP : 0 < ocTauP α q Λ m := by
    unfold ocTauP
    apply div_pos hPP
    have hL : 0 < ocL α q Λ m := by unfold ocL; omega
    exact_mod_cast hL
  unfold slowEnvelope
  by_cases hj : j ≤ l
  · have hjr : (j : ℝ) ≤ l := by exact_mod_cast hj
    have hm := mul_le_mul_of_nonneg_right hjr hPP.le
    have hz : Real.smoothTransition
        ((((j : ℝ) + 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m - t) /
          ocTauP α q Λ m) = 0 := Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith [ht.1]) hP.le)
    rw [hz, mul_zero]
  · have hjr : (l : ℝ) + 1 ≤ j := by exact_mod_cast (show l + 1 ≤ j by omega)
    have hm := mul_le_mul_of_nonneg_right hjr hPP.le
    have hz : Real.smoothTransition
        ((t - ((j : ℝ) - 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m) /
          ocTauP α q Λ m) = 0 := Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith [ht.2]) hP.le)
    rw [hz, zero_mul]

theorem renewal_boundary_quiet_margin {α q : ℝ} {Λ m : ℕ}
    (hΛ : 1 ≤ Λ) (ζ : ℝ → ℝ) (l : ℤ) :
    Set.Icc (((l : ℝ) + 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m)
      (((l : ℝ) + 1 / 2) * ocTauPP α q Λ m + ocTauP α q Λ m) ⊆
      ocQuietTimes α q Λ ζ m := by
  intro t ht
  apply CycleReference.pulseStreamVel_eq_zero_of_quiet
  intro k _
  unfold ocPulse
  rw [slowEnvelope_zero_on_renewal_quiet_margin hΛ l ht, zero_mul]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The independent smooth envelope supplies actual dimensional sample smoothness on every active output piece. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem active_dimFlux_spatial_smooth (F : ChartedFamily ι h D P Ctx)
    (ν e E a b : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (p : (F.locally_finite t t).toFinset)
    (c : Ctx p) (v u : ι) (γ : F.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) :
    ContDiff ℝ (n v : ℕ) (fun yz : Vec 2 × Vec 2 =>
      F.dimFlux ν e E p c v u γ d I t yz.1 yz.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro yz
  have hf := hs p c v u γ d I (t, yz.1)
    ⟨⟨(piece_time_finset_mem_iff F t p).mp p.property, ht⟩, Set.mem_univ _⟩ yz.2
  have hg : ContDiff ℝ (n v : ℕ) (fun w : Vec 2 × Vec 2 => (E⁻¹ • w.1, w.2)) :=
    (contDiff_fst.const_smul (E⁻¹)).prodMk contDiff_snd
  have hh := hf.comp yz hg.contDiffAt
  simpa only [ChartedFamily.dimFlux, ChartedFamily.slowFlux, Function.comp_def] using
    hh.const_smul (ν * e ^ (d - 2))

theorem active_pieceDimensionalNativeJetArray_smooth (F : ChartedFamily ι h D P Ctx)
    (ν e E a b : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (p : (F.locally_finite t t).toFinset)
    (c : Ctx p) (v u : ι) (γ : F.Γ v u) (r : ℕ) (I : DerivativeWord2 r) :
    ContDiff ℝ (n v : ℕ) (pieceDimensionalNativeJetArray F ν e E p c v u γ t r I) := by
  exact (active_dimFlux_spatial_smooth F ν e E a b n hs t ht p c v u γ (r + 1) I).comp
    (contDiff_id.prodMk (contDiff_id.const_smul (e⁻¹)))

end AVRegularity.CycleJointProofs
end
end
