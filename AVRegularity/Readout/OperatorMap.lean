-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Readout.RepresentationEstimates
public import AVRegularity.Statements.Intermediate.Readout.RepresentationMap
public import AVRegularity.Statements.Intermediate.Readout.IsRepresentationAt
public import AVRegularity.Statements.Intermediate.Readout.RepresentationValue
public import AVRegularity.Statements.Intermediate.Readout.RepresentedSize

/-! Estimates and representation preservation for constant component maps. -/

@[expose] public section

open Homogenization
open scoped ENNReal

namespace AVRegularity.Readout

theorem profileSeminorm_comp_le {H H' : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup H'] [NormedSpace ℝ H']
    (R : H →L[ℝ] H') (lam s : ℝ) (K : ℕ) (F : Vec 2 → H)
    (hF : ContDiff ℝ K F) :
    profileSeminorm lam K s (fun x => R (F x)) ≤
      ENNReal.ofReal ‖R‖ * profileSeminorm lam K s F := by
  unfold profileSeminorm
  calc
    (∑ α ∈ multiIndicesBetween 1 K,
        ENNReal.ofReal (lam ^ ((↑(α 0 + α 1) : ℝ) - s) /
          multiIndexFactorial α) *
          supNorm (partialDerivative α (fun x => R (F x)))) ≤
      ∑ α ∈ multiIndicesBetween 1 K,
        ENNReal.ofReal (lam ^ ((↑(α 0 + α 1) : ℝ) - s) /
          multiIndexFactorial α) *
          (ENNReal.ofReal ‖R‖ * supNorm (partialDerivative α F)) := by
      apply Finset.sum_le_sum
      intro α hα
      have horder : α 0 + α 1 ≤ K := by
        simp only [multiIndicesBetween, Finset.mem_filter] at hα
        exact hα.2.2
      rw [partialDerivative_comp α horder R F hF]
      exact mul_le_mul_right
        (supNorm_comp_le R (partialDerivative α F)) _
    _ = ENNReal.ofReal ‖R‖ *
        (∑ α ∈ multiIndicesBetween 1 K,
          ENNReal.ofReal (lam ^ ((↑(α 0 + α 1) : ℝ) - s) /
            multiIndexFactorial α) * supNorm (partialDerivative α F)) := by
      calc
        _ = ∑ α ∈ multiIndicesBetween 1 K,
              ENNReal.ofReal ‖R‖ *
                (ENNReal.ofReal (lam ^ ((↑(α 0 + α 1) : ℝ) - s) /
                  multiIndexFactorial α) * supNorm (partialDerivative α F)) := by
          apply Finset.sum_congr rfl
          intro α hα
          ac_rfl
        _ = _ := by rw [Finset.mul_sum]

theorem holderSeminorm_comp_le {H H' : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup H'] [NormedSpace ℝ H']
    (R : H →L[ℝ] H') (s : ℝ) (F : Vec 2 → H) :
    holderSeminorm s (fun x => R (F x)) ≤
      ENNReal.ofReal ‖R‖ * holderSeminorm s F := by
  have hR : 0 ≤ ‖R‖ := norm_nonneg R
  unfold holderSeminorm
  apply iSup_le
  intro y
  apply iSup_le
  intro z
  apply iSup_le
  intro hdist
  have hden : 0 ≤ torusDist y z ^ s :=
    Real.rpow_nonneg (le_ciInf (fun _ => Real.sqrt_nonneg _)) s
  have hnum : ‖R (F y) - R (F z)‖ ≤ ‖R‖ * ‖F y - F z‖ := by
    rw [← map_sub]
    exact R.le_opNorm _
  have hquot := div_le_div_of_nonneg_right hnum hden
  calc
    ENNReal.ofReal (‖R (F y) - R (F z)‖ / torusDist y z ^ s) ≤
        ENNReal.ofReal (‖R‖ * (‖F y - F z‖ / torusDist y z ^ s)) := by
          apply ENNReal.ofReal_mono
          calc
            _ ≤ (‖R‖ * ‖F y - F z‖) / torusDist y z ^ s := hquot
            _ = ‖R‖ * (‖F y - F z‖ / torusDist y z ^ s) := by ring
    _ = ENNReal.ofReal ‖R‖ *
        ENNReal.ofReal (‖F y - F z‖ / torusDist y z ^ s) :=
      ENNReal.ofReal_mul hR
    _ ≤ ENNReal.ofReal ‖R‖ * holderSeminorm s F :=
      mul_le_mul_of_nonneg_left
        (le_iSup_of_le y (le_iSup_of_le z (le_iSup_of_le hdist le_rfl))) bot_le

theorem representation_map_isRepresentationAt {H H' : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup H'] [NormedSpace ℝ H']
    {e : ℝ} {K : ℕ} (r : Representation H) (R : H →L[ℝ] H')
    (hr : IsRepresentationAt e K r) : IsRepresentationAt e K (r.map R) := by
  rcases hr with ⟨he, he1, hbaseCD, hbasePer, hprofiles⟩
  refine ⟨he, he1, ?_, ?_, ?_⟩
  · exact R.contDiff.comp hbaseCD
  · intro n x
    exact congrArg R (hbasePer n x)
  · intro p hp
    simp only [Representation.map, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩
    rcases hprofiles q hq with ⟨hqCD, hqPer, heq, hq1⟩
    exact ⟨R.contDiff.comp hqCD, (fun n x => congrArg R (hqPer n x)), heq, hq1⟩

theorem representation_map_value {H H' : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup H'] [NormedSpace ℝ H']
    (r : Representation H) (R : H →L[ℝ] H') :
    (r.map R).value = fun x => R (r.value x) := by
  funext x
  simp only [Representation.value, Representation.map, List.map_map, Function.comp_def]
  change R (r.base x) +
      (r.profiles.map fun p => R (p.1 x)).sum =
    R (r.base x + (r.profiles.map fun p => p.1 x).sum)
  rw [map_add]
  congr 1
  induction r.profiles with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, map_add, ih]

theorem representedSize_map_le {H H' : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup H'] [NormedSpace ℝ H']
    {s e : ℝ} {K : ℕ} (r : Representation H) (R : H →L[ℝ] H')
    (hr : IsRepresentationAt e K r) :
    representedSize s K e (r.map R) ≤
      ENNReal.ofReal ‖R‖ * representedSize s K e r := by
  rcases hr with ⟨he, he1, hbaseCD, hbasePer, hprofiles⟩
  let c := ENNReal.ofReal ‖R‖
  have hbase :
      supNorm (fun x => R (r.base x)) +
        profileSeminorm e K s (fun x => R (r.base x)) +
        holderSeminorm s (fun x => R (r.base x)) ≤
      c * (supNorm r.base + profileSeminorm e K s r.base + holderSeminorm s r.base) := by
    have hs := supNorm_comp_le R r.base
    have hp := profileSeminorm_comp_le R e s K r.base hbaseCD
    have hh := holderSeminorm_comp_le R s r.base
    calc
      _ ≤ c * supNorm r.base + c * profileSeminorm e K s r.base +
          c * holderSeminorm s r.base := by
        exact add_le_add (add_le_add hs hp) hh
      _ = c * (supNorm r.base + profileSeminorm e K s r.base +
          holderSeminorm s r.base) := by ring
  have hprofilesCost :
      (r.profiles.map fun p => profileNorm p.2 K s (fun x => R (p.1 x))).sum ≤
        c * (r.profiles.map fun p => profileNorm p.2 K s p.1).sum := by
    calc
      (r.profiles.map fun p => profileNorm p.2 K s (fun x => R (p.1 x))).sum ≤
          (r.profiles.map fun p => c * profileNorm p.2 K s p.1).sum := by
        apply List.sum_le_sum
        intro p hp
        have hpCD := (hprofiles p hp).1
        have hs := supNorm_comp_le R p.1
        have hsemi := profileSeminorm_comp_le R p.2 s K p.1 hpCD
        calc
          profileNorm p.2 K s (fun x => R (p.1 x)) ≤
              ENNReal.ofReal (p.2 ^ (-s)) *
                  (c * supNorm p.1) + c * profileSeminorm p.2 K s p.1 := by
                rw [profileNorm]
                exact add_le_add
                  (mul_le_mul_of_nonneg_left hs bot_le) hsemi
          _ = c * profileNorm p.2 K s p.1 := by
                rw [profileNorm]
                ring
      _ = c * (r.profiles.map fun p => profileNorm p.2 K s p.1).sum := by
        induction r.profiles with
        | nil => simp
        | cons p ps ih =>
            simp only [List.map_cons, List.sum_cons]
            rw [ih, mul_add]
  unfold representedSize
  simp only [Representation.map]
  calc
    _ = (supNorm (fun x => R (r.base x)) +
          profileSeminorm e K s (fun x => R (r.base x)) +
          holderSeminorm s (fun x => R (r.base x))) +
        (r.profiles.map fun p => profileNorm p.2 K s (fun x => R (p.1 x))).sum := by
      simp only [List.map_map, Function.comp_def]
    _ ≤ c * (supNorm r.base + profileSeminorm e K s r.base + holderSeminorm s r.base) +
        c * (r.profiles.map fun p => profileNorm p.2 K s p.1).sum :=
      add_le_add hbase hprofilesCost
    _ = c * representedSize s K e r := by
      unfold representedSize
      ring

end AVRegularity.Readout
