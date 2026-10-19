-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.InactiveTimeZeroFamilyPointwiseEnvelope

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The plane patch energies of a periodic datum sum to at most its cell energy. -/

theorem periodic_patch_integral_budget {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) (g : Vec 2 → ℝ≥0∞) (hg : Measurable g)
    (hper : AVenhance.IsZ2Periodic g) :
    (∑ j : Fin 2 → Fin N, ∫⁻ x,
      ENNReal.ofReal ((spatialPatchCutoff ζ N (fun i => (j i : ℤ)) x) ^ 2) * g x ∂volume) ≤
      ∫⁻ x in Applications.cellI, g x ∂volume := by
  have hper' (n : Fin 2 → ℤ) (x : Vec 2) :
      g (x + AVenhance.latticeShift n) = g x := hper n x
  let w (j : Fin 2 → Fin N) (n : Fin 2 → ℤ) (x : Vec 2) : ℝ≥0∞ :=
    ENNReal.ofReal ((spatialPatchCutoff ζ N (fun i => (j i : ℤ))
      (x + AVenhance.latticeShift n)) ^ 2)
  have hw (j : Fin 2 → Fin N) (n : Fin 2 → ℤ) : Measurable (w j n) := by
    apply Measurable.ennreal_ofReal
    exact (((spatialPatchCutoff_smooth hζ N _).continuous.measurable).comp
      (measurable_id.add measurable_const)).pow_const 2
  have ht (j : Fin 2 → Fin N) :
      (∫⁻ x, ENNReal.ofReal ((spatialPatchCutoff ζ N (fun i => (j i : ℤ)) x) ^ 2) * g x ∂volume) =
      ∫⁻ x in Applications.cellI, (∑' n, w j n x) * g x ∂volume := by
    have hm : Measurable (fun x => ENNReal.ofReal
        ((spatialPatchCutoff ζ N (fun i => (j i : ℤ)) x) ^ 2) * g x) :=
      (((spatialPatchCutoff_smooth hζ N _).continuous.measurable.pow_const 2).ennreal_ofReal.mul hg)
    rw [lintegral_tiling_translate _ hm]
    change (∑' n : Fin 2 → ℤ, ∫⁻ x in Applications.cellI,
      w j n x * g (x + AVenhance.latticeShift n) ∂volume) = _
    simp only [hper']
    rw [← lintegral_tsum (f := fun n x => w j n x * g x)
      (fun n => ((hw j n).mul hg).aemeasurable)]
    simp only [ENNReal.tsum_mul_right, w]
  simp_rw [ht]
  have hmj (j : Fin 2 → Fin N) :
      Measurable (fun x => (∑' n, w j n x) * g x) := (Measurable.tsum (hw j)).mul hg
  rw [← lintegral_finsetSum Finset.univ (f := fun j x => (∑' n, w j n x) * g x)
    (fun j _ => hmj j)]
  apply lintegral_mono
  intro x
  change (∑ j : Fin 2 → Fin N, (∑' n, w j n x) * g x) ≤ g x
  rw [← Finset.sum_mul]
  exact (mul_le_mul_of_nonneg_right (spatialPatch_image_square_budget hζ N hN x) (show 0 ≤ g x from zero_le)).trans_eq
    (one_mul (g x))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The lowered physical-order seminorm sum is paid by the original positive molecular prices. -/

theorem positive_lowered_seminorm_budget
    (ν ρ E G C : ℝ) (hν : 0 < ν) (hρ : 0 < ρ) (hE : 0 < E)
    (hρE : ρ ≤ E) (hG : 0 ≤ G) (hC : 0 ≤ C) (K D Dγ : ℕ)
    (M : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ≥0∞)
    (S : ℕ → ℝ≥0∞)
    (hS : ∀ dout ∈ Finset.Icc 2 D,
      S dout ≤ ENNReal.ofReal (G * C * (∑ din ∈ Finset.Icc dout Dγ,
        ∑ I : DerivativeWord2 (din - 1), E⁻¹ ^ (din - dout) * (M din I).toReal))) :
    (∑ dout ∈ Finset.Icc 2 D, S dout *
      (ENNReal.ofReal (ν * ρ ^ (dout - 2)))⁻¹ *
        ENNReal.ofReal (((K + dout - 2).factorial : ℝ) / (K.factorial : ℝ))) ≤
      ENNReal.ofReal (G * C * D * (∑ din ∈ Finset.Icc 2 Dγ,
        ∑ I : DerivativeWord2 (din - 1), molecularRealPrice ν ρ K (din - 2) (M din I))) := by
  have hn (dout : ℕ) : 0 ≤ G * C * (∑ din ∈ Finset.Icc dout Dγ,
      ∑ I : DerivativeWord2 (din - 1), E⁻¹ ^ (din - dout) * (M din I).toReal) := by
    positivity
  apply le_trans (Finset.sum_le_sum (fun dout hd =>
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hS dout hd) zero_le) zero_le))
  simp_rw [← ENNReal.ofReal_inv_of_pos (mul_pos hν (pow_pos hρ _))]
  simp_rw [← ENNReal.ofReal_mul (hn _)]
  have he dout :
      (G * C * (∑ din ∈ Finset.Icc dout Dγ,
        ∑ I : DerivativeWord2 (din - 1), E⁻¹ ^ (din - dout) * (M din I).toReal) *
          (ν * ρ ^ (dout - 2))⁻¹) *
          (((K + dout - 2).factorial : ℝ) / (K.factorial : ℝ)) =
      G * C * (∑ din ∈ Finset.Icc dout Dγ,
        ∑ I : DerivativeWord2 (din - 1),
          E⁻¹ ^ (din - dout) * (M din I).toReal * (ν * ρ ^ (dout - 2))⁻¹ *
            (((K + dout - 2).factorial : ℝ) / (K.factorial : ℝ))) := by
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have hnn dout : 0 ≤ G * C * (∑ din ∈ Finset.Icc dout Dγ,
      ∑ I : DerivativeWord2 (din - 1),
        E⁻¹ ^ (din - dout) * (M din I).toReal * (ν * ρ ^ (dout - 2))⁻¹ *
          (((K + dout - 2).factorial : ℝ) / (K.factorial : ℝ))) := by positivity
  have he' (dout : ℕ) :
      ENNReal.ofReal ((G * C * (∑ din ∈ Finset.Icc dout Dγ,
        ∑ I : DerivativeWord2 (din - 1), E⁻¹ ^ (din - dout) * (M din I).toReal)) *
          (ν * ρ ^ (dout - 2))⁻¹) *
        ENNReal.ofReal (((K + dout - 2).factorial : ℝ) / (K.factorial : ℝ)) =
      ENNReal.ofReal (G * C * (∑ din ∈ Finset.Icc dout Dγ,
        ∑ I : DerivativeWord2 (din - 1),
          E⁻¹ ^ (din - dout) * (M din I).toReal * (ν * ρ ^ (dout - 2))⁻¹ *
            (((K + dout - 2).factorial : ℝ) / (K.factorial : ℝ)))) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg (hn dout)
      (inv_nonneg.mpr (mul_pos hν (pow_pos hρ (dout - 2))).le)), he dout]
  simp_rw [he']
  rw [← ENNReal.ofReal_sum_of_nonneg (fun dout _ => hnn dout)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left
    (positive_native_order_budget ν ρ E hν hρ hE hρE K D Dγ M) (mul_nonneg hG hC)
  convert hh using 1; ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.ChartTransport
namespace AVRegularity.CycleJointProofs

/-! A single positive constant controls all reserved sampled-flow derivatives. -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem preparation_flow_uniform_sample_jets
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (ρ : ℝ) (hρ : 0 < ρ)
    (hρE : ρ ≤ ocEpsilon q Λ (m - 1)) (r σ : ℝ)
    (hr : r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m)
    (n : ℕ) (hn : n ≤ Jchart + 1) (f : Vec 2 → V) (hf : ContDiff ℝ (n : ℕ) f)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ j, j ≤ n → ∀ y, ρ ^ j * ‖iteratedFDeriv ℝ j f y‖ ≤ B) :
    let C := 1 + ∑ p ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart p|
    ∀ j, j ≤ n → ∀ x,
      ρ ^ j * ‖iteratedFDeriv ℝ j (fun y => f (streamFlow φ hφ r y σ)) x‖ ≤
        (n.factorial : ℝ) * C ^ n * ((n + 1 : ℕ) * B) := by
  dsimp only
  let C := 1 + ∑ p ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart p|
  have hC : 1 ≤ C := one_le_jetConst _ _
  intro j hj x
  have hh := preparation_flow_sample_jet_bound hc ha ρ hρ hρE r σ hr hσ hage
    j (hj.trans hn) f (hf.of_le (by exact_mod_cast hj)) B
      (fun l hl => hb l (hl.trans hj)) x
  apply hh.trans
  have hfact : (j.factorial : ℝ) ≤ n.factorial := by
    exact_mod_cast Nat.factorial_le hj
  have hp : C ^ j ≤ C ^ n := pow_le_pow_right₀ hC hj
  have hn' : ((j + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.add_le_add_right hj 1
  change (j.factorial : ℝ) * C ^ j * ((j + 1 : ℕ) * B) ≤ _
  gcongr

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! The preparation flow's reserved coefficients are uniformly bounded at every radius below the slow scale. -/

theorem preparationFlowJetConstant_nonneg (Cchart : ℕ → ℝ) (j : ℕ) :
    0 ≤ preparationFlowJetConstant Cchart j := by
  unfold preparationFlowJetConstant
  split_ifs
  · exact add_nonneg zero_le_one (div_nonneg (le_max_right _ _) (by norm_num))
  · exact div_nonneg (mul_nonneg (le_max_right _ _) (Nat.cast_nonneg _)) (by norm_num)

theorem preparation_scaled_flow_budget {E ρ : ℝ} (hE : 0 < E) (hρ : 0 ≤ ρ) (hρE : ρ ≤ E)
    (Cchart : ℕ → ℝ) (j : ℕ) :
    ρ ^ (j - 1) * (preparationFlowJetConstant Cchart j * E⁻¹ ^ (j - 1)) ≤
      preparationFlowJetConstant Cchart j := by
  have hr : ρ * E⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact (div_le_one hE).mpr hρE
  have hp : (ρ * E⁻¹) ^ (j - 1) ≤ 1 :=
    pow_le_one₀ (mul_nonneg hρ (inv_nonneg.mpr hE.le)) hr
  calc
    _ = preparationFlowJetConstant Cchart j * (ρ * E⁻¹) ^ (j - 1) := by
      rw [mul_pow]
      ring
    _ ≤ preparationFlowJetConstant Cchart j * 1 :=
      mul_le_mul_of_nonneg_left hp (preparationFlowJetConstant_nonneg Cchart j)
    _ = _ := mul_one _

end AVRegularity.CycleJointProofs
end
end
