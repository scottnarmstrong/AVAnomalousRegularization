-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.PointwiseJetSupOn
public import AVRegularity.CycleJoint.MultiplicationTermArrayEnergy
public import AVRegularity.Statements.Intermediate.CoupledEnergy.AdmissibleOrders
import AVRegularity.CycleEvolution.StrongUniqueness
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal

section
section
@[expose] public noncomputable section
open Homogenization
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Zero extension outside active times preserves the pointwise mixed-jet bounds
on an output window. The active set itself need not be measurable. -/

theorem pointwiseJetSupOn_inactiveTimeZero_le (W S : Set ℝ) (active : ℝ → Prop)
    [DecidablePred active] (f : ℝ → Vec 2 → Vec 2 → Vec 2)
    (hs : ∀ t, active t → t ∈ S) (r q : ℕ) :
    pointwiseJetSupOn (W ×ˢ Set.univ) r q
        (fun t Y z => if active t then f t Y z else 0) ≤
      pointwiseJetSupOn ((S ∩ W) ×ˢ Set.univ) r q f := by
  unfold pointwiseJetSupOn
  apply iSup_le
  intro t
  apply iSup_le
  intro Y
  apply iSup_le
  intro hY
  by_cases ht : active t
  · simp only [ht, ite_true]
    exact le_iSup_of_le t (le_iSup_of_le Y
      (le_iSup_of_le ⟨⟨hs t ht, hY.1⟩, Set.mem_univ Y⟩ le_rfl))
  · apply iSup_le
    intro z
    have hz : (fun Y' => iteratedFDeriv ℝ q
        ((fun Y z => if active t then f t Y z else 0) Y') z) =
        (fun _ : Vec 2 => (0 : ContinuousMultilinearMap ℝ (fun _ : Fin q => Vec 2) (Vec 2))) := by
      funext Y'
      simp only [ht, ite_false, iteratedFDeriv_fun_zero, Pi.zero_apply]
    rw [hz]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply]
    rw [enorm_eq_nnnorm, nnnorm_zero, ENNReal.coe_zero]
    exact zero_le

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Native carrier jet sums are exactly finite ordered derivative sums. -/

variable {E : Type*} [AddCommMonoid E]

theorem nativeJet_order_sum (K : ℕ) (f : ∀ r : ℕ, DerivativeWord2 r → E) :
    (∑ a : JetIndex2 K, f a.1.val a.2) =
      ∑ r ∈ Finset.range (K + 1), ∑ A : DerivativeWord2 r, f r A := by
  rw [Fintype.sum_sigma]
  exact Fin.sum_univ_eq_sum_range (fun r => ∑ A : DerivativeWord2 r, f r A) (K + 1)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Direction and ordered-word multiplicities in the native Piola bound are explicit finite factors. -/

theorem native_transport_direction_sum (r : ℕ) (s : Finset ℕ) (G C : ℝ)
    (M : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ) :
    (∑ _a : Fin 2, ∑ _A : DerivativeWord2 r, G *
      (∑ d ∈ s, ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2, C * M d I)) =
      (2 : ℝ) ^ (r + 2) * G * C * (∑ d ∈ s, ∑ I : DerivativeWord2 (d - 1), M d I) := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [DerivativeWord2, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat]
  simp_rw [← Finset.mul_sum]
  rw [pow_add]
  ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Removing a rank discount costs only the fixed graph depth in the original mass energy. -/

variable {ι : Type*}

theorem rankMass_bounds (r : ι → ℕ) (H : ℕ) (hr : ∀ i, r i ≤ H)
    (L : ℝ) (hL : 1 ≤ L) (i : ι) :
    1 ≤ rankMass r L i ∧ rankMass r L i ≤ L ^ (2 * H) := by
  unfold rankMass
  rw [← pow_mul, Nat.mul_comm (r i) 2]
  constructor
  · exact one_le_pow₀ hL
  · exact pow_le_pow_right₀ hL (Nat.mul_le_mul_left 2 (hr i))

theorem originalMass_rank_inverse_bounds
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (r : ι → ℕ) (H : ℕ) (hr : ∀ i, r i ≤ H)
    (L : ℝ) (hL : 1 ≤ L) (i : ι) :
    (π i * rankMass r L i)⁻¹ ≤ (π i)⁻¹ ∧
      (π i)⁻¹ ≤ L ^ (2 * H) * (π i * rankMass r L i)⁻¹ := by
  have hb := rankMass_bounds r H hr L hL i
  have hp : 0 < rankMass r L i := zero_lt_one.trans_le hb.1
  have he : (π i)⁻¹ = rankMass r L i * (π i * rankMass r L i)⁻¹ := by
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
  constructor
  · apply (inv_le_inv₀ (mul_pos (hπ i) hp) (hπ i)).mpr
    exact (mul_one (π i)).symm.le.trans (mul_le_mul_of_nonneg_left hb.1 (hπ i).le)
  · rw [he]
    exact mul_le_mul_of_nonneg_right hb.2 (inv_nonneg.mpr (mul_pos (hπ i) hp).le)

variable [Fintype ι]

theorem originalMass_rank_energy_bounds
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (r : ι → ℕ) (H : ℕ) (hr : ∀ i, r i ≤ H)
    (L : ℝ) (hL : 1 ≤ L) (energy : ι → ℝ≥0∞) :
    (∑ i, ENNReal.ofReal ((π i * rankMass r L i)⁻¹) * energy i) ≤
      (∑ i, ENNReal.ofReal ((π i)⁻¹) * energy i) ∧
    (∑ i, ENNReal.ofReal ((π i)⁻¹) * energy i) ≤
      ENNReal.ofReal (L ^ (2 * H)) *
        (∑ i, ENNReal.ofReal ((π i * rankMass r L i)⁻¹) * energy i) := by
  constructor
  · exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (originalMass_rank_inverse_bounds π hπ r H hr L hL i).1) zero_le)
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have he := ENNReal.ofReal_le_ofReal
      (originalMass_rank_inverse_bounds π hπ r H hr L hL i).2
    rw [ENNReal.ofReal_mul (pow_nonneg (zero_le_one.trans hL) _)] at he
    exact (mul_le_mul_of_nonneg_right he zero_le).trans_eq (mul_assoc _ _ _)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! Full-lattice indexing of two-dimensional torus patch images. -/

def periodImageLatticeEquiv (N : ℕ) (hN : 0 < N) :
    ((Fin 2 → Fin N) × (Fin 2 → ℤ)) ≃ (Fin 2 → ℤ) where
  toFun p i := periodImageIndexEquiv N hN (p.1 i, p.2 i)
  invFun k := (fun i => ((periodImageIndexEquiv N hN).symm (k i)).1,
    fun i => ((periodImageIndexEquiv N hN).symm (k i)).2)
  left_inv p := by
    apply Prod.ext
    · funext i
      exact congrArg Prod.fst ((periodImageIndexEquiv N hN).left_inv (p.1 i, p.2 i))
    · funext i
      exact congrArg Prod.snd ((periodImageIndexEquiv N hN).left_inv (p.1 i, p.2 i))
  right_inv k := by
    funext i
    exact (periodImageIndexEquiv N hN).right_inv (k i)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open MeasureTheory Homogenization
namespace AVRegularity.CycleJointProofs

/-! Periodic representatives equal almost everywhere on one cell are equal on the covering plane. -/

theorem periodic_ae_eq_global {E : Type*} (f g : Vec 2 → E)
    (hf : AVenhance.IsZ2Periodic f) (hg : AVenhance.IsZ2Periodic g)
    (he : f =ᵐ[volume.restrict AVenhance.unitCube] g) : f =ᵐ[volume] g := by
  have hc : f =ᵐ[volume.restrict Applications.cellI] g := by
    rw [Measure.restrict_congr_set Applications.cellI_ae_eq_unitCube]
    exact he
  have ht (n : Fin 2 → ℤ) : f =ᵐ[volume.restrict (Applications.cellAt n)] g := by
    have hshift : AVenhance.latticeShift (-n) = -AVenhance.latticeShift n := by
      funext i
      simp [AVenhance.latticeShift]
    have hpre : (fun x : Vec 2 => x + AVenhance.latticeShift (-n)) ⁻¹' Applications.cellI =
        Applications.cellAt n := by
      ext x
      simp [Applications.cellAt, hshift, sub_eq_add_neg]
    have hm : MeasurePreserving (fun x : Vec 2 => x + AVenhance.latticeShift (-n))
        (volume.restrict (Applications.cellAt n)) (volume.restrict Applications.cellI) := by
      simpa only [hpre] using
        (measurePreserving_add_right (volume : Measure (Vec 2)) (AVenhance.latticeShift (-n))).restrict_preimage
          Applications.measurableSet_cellI
    filter_upwards [hm.quasiMeasurePreserving.ae hc] with x hx
    simpa only [hf (-n) x, hg (-n) x] using hx
  have hall : ∀ᵐ x ∂(volume : Measure (Vec 2)), ∀ n : Fin 2 → ℤ,
      x ∈ Applications.cellAt n → f x = g x := ae_all_iff.mpr (fun n =>
    (ae_restrict_iff' (Applications.measurableSet_cellAt n)).mp (ht n))
  filter_upwards [hall] with x hx
  exact hx (fun i => ⌊x i⌋) (Applications.mem_cellAt_floor x)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Compact localization of periodic cell-L2 data produces genuine covering-plane L2 data. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem periodic_memLp_cellAt (f : Vec 2 → E)
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube))
    (hp : AVenhance.IsZ2Periodic f) (n : Fin 2 → ℤ) :
    MemLp f 2 (volume.restrict (Applications.cellAt n)) := by
  have hc : MemLp f 2 (volume.restrict Applications.cellI) := by
    rw [Measure.restrict_congr_set Applications.cellI_ae_eq_unitCube]
    exact hf
  have hshift : AVenhance.latticeShift (-n) = -AVenhance.latticeShift n := by
    funext i
    simp [AVenhance.latticeShift]
  have hpre : (fun x : Vec 2 => x + AVenhance.latticeShift (-n)) ⁻¹' Applications.cellI =
      Applications.cellAt n := by
    ext x
    simp [Applications.cellAt, hshift, sub_eq_add_neg]
  have hm : MeasurePreserving (fun x : Vec 2 => x + AVenhance.latticeShift (-n))
      (volume.restrict (Applications.cellAt n)) (volume.restrict Applications.cellI) := by
    simpa only [hpre] using
      (measurePreserving_add_right (volume : Measure (Vec 2)) (AVenhance.latticeShift (-n))).restrict_preimage
        Applications.measurableSet_cellI
  exact MemLp.ae_eq (Filter.Eventually.of_forall (fun x => hp (-n) x))
    (hc.comp_measurePreserving hm)

theorem periodic_bounded_supported_multiplier_memLp (f : Vec 2 → E)
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube)) (hp : AVenhance.IsZ2Periodic f)
    (c : Vec 2 → ℝ) (hcm : AEStronglyMeasurable c volume) (B R : ℝ)
    (hcB : ∀ x, ‖c x‖ ≤ B) (hcR : ∀ x, c x ≠ 0 → ‖x‖ ≤ R) :
    MemLp (fun x => c x • f x) 2 volume := by
  classical
  obtain ⟨M, hM⟩ := exists_nat_ge (R + 1)
  let g : Vec 2 → E := fun x => ∑ n ∈ Applications.latBox M, (Applications.cellAt n).indicator f x
  have hg : MemLp g 2 volume := memLp_finsetSum _ (fun n _ =>
    (memLp_indicator_iff_restrict (Applications.measurableSet_cellAt n)).mpr
      (periodic_memLp_cellAt f hf hp n))
  have hct : MemLp c ⊤ volume := memLp_top_of_bound hcm B (Filter.Eventually.of_forall hcB)
  have he : (fun x => c x • g x) = (fun x => c x • f x) := by
    funext x
    by_cases hz : c x = 0
    · simp [hz]
    · have hx := Applications.supBall_subset_iUnion_cellAt hM (hcR x hz)
      obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hn, hxn⟩ := Set.mem_iUnion.mp hxn
      have hgx : g x = f x := by
        dsimp only [g]
        rw [Finset.sum_eq_single n]
        · exact Set.indicator_of_mem hxn f
        · intro j _ hne
          apply Set.indicator_of_notMem
          intro hxj
          exact Set.disjoint_left.mp (Applications.cellAt_disjoint hne) hxj hxn
        · intro hnot
          exact (hnot hn).elim
      rw [hgx]
  rw [← he]
  exact hct.smul hg

end AVRegularity.CycleJointProofs
end
end

section
public section
namespace AVRegularity.CycleJointProofs

/-! Positive time scaling preserves closed subwindow inclusion. -/

theorem positive_time_scaled_interval_inclusion (a b c d scale : ℝ) (hs : 0 < scale)
    (hsub : Set.Icc a b ⊆ Set.Icc c d) :
    Set.Icc (a / scale) (b / scale) ⊆ Set.Icc (c / scale) (d / scale) := by
  intro t ht
  have hh := hsub ⟨(div_le_iff₀ hs).mp ht.1, (le_div_iff₀ hs).mp ht.2⟩
  exact ⟨(div_le_iff₀ hs).mpr hh.1, (le_div_iff₀ hs).mpr hh.2⟩

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Positive time normalization gives the exact nonnegative integral price. -/

theorem lintegral_comp_inv_mul_restrict_Icc (ν a b : ℝ) (hν : 0 < ν) (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in Set.Icc (ν * a) (ν * b), f (ν⁻¹ * t)) =
      ENNReal.ofReal ν * ∫⁻ t in Set.Icc a b, f t := by
  have hf : MeasurableEmbedding (fun t : ℝ => ν⁻¹ * t) :=
    (Homeomorph.mulLeft₀ ν⁻¹ (inv_ne_zero hν.ne')).isClosedEmbedding.measurableEmbedding
  rw [← hf.lintegral_map f, map_volume_restrict_Icc_inv_mul ν a b hν,
    lintegral_smul_measure]
  simp only [smul_eq_mul]

/-! Positive time normalization preserves the integrable weak identity, including its endpoint convention. -/

/-- Scaling an integrable time density preserves the half-open interval of the weak identity. -/
theorem integrableOn_comp_inv_mul_Ioc {ν a b : ℝ} (hν : 0 < ν)
    {f : ℝ → ℝ} (hf : IntegrableOn f (Set.Ioc a b)) :
    IntegrableOn (fun t => ν⁻¹ * f (ν⁻¹ * t)) (Set.Ioc (ν * a) (ν * b)) := by
  have hi : IntegrableOn f (Set.Icc a b) :=
    (integrableOn_Icc_iff_integrableOn_Ioc (f := f)).mpr hf
  have hm := memLp_comp_inv_mul_restrict_Icc hν (memLp_one_iff_integrable.mpr hi)
  have hn : IntegrableOn (fun t => f (ν⁻¹ * t)) (Set.Icc (ν * a) (ν * b)) :=
    memLp_one_iff_integrable.mp hm
  exact IntegrableOn.mono_set (hn.const_mul ν⁻¹) Set.Ioc_subset_Icc_self

/-- The inverse diffusion-time factor cancels the time Jacobian in the exact weak integral. -/
theorem setIntegral_inv_mul_comp_inv_mul_Ioc {ν a b : ℝ}
    (hν : 0 < ν) (hab : a ≤ b) (f : ℝ → ℝ) :
    (∫ t in Set.Ioc (ν * a) (ν * b), ν⁻¹ * f (ν⁻¹ * t)) =
      ∫ t in Set.Ioc a b, f t := by
  rw [← intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_left hab hν.le),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left f (inv_ne_zero hν.ne')]
  simp only [inv_inv, inv_mul_cancel_left₀ hν.ne', smul_eq_mul]
  exact intervalIntegral.integral_of_le hab

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! Positive diffusion-time scaling preserves the prescribed closed solution window. -/

theorem positiveTimeNormalization_mem_Icc {ν a b t : ℝ} (hν : 0 < ν)
    (ht : t ∈ Set.Icc (ν * a) (ν * b)) : ν⁻¹ * t ∈ Set.Icc a b := by
  rw [show ν⁻¹ * t = t / ν by rw [div_eq_mul_inv, mul_comm]]
  exact ⟨(le_div_iff₀ hν).mpr (by simpa only [mul_comm] using ht.1),
    (div_le_iff₀ hν).mpr (by simpa only [mul_comm] using ht.2)⟩

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! One finite chart reserve bounds all scalar gradient response prices before selecting the component family. -/

def scalarResponseGradientReservePrice (Kmax : ℕ) (L : ℝ) (Cw : ℕ → ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range (N + 1), scalarResponseGradientPrice Kmax L Cw k

theorem scalarResponseGradientPrice_le_reserve (Kmax : ℕ) (L : ℝ) (Cw : ℕ → ℝ)
    (N k : ℕ) (hk : k ≤ N) :
    scalarResponseGradientPrice Kmax L Cw k ≤ scalarResponseGradientReservePrice Kmax L Cw N :=
  Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

theorem scalarResponseGradientReservePrice_ne_top (Kmax : ℕ) (L : ℝ) (Cw : ℕ → ℝ) (N : ℕ) :
    scalarResponseGradientReservePrice Kmax L Cw N ≠ ⊤ := by
  apply ENNReal.sum_ne_top.mpr
  intro k _
  exact scalarResponseGradientPrice_ne_top Kmax L Cw k

/-! Finite chronological response energies retain the moment cost of every insertion. -/

def shiftedResponseEnergyBudget (a b : ℕ → ℝ≥0∞) (p : ℕ) : ℕ → ℕ → ℕ → ℝ≥0∞
  | _, 0, 0 => 1
  | n, j + 1, 0 => a n * shiftedResponseEnergyBudget a b p (n + p) j 0
  | n, 0, h + 1 => b n * shiftedResponseEnergyBudget a b p (n + p) 0 h
  | n, j + 1, h + 1 => 2 *
      (a n * shiftedResponseEnergyBudget a b p (n + p) j (h + 1) +
       b n * shiftedResponseEnergyBudget a b p (n + p) (j + 1) h)
termination_by _n j h => j + h

/-! The original-mass rank discount supplies actual source-feedback absorption before the family is chosen. -/

/-- The explicit rank scale `1 + 64 C (√(2^D) B)²` (explicit, so that
the prices built from it are uniform over the source strengths of a family). -/
def sourceFeedbackRankScale (C B : ℝ) (D : ℕ) : ℝ :=
  1 + 64 * C * (Real.sqrt ((2 : ℝ) ^ D) * B) ^ 2

theorem sourceFeedbackRankScale_mono (C : ℝ) (hC : 0 ≤ C) (D : ℕ) {B B' : ℝ} (hB : 0 ≤ B)
    (hBB' : B ≤ B') : sourceFeedbackRankScale C B D ≤ sourceFeedbackRankScale C B' D := by
  unfold sourceFeedbackRankScale
  have hs : 0 ≤ Real.sqrt ((2 : ℝ) ^ D) := Real.sqrt_nonneg _
  have h1 : Real.sqrt ((2 : ℝ) ^ D) * B ≤ Real.sqrt ((2 : ℝ) ^ D) * B' :=
    mul_le_mul_of_nonneg_left hBB' hs
  have h2 := pow_le_pow_left₀ (mul_nonneg hs hB) h1 2
  have h3 : 0 ≤ 64 * C := by linarith
  linarith [mul_le_mul_of_nonneg_left h2 h3]

theorem sourceFeedbackRankScale_spec (C B : ℝ) (hC : 0 ≤ C) (D : ℕ) :
    1 ≤ sourceFeedbackRankScale C B D ∧
      ENNReal.ofReal C * (32 * ENNReal.ofReal ((Real.sqrt ((2 : ℝ) ^ D) *
        (B / sourceFeedbackRankScale C B D)) ^ 2)) ≤ (1 / 2 : ℝ≥0∞) := by
  obtain ⟨hL, hs⟩ := real_source_feedback_discount_explicit C (Real.sqrt ((2 : ℝ) ^ D) * B) hC
  set L := sourceFeedbackRankScale C B D with hLdef
  refine ⟨hL, ?_⟩
  have he : ENNReal.ofReal C *
      (32 * ENNReal.ofReal ((Real.sqrt ((2 : ℝ) ^ D) * (B / L)) ^ 2)) =
        ENNReal.ofReal (32 * C * ((Real.sqrt ((2 : ℝ) ^ D) * B) / L) ^ 2) := by
    rw [show (32 : ℝ≥0∞) = ENNReal.ofReal (32 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 32),
      ← ENNReal.ofReal_mul hC]
    congr 1
    rw [mul_div_assoc]
    ring
  rw [he]
  calc
    _ ≤ ENNReal.ofReal (1 / 2 : ℝ) := ENNReal.ofReal_le_ofReal hs
    _ = _ := by rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]; norm_num

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! Finite source-path majorants have component-independent row and column budgets. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positive_source_powers_linear_theta (C Θ : ℝ) (hΘ₀ : 0 ≤ Θ) (hΘ₁ : Θ ≤ 1)
    (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (c : ℕ → ℝ) (hc : ∀ n ∈ s, 0 ≤ c n)
    (hC : 0 ≤ C) :
    ∑ n ∈ s, c n * (C * Θ) ^ n ≤ Θ * ∑ n ∈ s, c n * C ^ n := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hp : Θ ^ n ≤ Θ := by
    calc
      Θ ^ n ≤ Θ ^ 1 := pow_le_pow_of_le_one hΘ₀ hΘ₁ (hs n hn)
      _ = Θ := pow_one _
  rw [mul_pow]
  calc
    c n * (C ^ n * Θ ^ n) ≤ c n * (C ^ n * Θ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (pow_nonneg hC n)) (hc n hn)
    _ = Θ * (c n * C ^ n) := by ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter
open scoped Topology
namespace AVRegularity.CycleJointProofs

/-! Concrete smooth compact spatial cutoffs exhausting the plane. -/

def spatialApproximationBump : ContDiffBump (0 : Vec 2) :=
  ⟨1, 2, by norm_num, by norm_num⟩

def spatialApproximationScale (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

def spatialApproximationEquiv (n : ℕ) : Vec 2 ≃L[ℝ] Vec 2 :=
  Units.mk0 (spatialApproximationScale n) (by unfold spatialApproximationScale; positivity) •
    ContinuousLinearEquiv.refl ℝ (Vec 2)

def spatialApproximationCutoff (n : ℕ) : Vec 2 → ℝ :=
  fun x => spatialApproximationBump (spatialApproximationEquiv n x)

theorem spatialApproximationScale_pos (n : ℕ) : 0 < spatialApproximationScale n := by
  unfold spatialApproximationScale
  positivity

theorem spatialApproximationScale_le_one (n : ℕ) : spatialApproximationScale n ≤ 1 := by
  unfold spatialApproximationScale
  apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
  exact le_add_of_nonneg_left (Nat.cast_nonneg n)

theorem spatialApproximationScale_tendsto :
    Tendsto spatialApproximationScale atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem spatialApproximationCutoff_smooth (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (spatialApproximationCutoff n) :=
  spatialApproximationBump.contDiff.comp (spatialApproximationEquiv n).contDiff

theorem spatialApproximationCutoff_compact (n : ℕ) :
    HasCompactSupport (spatialApproximationCutoff n) :=
  spatialApproximationBump.hasCompactSupport.comp_homeomorph
    (spatialApproximationEquiv n).toHomeomorph

theorem spatialApproximationCutoff_bounds (n : ℕ) (x : Vec 2) :
    0 ≤ spatialApproximationCutoff n x ∧ spatialApproximationCutoff n x ≤ 1 :=
  ⟨spatialApproximationBump.nonneg, spatialApproximationBump.le_one⟩

theorem spatialApproximationCutoff_tendsto (x : Vec 2) :
    Tendsto (fun n => spatialApproximationCutoff n x) atTop (𝓝 1) := by
  have hp : Tendsto (fun n => spatialApproximationEquiv n x) atTop (𝓝 0) := by
    change Tendsto (fun n => spatialApproximationScale n • x) atTop (𝓝 0)
    simpa only [zero_smul] using spatialApproximationScale_tendsto.smul_const x
  have hh := spatialApproximationBump.continuous.continuousAt.tendsto.comp hp
  have h1 : spatialApproximationBump (0 : Vec 2) = 1 :=
    spatialApproximationBump.one_of_mem_closedBall
      (Metric.mem_closedBall_self spatialApproximationBump.rIn_pos.le)
  simpa only [Function.comp_def, spatialApproximationCutoff, h1] using hh

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Strong Hilbert time curves have finite Lp norms on their compact time window. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem strongTime_memLp {a b : ℝ} (hab : a ≤ b) {z dz : ℝ → H}
    (h : CycleEvolution.StrongTimeRegularity a b z dz) (p : ℝ≥0∞) :
    MemLp z p (volume.restrict (Icc a b)) := by
  have hc : ContinuousOn z (Icc a b) := by
    simpa only [uIcc_of_le hab] using h.ac.continuousOn
  obtain ⟨C, hC⟩ := h.ac.exists_bound
  apply MemLp.of_bound (hc.aestronglyMeasurable_of_isCompact isCompact_Icc measurableSet_Icc) C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hC t (by simpa only [uIcc_of_le hab] using ht)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! A fixed finite jet reserve gives a uniform Leibniz constant. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem uniform_product_jet_bound (f g : E → ℝ) (x : E) (n : ℕ)
    (hf : ContDiff ℝ (n : ℕ) f) (hg : ContDiff ℝ (n : ℕ) g)
    (A B : ℝ)
    (hfj : ∀ j ≤ n, ‖iteratedFDeriv ℝ j f x‖ ≤ A)
    (hgj : ∀ j ≤ n, ‖iteratedFDeriv ℝ j g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤
      (n + 1 : ℕ) * 2 ^ n * A * B := by
  have hA : 0 ≤ A := (norm_nonneg _).trans (hfj 0 (Nat.zero_le _))
  have hB : 0 ≤ B := (norm_nonneg _).trans (hgj 0 (Nat.zero_le _))
  have hh := finite_product_weighted_jet_bound f g x n hf hg 1 zero_le_one
    (fun _ => A) (fun _ => B)
    (fun j hj => by simpa only [one_pow, one_mul] using hfj j hj)
    (fun j hj => by simpa only [one_pow, one_mul] using hgj j hj)
  simp only [one_pow, one_mul] at hh
  apply hh.trans
  calc
    _ ≤ ∑ _j ∈ Finset.range (n + 1), (2 : ℝ) ^ n * A * B := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ hB
      apply mul_le_mul_of_nonneg_right _ hA
      exact_mod_cast Nat.choose_le_two_pow n j
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end AVRegularity.CycleJointProofs
end
end

section
public section
namespace AVRegularity.CycleJointProofs

/-! One finite scalar reserve absorbs every adjoint weight price up to the
 requested moment order. It may be chosen again when that order changes. -/

theorem exists_uniform_scalar_square_reserve (Cw : ℕ → ℝ) (N : ℕ) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ k ≤ N, Real.exp (18 * Cw k) / L ^ 2 ≤ 1 / 16 := by
  let A := ∑ k ∈ Finset.range (N + 1), Real.exp (18 * Cw k)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun k _ => (Real.exp_pos _).le)
  obtain ⟨L, hL, hbound⟩ := exists_scalar_square_reserve A hA
  refine ⟨L, hL, ?_⟩
  intro k hk
  have hkA : Real.exp (18 * Cw k) ≤ A :=
    Finset.single_le_sum (f := fun j => Real.exp (18 * Cw j))
      (fun j _ => (Real.exp_pos _).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  exact (div_le_div_of_nonneg_right hkA (sq_nonneg L)).trans hbound

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! Uniform finite Leibniz constants with the molecular radius left in every derivative term. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem uniform_product_weighted_jet_bound (f g : E → ℝ) (x : E) (n : ℕ)
    (hf : ContDiff ℝ (n : ℕ) f) (hg : ContDiff ℝ (n : ℕ) g)
    (ρ A B : ℝ) (hρ : 0 ≤ ρ)
    (hfj : ∀ j ≤ n, ρ ^ j * ‖iteratedFDeriv ℝ j f x‖ ≤ A)
    (hgj : ∀ j ≤ n, ρ ^ j * ‖iteratedFDeriv ℝ j g x‖ ≤ B) :
    ρ ^ n * ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤
      (n + 1 : ℕ) * 2 ^ n * A * B := by
  have hA : 0 ≤ A := (mul_nonneg (pow_nonneg hρ _) (norm_nonneg _)).trans (hfj 0 (Nat.zero_le _))
  have hB : 0 ≤ B := (mul_nonneg (pow_nonneg hρ _) (norm_nonneg _)).trans (hgj 0 (Nat.zero_le _))
  have hh := finite_product_weighted_jet_bound f g x n hf hg ρ hρ
    (fun _ => A) (fun _ => B) hfj hgj
  apply hh.trans
  calc
    _ ≤ ∑ _j ∈ Finset.range (n + 1), (2 : ℝ) ^ n * A * B := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right _ hB
      apply mul_le_mul_of_nonneg_right _ hA
      exact_mod_cast Nat.choose_le_two_pow n j
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The tensor word price of every admissible coupling is bounded by the fixed maximal source order. -/

variable {ι : Type*}

theorem admissibleDerivativeWord_card_le (K : ι → ℕ) (D : ℕ) (i u : ι)
    (d : admissibleOrders K D i u) :
    Fintype.card (DerivativeWord2 (d.1 - 1)) ≤ 2 ^ D := by
  have hd : d.1 ≤ D := (Finset.mem_Icc.mp (Finset.mem_filter.mp d.property).1).2
  simp only [DerivativeWord2, DerivativeWord, Fintype.card_fun, Fintype.card_fin]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) ((Nat.sub_le d.1 1).trans hd)

theorem admissibleDerivativeWord_sqrt_card_le (K : ι → ℕ) (D : ℕ) (i u : ι)
    (d : admissibleOrders K D i u) :
    Real.sqrt (Fintype.card (DerivativeWord2 (d.1 - 1)) : ℝ) ≤ Real.sqrt ((2 : ℝ) ^ D) := by
  apply Real.sqrt_le_sqrt
  exact_mod_cast admissibleDerivativeWord_card_le K D i u d

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleJointProofs

/-! Finite source and derivative-order flux sums commute with actual spatial weak pairings. -/

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem couplingFamily_pairing_integral (K : ι → ℕ) (D : ℕ) (i : ι)
    (μ : Measure (Vec 2))
    (B : ∀ i', admissibleOrders K D i i' → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (φ : Vec 2 → E) (k : Fin 2)
    (hi : ∀ i' d, Integrable (fun x => inner ℝ (B i' d x k) (φ x)) μ) :
    Integrable (fun x => inner ℝ ((∑ i', ∑ d, B i' d x) k) (φ x)) μ ∧
    (∫ x, inner ℝ ((∑ i', ∑ d, B i' d x) k) (φ x) ∂μ) =
      ∑ i', ∑ d, ∫ x, inner ℝ (B i' d x k) (φ x) ∂μ := by
  have he : (fun x => inner ℝ ((∑ i', ∑ d, B i' d x) k) (φ x)) =
      fun x => ∑ i', ∑ d, inner ℝ (B i' d x k) (φ x) := by
    funext x
    simp only [WithLp.ofLp_sum, Finset.sum_apply, sum_inner]
  have his (i' : ι) : Integrable (fun x => ∑ d, inner ℝ (B i' d x k) (φ x)) μ :=
    integrable_finsetSum Finset.univ (fun d _ => hi i' d)
  refine ⟨he.symm ▸ integrable_finsetSum Finset.univ (fun i' _ => his i'), ?_⟩
  rw [he, integral_finsetSum Finset.univ (fun i' _ => his i')]
  exact Finset.sum_congr rfl (fun i' _ => integral_finsetSum Finset.univ (fun d _ => hi i' d))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleJointProofs

/-! Strong time regularity assembles in finite Hilbert products. -/

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem strongTime_finset_sum {ι : Type*} {a b : ℝ} (S : Finset ι)
    (z dz : ι → ℝ → H)
    (h : ∀ i ∈ S, CycleEvolution.StrongTimeRegularity a b (z i) (dz i)) :
    CycleEvolution.StrongTimeRegularity a b (fun t => ∑ i ∈ S, z i t)
      (fun t => ∑ i ∈ S, dz i t) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨?_, Filter.Eventually.of_forall (fun t => hasDerivAt_const t 0)⟩
    simp only [AbsolutelyContinuousOnInterval, dist_self, Finset.sum_const_zero]
    exact tendsto_const_nhds
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i S)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem strongTime_piLp {ι : Type*} [Fintype ι] {a b : ℝ}
    (z dz : ι → ℝ → H)
    (h : ∀ i, CycleEvolution.StrongTimeRegularity a b (z i) (dz i)) :
    CycleEvolution.StrongTimeRegularity a b
      (fun t => WithLp.toLp 2 (fun i => z i t))
      (fun t => WithLp.toLp 2 (fun i => dz i t)) := by
  classical
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => H)).symm.toContinuousLinearMap
  let L := fun i => J.comp (ContinuousLinearMap.single ℝ (fun _ : ι => H) i)
  have hp := strongTime_finset_sum Finset.univ
    (fun i t => L i (z i t)) (fun i t => L i (dz i t))
    (fun i _ => (h i).map (L i))
  have he (f : ι → H) : (∑ i, L i (f i)) = WithLp.toLp 2 f := by
    change (∑ i, J ((ContinuousLinearMap.single ℝ (fun _ : ι => H) i) (f i))) = _
    rw [← map_sum]
    change J (∑ i, (ContinuousLinearMap.single ℝ (fun _ : ι => H) i) (f i)) = J f
    congr 1
    funext j
    simp only [ContinuousLinearMap.single_apply, Finset.univ_sum_single]
  simpa only [he] using hp
end

/-! Finite source and direction assembly preserves the actual spacetime readout and image price. -/

section
variable {X N J : Type*} [MeasurableSpace X] [Countable N]

theorem finite_pairing_spacetime_readout (μ : Measure X) (S : Finset J)
    (G : J → N → X → ℝ) (P : J → X → ℝ)
    (hi : ∀ j ∈ S, ∀ n, Integrable (G j n) μ)
    (hs : ∀ j ∈ S, Summable (fun n => ∫ t, ‖G j n t‖ ∂μ))
    (hP : ∀ j ∈ S, Integrable (P j) μ)
    (he : ∀ j ∈ S, (∑' n, ∫ t, G j n t ∂μ) = ∫ t, P j t ∂μ) :
    (∀ n, Integrable (fun t => ∑ j ∈ S, G j n t) μ) ∧
    Summable (fun n => ∫ t, ‖∑ j ∈ S, G j n t‖ ∂μ) ∧
    Integrable (fun t => ∑ j ∈ S, P j t) μ ∧
    (∑' n, ∫ t, ∑ j ∈ S, G j n t ∂μ) = ∫ t, ∑ j ∈ S, P j t ∂μ := by
  have hsj : ∀ j ∈ S, Summable (fun n => ∫ t, G j n t ∂μ) := by
    intro j hj
    exact (hasSum_integral_of_summable_integral_norm (hi j hj) (hs j hj)).summable
  refine ⟨fun n => integrable_finsetSum S (fun j hj => hi j hj n),
    finite_pairing_time_summable μ S G hi hs, integrable_finsetSum S hP, ?_⟩
  calc
    _ = ∑' n, ∑ j ∈ S, ∫ t, G j n t ∂μ :=
      tsum_congr (fun n => integral_finsetSum S (fun j hj => hi j hj n))
    _ = ∑ j ∈ S, ∑' n, ∫ t, G j n t ∂μ := Summable.tsum_finsetSum hsj
    _ = ∑ j ∈ S, ∫ t, P j t ∂μ := Finset.sum_congr rfl he
    _ = _ := (integral_finsetSum S hP).symm
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped Matrix
namespace AVRegularity.CycleJointProofs

/-! Matrix composition and adjoint pairings for Hilbert-valued material gradients. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hilbertMatrixAction_mul (M N : Matrix (Fin 2) (Fin 2) ℝ) (G : Fin 2 → E) :
    hilbertMatrixAction (M * N) G = hilbertMatrixAction M (hilbertMatrixAction N G) := by
  funext k
  apply ext_inner_left ℝ
  intro e
  simp_rw [hilbertMatrixAction_inner]
  rw [Matrix.mulVec_mulVec]

theorem hilbertMatrixAction_one (G : Fin 2 → E) :
    hilbertMatrixAction (1 : Matrix (Fin 2) (Fin 2) ℝ) G = G := by
  funext k
  simp only [hilbertMatrixAction, Matrix.one_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem hilbertMatrixAction_pair (M : Matrix (Fin 2) (Fin 2) ℝ) (G H : Fin 2 → E) :
    (∑ k : Fin 2, inner ℝ (hilbertMatrixAction M G k) (H k)) =
      ∑ k : Fin 2, inner ℝ (G k) (hilbertMatrixAction Mᵀ H k) := by
  simp only [hilbertMatrixAction, Matrix.transpose_apply, Fin.sum_univ_two,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  ring

theorem hilbertMatrixAction_metric_pair (J : Matrix (Fin 2) (Fin 2) ℝ)
    (hJ : IsUnit J.det) (G H : Fin 2 → E) :
    (∑ k : Fin 2, inner ℝ (hilbertMatrixAction Jᵀ G k)
      (hilbertMatrixAction (J⁻¹ * (J⁻¹)ᵀ) (hilbertMatrixAction Jᵀ H) k)) =
      ∑ k : Fin 2, inner ℝ (G k) (H k) := by
  rw [hilbertMatrixAction_pair, Matrix.transpose_transpose,
    ← hilbertMatrixAction_mul, ← hilbertMatrixAction_mul]
  have hm : J * (J⁻¹ * (J⁻¹)ᵀ) * Jᵀ = 1 := by
    rw [← Matrix.mul_assoc J J⁻¹, Matrix.mul_nonsing_inv J hJ, Matrix.one_mul,
      ← Matrix.transpose_mul, Matrix.mul_nonsing_inv J hJ, Matrix.transpose_one]
  rw [hm, hilbertMatrixAction_one]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! Source powers obey the exact inverse-mass row and column bounds. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem massMatrix_pow_row_sum (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (A : Matrix ι ι ℝ) (hA : ∀ v u, 0 ≤ A v u) (θ : ℝ) (hθ : 0 ≤ θ)
    (hrow : ∀ v, ∑ u, Real.sqrt (π u / π v) * A v u ≤ θ) (n : ℕ) (v : ι) :
    ∑ u, Real.sqrt (π u / π v) * (A ^ n) v u ≤ θ ^ n := by
  have hb : ∀ v u, 0 ≤ massConjugatedMatrix π A v u := fun v u =>
    mul_nonneg (Real.sqrt_nonneg _) (hA v u)
  have hs := positiveMatrix_pow_row_sum (massConjugatedMatrix π A) hb θ hθ hrow n v
  rw [← massConjugatedMatrix_pow π hπ] at hs
  exact hs

theorem massMatrix_pow_col_sum (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (A : Matrix ι ι ℝ) (hA : ∀ v u, 0 ≤ A v u) (θ : ℝ) (hθ : 0 ≤ θ)
    (hcol : ∀ u, ∑ v, Real.sqrt (π u / π v) * A v u ≤ θ) (n : ℕ) (u : ι) :
    ∑ v, Real.sqrt (π u / π v) * (A ^ n) v u ≤ θ ^ n := by
  have hb : ∀ v u, 0 ≤ massConjugatedMatrix π A v u := fun v u =>
    mul_nonneg (Real.sqrt_nonneg _) (hA v u)
  have hs := positiveMatrix_pow_col_sum (massConjugatedMatrix π A) hb θ hθ hcol n u
  rw [← massConjugatedMatrix_pow π hπ] at hs
  exact hs

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! Actual native response insertions satisfy a fixed-point identity with the zeroth response retained explicitly. -/

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem finiteResponse_native_equation (M S : Module.End ℝ E) (f : E) (j n : ℕ) :
    finiteResponse 1 M S f j n =
      (if j = 0 ∧ n = 0 then f else 0) +
      (if j = 0 then 0 else M (finiteResponse 1 M S f (j - 1) n)) +
      (if n = 0 then 0 else S (finiteResponse 1 M S f j (n - 1))) := by
  cases j <;> cases n <;> simp [finiteResponse]

theorem finiteResponse_native_fixedPoint_residual (M S : Module.End ℝ E) (f : E) (J H : ℕ) :
    let U := finiteResponse 1 M S f
    let V := ∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.range (H + 1), U j n
    V - M V - S V = f - M (∑ n ∈ Finset.range (H + 1), U J n) -
      S (∑ j ∈ Finset.range (J + 1), U j H) := by
  dsimp only
  let U := finiteResponse 1 M S f
  have hbase : (∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.range (H + 1),
      if j = 0 ∧ n = 0 then f else 0) = f := by
    simp [ite_and]
  have hm : (∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.range (H + 1),
      if j = 0 then 0 else M (U (j - 1) n)) =
      M (∑ j ∈ Finset.range J, ∑ n ∈ Finset.range (H + 1), U j n) := by
    simp only [map_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ n ∈ Finset.range (H + 1), ∑ j ∈ Finset.range J, M (U j n) :=
        Finset.sum_congr rfl (fun n _ => sum_range_zero_predecessor (fun j => M (U j n)) J)
      _ = _ := Finset.sum_comm
  have hs : (∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.range (H + 1),
      if n = 0 then 0 else S (U j (n - 1))) =
      S (∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.range H, U j n) := by
    simp only [map_sum]
    exact Finset.sum_congr rfl (fun j _ => sum_range_zero_predecessor (fun n => S (U j n)) H)
  have he : (∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.range (H + 1), U j n) =
      f + M (∑ j ∈ Finset.range J, ∑ n ∈ Finset.range (H + 1), U j n) +
      S (∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.range H, U j n) := by
    rw [Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl
      (fun n _ => finiteResponse_native_equation M S f j n))]
    simp only [Finset.sum_add_distrib]
    rw [hbase, hm, hs]
  have hmfull : M (∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.range (H + 1), U j n) =
      M (∑ j ∈ Finset.range J, ∑ n ∈ Finset.range (H + 1), U j n) +
      M (∑ n ∈ Finset.range (H + 1), U J n) := by
    rw [Finset.sum_range_succ, map_add]
  have hsfull : S (∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.range (H + 1), U j n) =
      S (∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.range H, U j n) +
      S (∑ j ∈ Finset.range (J + 1), U j H) := by
    rw [Finset.sum_congr rfl (fun j _ => Finset.sum_range_succ (fun n => U j n) H),
      Finset.sum_add_distrib, map_add]
  change (∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.range (H + 1), U j n) -
    M (∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.range (H + 1), U j n) -
    S (∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.range (H + 1), U j n) = _
  rw [hmfull, hsfull, he]
  abel

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Native source jets with a fixed maximum original order are retained exactly once by any sufficient Sobolev reserve. -/

variable {E : Type*} [AddCommMonoid E]

theorem nativeJet_source_order_sum (K D : ℕ) (hD : D ≤ K + 1)
    (f : ∀ r : ℕ, DerivativeWord2 r → E) :
    (∑ a : JetIndex2 K, if 1 ≤ a.1.val ∧ a.1.val < D then f a.1.val a.2 else 0) =
      ∑ r ∈ Finset.Icc 1 (D - 1), ∑ A : DerivativeWord2 r, f r A := by
  classical
  rw [nativeJet_order_sum K (fun r A => if 1 ≤ r ∧ r < D then f r A else 0)]
  have he (r : ℕ) : (∑ A : DerivativeWord2 r, if 1 ≤ r ∧ r < D then f r A else 0) =
      if 1 ≤ r ∧ r < D then ∑ A : DerivativeWord2 r, f r A else 0 := by
    by_cases hr : 1 ≤ r ∧ r < D
    · simp only [ite_eq_left hr]
    · simp only [ite_eq_right hr, Finset.sum_const_zero]
  simp_rw [he]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  · intro r hr
    rfl

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! Rank discounts make triangular Schur budgets small while retaining the original masses and avoiding component counts. -/

variable {ι : Type*}

theorem massConjugatedMatrix_rank_product
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (r : ι → ℕ) (L : ℝ)
    (A : Matrix ι ι ℝ) :
    massConjugatedMatrix (fun i => π i * rankMass r L i) A =
      massConjugatedMatrix (rankMass r L) (massConjugatedMatrix π A) := by
  funext v u
  unfold massConjugatedMatrix
  rw [mul_div_mul_comm, Real.sqrt_mul (div_nonneg (hπ u).le (hπ v).le),
    mul_assoc]
  ring

theorem originalMass_rank_entry_le
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (r : ι → ℕ) (L : ℝ) (hL : 1 ≤ L)
    (A : Matrix ι ι ℝ) (hA : ∀ v u, 0 ≤ A v u)
    (hr : ∀ v u, A v u ≠ 0 → r u < r v) (v u : ι) :
    massConjugatedMatrix (fun i => π i * rankMass r L i) A v u ≤
      massConjugatedMatrix π A v u / L := by
  rw [massConjugatedMatrix_rank_product π hπ r L A]
  by_cases hz : A v u = 0
  · simp only [massConjugatedMatrix, hz, mul_zero, zero_div]
    exact le_refl 0
  · have hn : 0 ≤ massConjugatedMatrix π A v u :=
      mul_nonneg (Real.sqrt_nonneg _) (hA v u)
    have he := mul_le_mul_of_nonneg_right
      (rankMass_sqrt_ratio_le_inv r L hL v u (hr v u hz)) hn
    simpa only [massConjugatedMatrix, one_div_mul_eq_div] using he

variable [Fintype ι]

theorem originalMass_rank_schur_budget
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (r : ι → ℕ) (L : ℝ) (hL : 1 ≤ L)
    (A : Matrix ι ι ℝ) (hA : ∀ v u, 0 ≤ A v u)
    (hr : ∀ v u, A v u ≠ 0 → r u < r v) (B : ℝ)
    (hrow : ∀ v, ∑ u, massConjugatedMatrix π A v u ≤ B)
    (hcol : ∀ u, ∑ v, massConjugatedMatrix π A v u ≤ B) :
    (∀ v, ∑ u, massConjugatedMatrix (fun i => π i * rankMass r L i) A v u ≤ B / L) ∧
    (∀ u, ∑ v, massConjugatedMatrix (fun i => π i * rankMass r L i) A v u ≤ B / L) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  constructor
  · intro v
    calc
      _ ≤ ∑ u, massConjugatedMatrix π A v u / L :=
        Finset.sum_le_sum (fun u _ => originalMass_rank_entry_le π hπ r L hL A hA hr v u)
      _ = (∑ u, massConjugatedMatrix π A v u) / L := (Finset.sum_div _ _ _).symm
      _ ≤ B / L := div_le_div_of_nonneg_right (hrow v) hLp.le
  · intro u
    calc
      _ ≤ ∑ v, massConjugatedMatrix π A v u / L :=
        Finset.sum_le_sum (fun v _ => originalMass_rank_entry_le π hπ r L hL A hA hr v u)
      _ = (∑ v, massConjugatedMatrix π A v u) / L := (Finset.sum_div _ _ _).symm
      _ ≤ B / L := div_le_div_of_nonneg_right (hcol u) hLp.le

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleJointProofs

/-! Finite cell truncation equals the original periodic representative on a prescribed ball. -/

variable {E : Type*} [NormedAddCommGroup E]

def finiteCellTruncation (M : ℕ) (f : Vec 2 → E) : Vec 2 → E :=
  fun x => ∑ n ∈ Applications.latBox M, (Applications.cellAt n).indicator f x

theorem finiteCellTruncation_memLp (M : ℕ) (f : Vec 2 → E)
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube)) (hp : AVenhance.IsZ2Periodic f) :
    MemLp (finiteCellTruncation M f) 2 volume := by
  classical
  exact memLp_finsetSum _ (fun n _ =>
    (memLp_indicator_iff_restrict (Applications.measurableSet_cellAt n)).mpr
      (periodic_memLp_cellAt f hf hp n))

theorem finiteCellTruncation_eq_on_ball {M : ℕ} {R : ℝ} (hM : R + 1 ≤ M)
    (f : Vec 2 → E) {x : Vec 2} (hx : ‖x‖ ≤ R) : finiteCellTruncation M f x = f x := by
  classical
  have hxc := Applications.supBall_subset_iUnion_cellAt hM hx
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hxc
  obtain ⟨hn, hxn⟩ := Set.mem_iUnion.mp hxn
  unfold finiteCellTruncation
  rw [Finset.sum_eq_single n]
  · exact Set.indicator_of_mem hxn f
  · intro j _ hne
    apply Set.indicator_of_notMem
    intro hxj
    exact Set.disjoint_left.mp (Applications.cellAt_disjoint hne) hxj hxn
  · intro hnot
    exact (hnot hn).elim

end AVRegularity.CycleJointProofs
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The actual coefficient product carrier reads its literal ordered Leibniz jet. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

/-- Every chosen raw jet of the product is the literal Leibniz jet almost everywhere. -/
theorem planeMulCoefficient_rawJet_ae {K : ℕ} (U : PlaneHk Set.univ K E)
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C)
    {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l) (β : JetIndex2 K) :
    (U.mulCoefficient C hC hb).toFunction.jet β =ᵐ[volume]
      multiplicationRawJet C U.toFunction.jet β := by
  have h := (U.toFunction.mulCoefficient C hC hb).toHk_toFunction_ae β
  filter_upwards [(ae_restrict_iff' MeasurableSet.univ).mp h] with x hx
  exact hx (Set.mem_univ x)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! At order zero the actual Sobolev carrier energy is precisely the value's L2 integral. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem zeroJetIndex_eq (a : JetIndex2 0) : a = valueIndex2 0 := by
  obtain ⟨⟨j, hj⟩, w⟩ := a
  have hz : j = 0 := by omega
  subst j
  congr
  ext i
  exact Fin.elim0 i

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
theorem zeroOrderJet_norm_sq (μ : Measure (Vec 2)) (D : JetL2 μ 0 E) :
    ‖D‖ ^ 2 = ‖D (valueIndex2 0)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_eq_single (valueIndex2 0)
  · intro b _ hb
    exact (hb (zeroJetIndex_eq b)).elim
  · simp

theorem planeHk_zero_norm_sq {U : Set (Vec 2)} (f : PlaneHk U 0 E) :
    ‖f‖ ^ 2 = ∫ x in U, ‖f.toFunction.jet (valueIndex2 0) x‖ ^ 2 ∂volume := by
  change ‖f.val‖ ^ 2 = _
  rw [zeroOrderJet_norm_sq]
  simpa only [Lp.toLp_coeFn, PlaneHk.toFunction, planeJetRepresentative] using
    normSq_toLp_eq_integral (Lp.memLp (f.val (valueIndex2 0)))

theorem torusHk_zero_norm_sq (f : TorusHk 0 E) :
    ‖f‖ ^ 2 = ∫ x in AVenhance.unitCube,
      ‖f.toFunction.jet (valueIndex2 0) x‖ ^ 2 ∂volume := by
  change ‖f.val‖ ^ 2 = _
  rw [zeroOrderJet_norm_sq]
  have he := periodicJetRepresentative_ae f.val (valueIndex2 0)
  have hi : (∫ x in AVenhance.unitCube,
      ‖periodicJetRepresentative f.val (valueIndex2 0) x‖ ^ 2 ∂volume) =
      ∫ x in AVenhance.unitCube, ‖(f.val (valueIndex2 0)) x‖ ^ 2 ∂volume :=
    integral_congr_ae (he.mono (fun _ h => congrArg (fun z : E => ‖z‖ ^ 2) h))
  change ‖f.val (valueIndex2 0)‖ ^ 2 =
    ∫ x in AVenhance.unitCube, ‖periodicJetRepresentative f.val (valueIndex2 0) x‖ ^ 2 ∂volume
  rw [hi]
  simpa only [Lp.toLp_coeFn] using normSq_toLp_eq_integral (Lp.memLp (f.val (valueIndex2 0)))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! A zero coefficient produces the genuine zero Sobolev carrier. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] [FiniteDimensional ℝ F]

/-- Vanishing pointwise coefficients give zero in the actual carrier, independently of budgets. -/
theorem planeMulCoefficient_eq_zero {K : ℕ} (U : PlaneHk Set.univ K E)
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C)
    {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l)
    (hz : ∀ x, C x = 0) : U.mulCoefficient C hC hb = 0 := by
  apply PlaneHk.ext_value isOpen_univ
  apply Lp.ext
  have hr := planeMulCoefficient_rawJet_ae U C hC hb (valueIndex2 K)
  have ha : (U.mulCoefficient C hC hb).toFunction.jet (valueIndex2 K) =ᵐ[volume]
      fun _ => (0 : F) := by
    filter_upwards [hr] with x hx
    rw [hx, multiplicationRawJet_value, hz x, zero_apply]
  have h0 := Lp.coeFn_zero F 2 ((volume : Measure (Vec 2)).restrict Set.univ)
  filter_upwards [ae_restrict_of_ae ha, h0] with x hx hzx
  exact hx.trans hzx.symm

end AVRegularity.CycleJointProofs
end
end
