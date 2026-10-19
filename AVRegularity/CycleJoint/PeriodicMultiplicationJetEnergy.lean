-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.PlaneScalarDiffusionDeviationReadout
public import AVRegularity.CycleJoint.CoupledWeakIdentityIntegralImageAssembly
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyDimFlux
import AVRegularity.CoupledEnergyPlane.Variational.PrincipalMask
public import AVRegularity.Statements.Intermediate.Families.FamilyEdges
public import AVRegularity.Statements.Intermediate.CycleJoint.HasEdgePath
public import AVRegularity.Statements.Intermediate.Families.ChartInvJacobian
import AVRegularity.CycleJoint.CoefficientSeminormAddition
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds

section
section
@[expose] public noncomputable section
open AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Uniform coefficient prefactors and mesh powers preserve factorial radii. -/

theorem factorialWeight_coefficient_mesh_price (ρ s L B : ℝ)
    (hρ : 0 ≤ ρ) (hs : 0 ≤ s) (hL : 1 ≤ L) (hmesh : ρ * s ≤ L)
    {j K : ℕ} (hj : j ≤ K) (m : PositionMask j) :
    factorialWeight ρ j * (9 * (B * s ^ maskLeftLength j m) ^ 2) ≤
      (9 * B ^ 2 * L ^ (2 * K)) * factorialWeight ρ (maskRightLength j m) := by
  have hp := mul_le_mul_of_nonneg_left
    (factorialWeight_mask_mesh_reserve ρ s L hρ hs hL hmesh hj m)
    (mul_nonneg (show (0 : ℝ) ≤ 9 by norm_num) (sq_nonneg B))
  rw [show 2 * maskLeftLength j m = maskLeftLength j m * 2 by omega,
    pow_mul] at hp
  convert hp using 1 <;> ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleJointProofs

/-! Every measurable partition weight is an L² contraction, including at times outside the cover. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem family_weight_le_one (F : ChartedFamily ι h D P Ctx) (p : P) (t : ℝ) :
    F.weight p t ≤ 1 := by
  classical
  by_cases hp : t ∈ (F.piece p).output
  · let S := (F.locally_finite t t).toFinset
    have hsum : (∑ q ∈ S, F.weight q t) = 1 := by
      rw [← F.weight_sum t ⟨p, hp⟩]
      symm
      apply finsum_eq_sum_of_support_subset
      intro q hq
      exact (piece_time_finset_mem_iff F t q).mpr (by
        by_contra hout
        exact hq (F.weight_zero q t hout))
    rw [← hsum]
    exact Finset.single_le_sum (fun q _ => F.weight_nonneg q t)
      ((piece_time_finset_mem_iff F t p).mpr hp)
  · rw [F.weight_zero p t hp]
    exact zero_le_one

theorem family_weight_finset_sum_le_one (F : ChartedFamily ι h D P Ctx)
    (S : Finset P) (t : ℝ) : (∑ p ∈ S, F.weight p t) ≤ 1 := by
  classical
  by_cases hactive : ∃ p, t ∈ (F.piece p).output
  · let T := (F.locally_finite t t).toFinset
    have htotal : (∑ p ∈ S ∪ T, F.weight p t) = 1 := by
      rw [← F.weight_sum t hactive]
      symm
      apply finsum_eq_sum_of_support_subset
      intro p hp
      apply Finset.mem_union_right
      exact (piece_time_finset_mem_iff F t p).mpr (by
        by_contra hout
        exact hp (F.weight_zero p t hout))
    rw [← htotal]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      (fun p _ _ => F.weight_nonneg p t)
  · have hz : ∀ p, F.weight p t = 0 := fun p => F.weight_zero p t
      (fun hp => hactive ⟨p, hp⟩)
    simp only [hz, Finset.sum_const_zero]
    exact zero_le_one

theorem family_weight_abs_le_one (F : ChartedFamily ι h D P Ctx) (p : P) (t : ℝ) :
    |F.weight p t| ≤ 1 := by
  rw [abs_of_nonneg (F.weight_nonneg p t)]
  exact family_weight_le_one F p t

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! Exact transfer of a normalized cell sample's jet budget to physical coordinates. -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem normalized_physical_sample_jet_le (f : Vec 2 → V) (j : ℕ)
    (hf : ContDiff ℝ (j : ℕ) f) (s e ρ B : ℝ) (he : 0 < e)
    (hb : ∀ z, (ρ / e) ^ j * ‖iteratedFDeriv ℝ j f z‖ ≤ B) (x : Vec 2) :
    ρ ^ j * ‖iteratedFDeriv ℝ j (fun y => s • f (e⁻¹ • y)) x‖ ≤ |s| * B := by
  have hc : ContDiff ℝ (j : ℕ) (fun y : Vec 2 => f (e⁻¹ • y)) :=
    hf.comp (contDiff_id.const_smul (e⁻¹))
  rw [iteratedFDeriv_const_smul_apply' hc.contDiffAt, norm_smul, Real.norm_eq_abs]
  calc
    _ = |s| * (ρ ^ j * ‖iteratedFDeriv ℝ j (fun y => f (e⁻¹ • y)) x‖) := by ring
    _ = |s| * ((ρ / e) ^ j * ‖iteratedFDeriv ℝ j f (e⁻¹ • x)‖) := by
      rw [AVRegularity.CycleWords.normalizedJet_rescaling_eq j hf,
        abs_of_pos (inv_pos.mpr he), ← div_eq_mul_inv]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb (e⁻¹ • x)) (abs_nonneg s)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Carrier addition and scaling have the expected periodic representatives on the whole plane. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  {K : ℕ}

omit [NormedSpace ℝ E] in
theorem periodicJetRepresentative_add_global
    (D G : JetL2 (volume.restrict AVenhance.unitCube) K E) (a : JetIndex2 K) :
    periodicJetRepresentative (D + G) a =ᵐ[volume]
      fun x => periodicJetRepresentative D a x + periodicJetRepresentative G a x := by
  apply periodic_ae_eq_global _ _ (periodicJetRepresentative_periodic (D + G) a)
    (fun n x => by rw [periodicJetRepresentative_periodic D a n x,
      periodicJetRepresentative_periodic G a n x])
  filter_upwards [periodicJetRepresentative_ae (D + G) a, periodicJetRepresentative_ae D a,
    periodicJetRepresentative_ae G a, Lp.coeFn_add (D a) (G a)] with x hsum hD hG hc
  rw [hsum, hD, hG]
  exact hc

theorem periodicJetRepresentative_smul_global (c : ℝ)
    (D : JetL2 (volume.restrict AVenhance.unitCube) K E) (a : JetIndex2 K) :
    periodicJetRepresentative (c • D) a =ᵐ[volume]
      fun x => c • periodicJetRepresentative D a x := by
  apply periodic_ae_eq_global _ _ (periodicJetRepresentative_periodic (c • D) a)
    (fun n x => by rw [periodicJetRepresentative_periodic D a n x])
  filter_upwards [periodicJetRepresentative_ae (c • D) a, periodicJetRepresentative_ae D a,
    Lp.coeFn_smul c (D a)] with x hsum hD hc
  rw [hsum, hD]
  exact hc

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Original dimensional piece fluxes indexed by their positive native input derivative order. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

def pieceDimensionalNativeJetArray (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (t : ℝ)
    (r : ℕ) (I : DerivativeWord2 r) (y : Vec 2) : Vec 2 :=
  F.dimFlux ν e E p c v u γ (r + 1)
    (by simpa only [Nat.add_sub_cancel] using I) t y (e⁻¹ • y)

theorem pieceDimensionalNativeJetArray_source_order
    (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (t : ℝ)
    (d : ℕ) (hd : 1 ≤ d) (I : DerivativeWord2 (d - 1)) (y : Vec 2) :
    pieceDimensionalNativeJetArray F ν e E p c v u γ t (d - 1) I y =
      F.dimFlux ν e E p c v u γ d I t y (e⁻¹ • y) := by
  cases d with
  | zero => omega
  | succ d => rfl

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Strong time regularity of stored derivatives gives strong Sobolev time regularity. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHk_strong_time_of_jets {U : Set (Vec 2)} {K : ℕ} {a b : ℝ}
    (z dz : ℝ → PlaneHk U K E)
    (h : ∀ α : JetIndex2 K, CycleEvolution.StrongTimeRegularity a b
      (fun t => (z t).val α) (fun t => (dz t).val α)) :
    CycleEvolution.StrongTimeRegularity a b z dz := by
  apply closedSubspace_strong_time (planeHkGraph (E := E) U K) z dz
  have hp := strongTime_piLp (fun α t => (z t).val α)
    (fun α t => (dz t).val α) h
  simpa only [WithLp.toLp_ofLp] using hp

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! A genuine plane Sobolev carrier is already determined by any lower-order truncation. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K L : ℕ}

theorem truncatePlaneHk_injective (hKL : K ≤ L) :
    Function.Injective (truncatePlaneHk (E := E) (U := Set.univ) hKL) := by
  intro f g hfg
  apply PlaneHk.ext_value isOpen_univ
  have hv := congrArg (fun u : PlaneHk Set.univ K E => u.val (valueIndex2 K)) hfg
  have hz : truncateJetIndex hKL (valueIndex2 K) = valueIndex2 L := rfl
  simpa only [truncatePlaneHk_apply, hz] using hv

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! Fixed bounded observation sets convert lattice decay into translated spatial moments. -/

theorem spatialLatticeWeight_le_local_moment (n : Fin 2 → ℤ) (x z : Vec 2)
    (R : ℝ) (hR : 0 ≤ R) (hx : ‖x‖ ≤ R) :
    spatialLatticeWeight n ≤ (1 + R + ‖z‖) ^ 2 *
      (1 + ‖x + AVenhance.latticeShift n - z‖) ^ 2 := by
  have hbase : 0 ≤ 1 + ‖x‖ + ‖z‖ + ‖x + AVenhance.latticeShift n - z‖ := by positivity
  have hc : 0 ≤ 1 + R + ‖z‖ := by positivity
  have ht : 0 ≤ ‖x + AVenhance.latticeShift n - z‖ := norm_nonneg _
  have he : 1 + ‖x‖ + ‖z‖ + ‖x + AVenhance.latticeShift n - z‖ ≤
      (1 + R + ‖z‖) * (1 + ‖x + AVenhance.latticeShift n - z‖) := by
    nlinarith only [hx, hR, norm_nonneg z, mul_nonneg hR ht,
      mul_nonneg (norm_nonneg z) ht]
  calc
    spatialLatticeWeight n ≤ _ := spatialLatticeWeight_le_translated_norm n x z
    _ ≤ ((1 + R + ‖z‖) * (1 + ‖x + AVenhance.latticeShift n - z‖)) ^ 2 :=
      pow_le_pow_left₀ hbase he _
    _ = _ := mul_pow _ _ _

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Genuine spatial L2 forcings preserve all-time spatial integrability under time-a.e. replacement. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem coupledWeakIdentity_time_ae_forcing_congr (μ : Measure (Vec 2)) (ν a t : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (u f φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (du : ℝ → Fin 2 → Vec 2 → E)
    (flux F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (g : ℝ → Vec 2 → E)
    (hdφ : ∀ k, MemLp (dφ k) 2 μ)
    (hF : ∀ s ∈ Set.Ioc a t, ∀ k, MemLp (fun x => F s x k) 2 μ)
    (hF' : ∀ s ∈ Set.Ioc a t, ∀ k, MemLp (fun x => F' s x k) 2 μ)
    (heq : ∀ᵐ s ∂volume.restrict (Set.Ioc a t), F s =ᵐ[μ] F' s)
    (hs : CoupledWeakIdentity μ ν a t v u f φ dφ du flux F g) :
    CoupledWeakIdentity μ ν a t v u f φ dφ du flux F' g := by
  apply coupledWeakIdentity_time_ae_rhs_congr μ ν a t v u f φ dφ du flux F F' g heq _ hs
  intro s hst
  have hcorrection : Integrable (fun x => ∑ k : Fin 2,
      inner ℝ (F s x k - F' s x k) (dφ k x)) μ :=
    integrable_finsetSum Finset.univ (fun k _ => rawInner_integrable_of_memLp_two μ _ _
      ((hF s hst k).sub (hF' s hst k)) (hdφ k))
  apply ((hs.2.2.1 s hst).add hcorrection).congr
  apply Filter.Eventually.of_forall
  intro x
  simp only [Pi.add_apply, weakIdentityRhs, inner_add_left, inner_sub_left,
    Fin.sum_univ_two]
  ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Differentiation preserves the original spatial support of every coefficient array. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem orderedCoefficientDerivative_tsupport_subset (C : Vec 2 → E →L[ℝ] F)
    (j : ℕ) (w : DerivativeWord2 j) :
    tsupport (orderedCoefficientDerivative C j w) ⊆ tsupport C := by
  induction j with
  | zero => exact Set.Subset.refl _
  | succ j ih =>
    exact (tsupport_fderiv_apply_subset ℝ (basisVec (w (Fin.last j)))).trans (ih (Fin.init w))

theorem coefficientDerivativeArray_zero_of_not_tsupport (C : Vec 2 → E →L[ℝ] F)
    (j : ℕ) (x : Vec 2) (hx : x ∉ tsupport C) : coefficientDerivativeArray C j x = 0 := by
  have hz (w : DerivativeWord2 j) : orderedCoefficientDerivative C j w x = 0 := by
    by_contra hn
    exact hx (orderedCoefficientDerivative_tsupport_subset C j w (subset_tsupport _ hn))
  ext z w
  change orderedCoefficientDerivative C j w x z = 0
  rw [hz]
  rfl

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Shrinking the auxiliary existence radius preserves finite coefficient seminorms. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem coefficientSeminorm_radius_mono (ρ R : ℝ) (hρ : 0 ≤ ρ) (hρR : ρ ≤ R)
    (K : ℕ) (a b : ℝ) (A : ℝ → Vec 2 → E →L[ℝ] F) :
    coefficientSeminorm ρ K a b A ≤ coefficientSeminorm R K a b A := by
  unfold coefficientSeminorm
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_right _ zero_le
  exact ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ hρ hρR j) (by positivity))

theorem coefficientSeminorm_radius_ne_top (ρ R : ℝ) (hρ : 0 ≤ ρ) (hρR : ρ ≤ R)
    (K : ℕ) (a b : ℝ) (A : ℝ → Vec 2 → E →L[ℝ] F)
    (hA : coefficientSeminorm R K a b A ≠ ⊤) :
    coefficientSeminorm ρ K a b A ≠ ⊤ :=
  ne_top_of_le_ne_top hA (coefficientSeminorm_radius_mono ρ R hρ hρR K a b A)

theorem exists_auxiliary_absorption_radius (ρ ν M : ℝ)
    (hρ : 0 < ρ) (hν : 0 < ν) (hM : 0 ≤ M) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧ r ≤ 1 / 2 ∧ M * r ^ 2 ≤ ν / 8 := by
  let r := min ρ (min (1 / 2) (ν / (8 * (M + 1))))
  have hden : 0 < 8 * (M + 1) := by positivity
  have hr : 0 < r := lt_min hρ (lt_min (by norm_num) (div_pos hν hden))
  have hrhalf : r ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hrν : r ≤ ν / (8 * (M + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hmul := (le_div_iff₀ hden).mp hrν
  refine ⟨r, hr, min_le_left _ _, hrhalf, ?_⟩
  have hsquare : r ^ 2 ≤ r := by nlinarith
  have hmr : M * r ≤ ν / 8 := by nlinarith
  exact (mul_le_mul_of_nonneg_left hsquare hM).trans hmr
end

/-! Restricting the coefficient time window decreases its pointwise seminorm. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem coefficientSeminorm_time_mono (ρ : ℝ) (K : ℕ) (a b c d : ℝ)
    (hsub : Set.Icc a b ⊆ Set.Icc c d) (A : ℝ → Vec 2 → E →L[ℝ] F) :
    coefficientSeminorm ρ K a b A ≤ coefficientSeminorm ρ K c d A := by
  unfold coefficientSeminorm
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ zero_le
  refine iSup_le fun t => iSup_le fun ht => ?_
  exact le_iSup_of_le t (le_iSup_of_le (hsub ht) le_rfl)
end

end AVRegularity.CycleJointProofs
end
end

section
public section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The coefficient reserve depends on spatial slices only at times in its window. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem coefficientSeminorm_window_congr
    (ρ : ℝ) (K : ℕ) (a b : ℝ)
    (A A' : ℝ → Vec 2 → E →L[ℝ] F)
    (heq : ∀ t ∈ Set.Icc a b, A' t = A t) :
    coefficientSeminorm ρ K a b A' = coefficientSeminorm ρ K a b A := by
  unfold coefficientSeminorm
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply iSup_congr
  intro t
  apply iSup_congr
  intro ht
  rw [heq t ht]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The zeroth factorial-seminorm term bounds the literal pointwise coefficient. -/

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem coefficient_norm_le_value_array (A : Vec 2 → E →L[ℝ] G) (x : Vec 2) :
    ‖A x‖ ≤ ‖coefficientDerivativeArray A 0 x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro z
  have hp := PiLp.norm_apply_le (coefficientDerivativeArray A 0 x z)
    (fun i : Fin 0 => Fin.elim0 i)
  exact hp.trans ((coefficientDerivativeArray A 0 x).le_opNorm z)

theorem coefficient_value_le_seminorm (ρ : ℝ) (K : ℕ) (t₀ t₁ : ℝ)
    (A : ℝ → Vec 2 → E →L[ℝ] G) (t : ℝ) (ht : t ∈ Set.Icc t₀ t₁) (x : Vec 2) :
    ENNReal.ofReal ‖A t x‖ ≤ coefficientSeminorm ρ K t₀ t₁ A := by
  have hp : ENNReal.ofReal ‖A t x‖ ≤
      ⨆ s ∈ Set.Icc t₀ t₁, ⨆ y : Vec 2,
        (‖coefficientDerivativeArray (A s) 0 y‖₊ : ℝ≥0∞) := by
    apply le_iSup_of_le t
    apply le_iSup_of_le ht
    apply le_iSup_of_le x
    simpa only [← ENNReal.ofReal_coe_nnreal, coe_nnnorm] using
      ENNReal.ofReal_le_ofReal (coefficient_norm_le_value_array (A t) x)
  unfold coefficientSeminorm
  have hs := Finset.single_le_sum
    (f := fun j : ℕ => ENNReal.ofReal (ρ ^ j / (j.factorial : ℝ)) *
      ⨆ s ∈ Set.Icc t₀ t₁, ⨆ y : Vec 2,
        (‖coefficientDerivativeArray (A s) j y‖₊ : ℝ≥0∞))
    (fun _ _ => zero_le) (Finset.mem_range.mpr (Nat.zero_lt_succ K))
  exact hp.trans (by simpa using hs)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! Prepending a source edge preserves the literal finite-path representation. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem hasEdgePath_prepend {F : ChartedFamily ι h D P Ctx} {n : ℕ} {u v w : ι}
    (hp : HasEdgePath F n u v) (he : Nonempty (F.Γ u w)) : HasEdgePath F (n + 1) w v := by
  obtain ⟨p, h0, hl, hp⟩ := hp
  refine ⟨Fin.cons w p, by simp, ?_, ?_⟩
  · simpa using hl
  · intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · simpa [h0] using he
    · simpa using hp j

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The terminal row retains its metric power at one common initial moment reserve. -/

def terminalResponseEnergyPrice (C θ : ℝ≥0∞) (J H : ℕ) : ℝ≥0∞ :=
  2 ^ (H + 1) * ∑ h ∈ Finset.range (H + 1),
    shiftedResponseEnergyBudget (fun _ => 1) (fun _ => 1) 0 0 J h * C ^ (J + h) * θ ^ (2 * h)

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem finiteResponse_terminal_energy_gain (M S : Module.End ℝ E)
    (energy : ℕ → E → ℝ≥0∞) (a b : ℕ → ℝ≥0∞) (C η θ : ℝ≥0∞) (p N : ℕ)
    (hz : ∀ n, energy n 0 = 0)
    (hadd : ∀ n x y, energy n (x + y) ≤ 2 * (energy n x + energy n y))
    (hM : ∀ n, n + p ≤ N → ∀ x, energy n (M x) ≤ a n * energy (n + p) x)
    (hS : ∀ n, n + p ≤ N → ∀ x, energy n (S x) ≤ b n * energy (n + p) x)
    (ha : ∀ k ≤ N, a k ≤ C * η ^ 2) (hb : ∀ k ≤ N, b k ≤ C * θ ^ 2)
    (f : E) (G0 : ℝ≥0∞) (hinit : ∀ k ≤ N, energy k f ≤ G0)
    (n J H : ℕ) (hN : n + (J + H) * p ≤ N) :
    energy n (∑ h ∈ Finset.range (H + 1), finiteResponse 1 M S f J h) ≤
      terminalResponseEnergyPrice C θ J H * η ^ (2 * J) * G0 := by
  refine (finite_quadratic_energy_sum_le (energy n) (hz n) (hadd n) _ _).trans ?_
  simp only [Finset.card_range]
  calc
    2 ^ (H + 1) * ∑ h ∈ Finset.range (H + 1), energy n (finiteResponse 1 M S f J h) ≤
        2 ^ (H + 1) * ∑ h ∈ Finset.range (H + 1),
          ((shiftedResponseEnergyBudget (fun _ => 1) (fun _ => 1) 0 0 J h *
            C ^ (J + h) * θ ^ (2 * h)) * η ^ (2 * J) * G0) := by
      apply mul_le_mul_of_nonneg_left _ zero_le
      apply Finset.sum_le_sum
      intro h hh
      have hh' : h ≤ H := Nat.le_of_lt_succ (Finset.mem_range.mp hh)
      have hk : n + (J + h) * p ≤ N :=
        (Nat.add_le_add_left (Nat.mul_le_mul_right p (Nat.add_le_add_left hh' J)) n).trans hN
      have he := finiteResponse_reserved_energy_gain M S energy a b C η θ p N hadd hM hS
        ha hb f n J h hk
      rw [shiftedResponseEnergyBudget_unit_independent p 0 n 0] at he
      have he' := he.trans (mul_le_mul_of_nonneg_left (hinit _ hk) zero_le)
      convert he' using 1
      ring
    _ = terminalResponseEnergyPrice C θ J H * η ^ (2 * J) * G0 := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      unfold terminalResponseEnergyPrice
      ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! Descending original identities retain precisely their admissible derivative
orders; a fixed Fin D array only pads those orders with exact zeros. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {E : Type*} [AddCommMonoid E]

theorem originalNativeOrder_admissible_eq_padded
    (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ) (hdesc : F.IsDescending K)
    (v u : ι) (γ : F.Γ v u) (f : ℕ → E)
    (hz : ∀ r, (F.identity v u γ).maxOrder ≤ r → f r = 0) :
    (∑ d : admissibleOrders K D v u, f (d.val - 1)) =
      ∑ j : Fin D, f (j.val + 1) := by
  classical
  rw [Finset.sum_coe_sort (admissibleOrders K D v u) (fun d => f (d - 1))]
  have had : (∑ d ∈ admissibleOrders K D v u, f (d - 1)) =
      ∑ d ∈ Finset.Icc 2 D, f (d - 1) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hnot
    have hd' := Finset.mem_Icc.mp hd
    have hreserve : ¬ K v + d ≤ K u + 2 := by
      intro hh
      exact hnot (Finset.mem_filter.mpr ⟨hd, hh⟩)
    have hh := hdesc v u γ
    exact hz (d - 1) (by omega)
  rw [had, ← native_source_order_shift]
  have hpadded : (∑ r ∈ Finset.Icc 1 (D - 1), f r) = ∑ r ∈ Finset.Icc 1 D, f r := by
    apply Finset.sum_subset
    · intro r hr
      have hh := Finset.mem_Icc.mp hr
      exact Finset.mem_Icc.mpr ⟨hh.1, hh.2.trans (Nat.sub_le _ _)⟩
    · intro r hr hnot
      have hh := Finset.mem_Icc.mp hr
      have hrd : r = D := by
        by_contra hne
        exact hnot (Finset.mem_Icc.mpr ⟨hh.1, by omega⟩)
      apply hz r
      simpa only [hrd] using (F.identity v u γ).le_D
  rw [hpadded, Fin.sum_univ_eq_sum_range (fun j => f (j + 1)) D]
  symm
  apply Finset.sum_bij (fun j _ => j + 1)
  · intro j hj
    have hh := Finset.mem_range.mp hj
    exact Finset.mem_Icc.mpr ⟨Nat.succ_pos _, Nat.succ_le_of_lt hh⟩
  · intro j _ k _ heq
    omega
  · intro r hr
    have hh := Finset.mem_Icc.mp hr
    refine ⟨r - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro j _
    rfl

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! A fourth radial moment dominates the squared lattice weight on any fixed ball. -/

theorem spatialImage_moment_lower_bound (n : Fin 2 → ℤ) (x z : Vec 2)
    (R : ℝ) (hR : 0 ≤ R) (hx : ‖x‖ ≤ R) :
    1 ≤ ((1 + R + ‖z‖) ^ 4 * (1 / spatialLatticeWeight n) ^ 2) *
      (1 + ‖x + AVenhance.latticeShift n - z‖) ^ 4 := by
  have hw := spatialLatticeWeight_le_local_moment n x z R hR hx
  have hp := spatialLatticeWeight_pos n
  have hs : spatialLatticeWeight n ^ 2 ≤
      (1 + R + ‖z‖) ^ 4 * (1 + ‖x + AVenhance.latticeShift n - z‖) ^ 4 := by
    have he := pow_le_pow_left₀ hp.le hw 2
    convert he using 1; ring
  have hh := mul_le_mul_of_nonneg_right hs (sq_nonneg (1 / spatialLatticeWeight n))
  have hc : spatialLatticeWeight n ^ 2 * (1 / spatialLatticeWeight n) ^ 2 = 1 := by
    field_simp
  rw [hc] at hh
  convert hh using 1; ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The exact native order-lowering flux recursion separates coefficient differentiation from the next derivative of the state. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem transitionT_cons_flux (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (i : Fin 2) (I : List (Fin 2)) (r : ℕ)
    (g : DerivativeWord2 (r + 1) → E) (x : Vec 2) :
    (∑ A : DerivativeWord2 (r + 1), transitionT K (i :: I) (List.ofFn A) x • g A) =
      (∑ A : DerivativeWord2 (r + 1),
        weightedCoordinateDerivative K i (transitionT K I (List.ofFn A)) x • g A) +
      ∑ a : Fin 2, K x a i •
        (∑ A : DerivativeWord2 r, transitionT K I (List.ofFn A) x • g (Fin.cons a A)) := by
  classical
  rw [derivativeWord_cons_sum r, derivativeWord_cons_sum r]
  simp only [List.ofFn_cons, transitionT, weightedCoordinateDerivative, smul_eq_mul,
    add_smul, Finset.sum_add_distrib, Finset.smul_sum, mul_smul]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! Each coordinate of a sampled vector field spends no additional jet budget. -/

theorem vector_component_jet_budget (f : Vec 2 → Vec 2) (n : ℕ)
    (hf : ContDiff ℝ (n : ℕ) f) (ρ B : ℝ) (hρ : 0 ≤ ρ)
    (hb : ∀ x, ρ ^ n * ‖iteratedFDeriv ℝ n f x‖ ≤ B) (i : Fin 2) (x : Vec 2) :
    ρ ^ n * ‖iteratedFDeriv ℝ n (fun y => f y i) x‖ ≤ B := by
  let L : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    change ‖z i‖ ≤ 1 * ‖z‖
    simpa only [one_mul] using norm_le_pi_norm z i
  have hh := L.norm_iteratedFDeriv_comp_left (n := n) (x := x) hf.contDiffAt le_rfl
  have hnorm : ‖iteratedFDeriv ℝ n (fun y => f y i) x‖ ≤ ‖iteratedFDeriv ℝ n f x‖ := by
    exact hh.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hL (norm_nonneg (iteratedFDeriv ℝ n f x)))
  exact (mul_le_mul_of_nonneg_left hnorm (pow_nonneg hρ n)).trans (hb x)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleJointProofs

/-! Signed integrable plane tests transfer exactly to their lattice periodization. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integral_cell_periodization (f : Vec 2 → E) (hf : Integrable f volume) :
    (∫ x in Applications.cellI, latticePeriodization f x ∂volume) = ∫ x, f x ∂volume := by
  have hi : ∀ n : Fin 2 → ℤ, Integrable
      (fun x => f (x + AVenhance.latticeShift n)) (volume.restrict Applications.cellI) := by
    intro n
    exact ((measurePreserving_add_right (volume : Measure (Vec 2))
      (AVenhance.latticeShift n)).integrable_comp_of_integrable hf).integrableOn
  rw [integral_tiling_translate f hf]
  exact (integral_tsum_of_summable_integral_norm hi
    (summable_cell_integral_norm f hf)).symm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Each coefficient derivative array has the original compact support. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem coefficientDerivativeArray_compact (C : Vec 2 → E →L[ℝ] F)
    (hc : HasCompactSupport C) (j : ℕ) :
    HasCompactSupport (fun x => coefficientDerivativeArray C j x) := by
  apply HasCompactSupport.intro hc
  intro x hx
  exact coefficientDerivativeArray_zero_of_not_tsupport C j x hx

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Literal coefficient derivatives commute with translation on the covering plane. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem orderedCoefficientDerivative_translate (C : Vec 2 → E →L[ℝ] F)
    (j : ℕ) (w : DerivativeWord2 j) (a x : Vec 2) :
    orderedCoefficientDerivative (fun y => C (y + a)) j w x =
      orderedCoefficientDerivative C j w (x + a) := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    have he : orderedCoefficientDerivative (fun y => C (y + a)) j (Fin.init w) =
        fun y => orderedCoefficientDerivative C j (Fin.init w) (y + a) :=
      funext (fun y => ih (Fin.init w) y)
    rw [orderedCoefficientDerivative, he]
    change (fderiv ℝ (fun y => orderedCoefficientDerivative C j (Fin.init w) (y + a)) x)
      (basisVec (w (Fin.last j))) = _
    rw [fderiv_comp_add_right]
    rfl

theorem coefficientDerivativeArray_translate (C : Vec 2 → E →L[ℝ] F)
    (j : ℕ) (a x : Vec 2) :
    coefficientDerivativeArray (fun y => C (y + a)) j x =
      coefficientDerivativeArray C j (x + a) := by
  ext z w
  change orderedCoefficientDerivative (fun y => C (y + a)) j w x z =
    orderedCoefficientDerivative C j w (x + a) z
  rw [orderedCoefficientDerivative_translate]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The literal localized product jet is linear and respects changes of representatives. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {K : ℕ}

theorem multiplicationRawJet_add (C : Vec 2 → E →L[ℝ] F) (D G : RawJet2 K E) :
    multiplicationRawJet C (D + G) = multiplicationRawJet C D + multiplicationRawJet C G := by
  funext a x
  simp [multiplicationRawJet, multiplicationTerm, Pi.add_apply, map_add, Finset.sum_add_distrib]

theorem multiplicationRawJet_smul (C : Vec 2 → E →L[ℝ] F) (c : ℝ) (D : RawJet2 K E) :
    multiplicationRawJet C (c • D) = c • multiplicationRawJet C D := by
  funext a x
  simp [multiplicationRawJet, multiplicationTerm, Pi.smul_apply, map_smul, Finset.smul_sum]

theorem multiplicationRawJet_congr_ae (C : Vec 2 → E →L[ℝ] F) (D G : RawJet2 K E)
    (he : ∀ a, D a =ᵐ[volume] G a) :
    ∀ a, multiplicationRawJet C D a =ᵐ[volume] multiplicationRawJet C G a := by
  have hh : ∀ᵐ x ∂(volume : Measure (Vec 2)), ∀ a, D a x = G a x := ae_all_iff.mpr he
  intro a
  filter_upwards [hh] with x hx
  unfold multiplicationRawJet
  apply Finset.sum_congr rfl
  intro m _
  unfold multiplicationTerm
  rw [hx]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! Composition of literal source paths. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem hasEdgePath_concat {F : ChartedFamily ι h D P Ctx} {n m : ℕ} {u v w : ι}
    (hp : HasEdgePath F n u v) (hq : HasEdgePath F m v w) :
    HasEdgePath F (n + m) u w := by
  induction n generalizing u with
  | zero =>
    obtain ⟨p, h0, hl, _⟩ := hp
    have huv : u = v := by simpa using h0.symm.trans hl
    rw [huv, Nat.zero_add]
    exact hq
  | succ n ih =>
    obtain ⟨p, h0, hl, he⟩ := hp
    have ht : HasEdgePath F n (p 1) v := by
      refine ⟨Fin.tail p, rfl, ?_, ?_⟩
      · simpa [Fin.tail] using hl
      · intro k
        simpa [Fin.tail] using he k.succ
    have hfirst : Nonempty (F.Γ (p 1) u) := by
      simpa [h0] using he 0
    simpa [Nat.succ_add] using hasEdgePath_prepend (ih ht) hfirst

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The literal terminal metric forcing gains one further metric power, without a further scalar response. -/

section
variable {E Q : Type*} [AddCommGroup E] [Module ℝ E]

theorem finiteResponse_terminal_forcing_energy_gain (M S : Module.End ℝ E)
    (energy : ℕ → E → ℝ≥0∞) (fluxEnergy : Q → ℝ≥0∞) (L : E → Q)
    (a b : ℕ → ℝ≥0∞) (C D η θ : ℝ≥0∞) (p N : ℕ)
    (hz : ∀ n, energy n 0 = 0)
    (hadd : ∀ n x y, energy n (x + y) ≤ 2 * (energy n x + energy n y))
    (hM : ∀ n, n + p ≤ N → ∀ x, energy n (M x) ≤ a n * energy (n + p) x)
    (hS : ∀ n, n + p ≤ N → ∀ x, energy n (S x) ≤ b n * energy (n + p) x)
    (ha : ∀ k ≤ N, a k ≤ C * η ^ 2) (hb : ∀ k ≤ N, b k ≤ C * θ ^ 2)
    (f : E) (G0 : ℝ≥0∞) (hinit : ∀ k ≤ N, energy k f ≤ G0)
    (n J H : ℕ) (hN : n + p + (J + H) * p ≤ N)
    (hL : ∀ x, fluxEnergy (L x) ≤ (D * η ^ 2) * energy (n + p) x) :
    fluxEnergy (L (∑ h ∈ Finset.range (H + 1), finiteResponse 1 M S f J h)) ≤
      (D * terminalResponseEnergyPrice C θ J H) * η ^ (2 * (J + 1)) * G0 := by
  have hbnd := finiteResponse_terminal_energy_gain M S energy a b C η θ p N hz hadd
    hM hS ha hb f G0 hinit (n + p) J H hN
  refine ((hL _).trans (mul_le_mul_of_nonneg_left hbnd zero_le)).trans_eq ?_
  rw [Nat.mul_add, Nat.mul_one, pow_add]
  ring
end

/-! The fixed terminal response reserve has a finite energy price. -/

theorem terminalResponseEnergyPrice_ne_top (C θ : ℝ≥0∞) (hC : C ≠ ⊤) (hθ : θ ≠ ⊤)
    (J H : ℕ) : terminalResponseEnergyPrice C θ J H ≠ ⊤ := by
  apply ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
  apply ENNReal.sum_ne_top.mpr
  intro h _
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (shiftedResponseEnergyBudget_unit_ne_top 0 0 J h)
      (ENNReal.pow_ne_top hC)) (ENNReal.pow_ne_top hθ)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Finite Leibniz summation costs only the number of positional subsets. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem multiplicationRawJet_pointwise_square_le {K : ℕ}
    (C : Vec 2 → E →L[ℝ] F) (D : RawJet2 K E) (a : JetIndex2 K) (x : Vec 2) :
    ‖multiplicationRawJet C D a x‖ ^ 2 ≤
      (Fintype.card (PositionMask a.1.val) : ℝ) *
        ∑ m : PositionMask a.1.val,
          ‖multiplicationTerm (Nat.le_of_lt_succ a.1.isLt) C D m a.2 x‖ ^ 2 := by
  unfold multiplicationRawJet
  apply le_trans (pow_le_pow_left₀ (norm_nonneg _)
    (norm_sum_le Finset.univ _) 2)
  simpa only [Finset.card_univ] using
    (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun m : PositionMask a.1.val =>
        ‖multiplicationTerm (Nat.le_of_lt_succ a.1.isLt) C D m a.2 x‖))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Literal zero forcing tests give the actual zero Sobolev carriers in the solution class. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Reattach the genuine zero carriers without choosing their representatives pointwise. -/
theorem coupledWeakIdentity_zeroCarrier_forcing (K : ℕ) (ν a t : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (u₀ f φ : Vec 2 → E)
    (dφ : Fin 2 → Vec 2 → E) (du : ℝ → Fin 2 → Vec 2 → E)
    (flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (h : CoupledWeakIdentity volume ν a t v u₀ f φ dφ du flux 0 0) :
    CoupledWeakIdentity volume ν a t v u₀ f φ dφ du flux
      (fun _ => (0 : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))).toFunction.jet
        (valueIndex2 K))
      (fun _ => (0 : PlaneHk Set.univ K E).toFunction.jet (valueIndex2 K)) := by
  apply coupledWeakIdentity_integrands_congr volume ν a t v v _ _ _ _ _ _ _ _
    _ _ _ _ 0 _ 0 _ Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl _ h
  intro s _
  exact weakIdentityRhs_congr_ae volume ν s v v _ _ _ _ _ _ _ _ 0 _ 0 _
    Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl
    (fun _ => Filter.EventuallyEq.rfl) (fun _ => Filter.EventuallyEq.rfl)
    Filter.EventuallyEq.rfl
    (planeZero_rawJet_ae (E := PiLp 2 (fun _ : Fin 2 => E)) K (valueIndex2 K)).symm
    (planeZero_rawJet_ae (E := E) K (valueIndex2 K)).symm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! Nonnegative time partitions preserve uniform positive jet budgets without a piece-count loss. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem positive_piece_jet_assembly (F : ChartedFamily ι h D P Ctx)
    (a b t : ℝ) (ht : t ∈ Set.Icc a b) (hcover : ∃ p, t ∈ (F.piece p).output)
    (f : P → Vec 2 → V) (n : ℕ) (hf : ∀ p, ContDiff ℝ (n : ℕ) (f p))
    (hz : ∀ p x, t ∉ (F.piece p).output → f p x = 0)
    (ρ B : ℝ) (hρ : 0 ≤ ρ)
    (hjet : ∀ p x, ρ ^ n * ‖iteratedFDeriv ℝ n (f p) x‖ ≤ F.weight p t * B)
    (x : Vec 2) :
    ρ ^ n * ‖iteratedFDeriv ℝ n (fun y => ∑ᶠ p, f p y) x‖ ≤ B := by
  classical
  let s := (F.locally_finite a b).toFinset
  have he y : (∑ᶠ p, f p y) = ∑ p ∈ s, f p y := by
    apply finsum_eq_sum_of_support_subset
    intro p hp
    change p ∈ (F.locally_finite a b).toFinset
    rw [Set.Finite.mem_toFinset]
    have hout : t ∈ (F.piece p).output := by
      by_contra hh
      exact hp (hz p y hh)
    exact ⟨t, hout, ht⟩
  have hw : (∑ p ∈ s, F.weight p t) = 1 := by
    rw [← F.weight_sum t hcover]
    symm
    apply finsum_eq_sum_of_support_subset
    intro p hp
    change p ∈ (F.locally_finite a b).toFinset
    rw [Set.Finite.mem_toFinset]
    have hout : t ∈ (F.piece p).output := by
      by_contra hh
      exact hp (F.weight_zero p t hh)
    exact ⟨t, hout, ht⟩
  simp_rw [he]
  apply (mul_le_mul_of_nonneg_left
    (finite_jet_finset_sum_norm_le s f n (fun p _ => hf p) x) (pow_nonneg hρ n)).trans
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ p ∈ s, F.weight p t * B := Finset.sum_le_sum (fun p _ => hjet p x)
    _ = B := by rw [← Finset.sum_mul, hw, one_mul]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CoupledEnergy.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Spatially frozen coefficients have no positive derivative price at any Sobolev reserve. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem orderedCoefficientDerivative_const_succ (C : E →L[ℝ] F)
    (j : ℕ) (w : DerivativeWord2 (j + 1)) :
    orderedCoefficientDerivative (fun _ : Vec 2 => C) (j + 1) w = 0 := by
  induction j with
  | zero =>
    funext x
    simp [orderedCoefficientDerivative]
  | succ j ih =>
    funext x
    rw [orderedCoefficientDerivative, ih]
    simp

theorem coefficientDerivativeArray_const_succ (C : E →L[ℝ] F) (j : ℕ) (x : Vec 2) :
    coefficientDerivativeArray (fun _ : Vec 2 => C) (j + 1) x = 0 := by
  apply ContinuousLinearMap.ext
  intro U
  apply PiLp.ext
  intro w
  simp only [coefficientDerivativeArray_apply, orderedCoefficientDerivative_const_succ,
    Pi.zero_apply, zero_apply, PiLp.zero_apply]

theorem coefficientSeminorm_spatial_const_le (ρ : ℝ) (K : ℕ) (a b : ℝ)
    (C : ℝ → E →L[ℝ] F) (M : ℝ) (hC : ∀ t ∈ Set.Icc a b, ‖C t‖ ≤ M) :
    coefficientSeminorm ρ K a b (fun t _ => C t) ≤ ENNReal.ofReal M := by
  classical
  unfold coefficientSeminorm
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      ENNReal.ofReal_one, one_mul]
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    apply iSup_le
    intro x
    rw [← ENNReal.ofReal_coe_nnreal]
    simpa only [coe_nnnorm, coefficientDerivativeArray_zero_norm] using
      ENNReal.ofReal_le_ofReal (hC t ht)
  · intro j _ hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [coefficientDerivativeArray_const_succ]
  · intro hzero
    exact (hzero (Finset.mem_range.mpr (Nat.succ_pos K))).elim

end AVRegularity.CycleJointProofs
end
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The positive native derivative indexing reproduces the literal dimensional transported piece array. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem pieceDimensionalNativeJetArray_transported
    (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (t : ℝ)
    (r : ℕ) (A : DerivativeWord2 r) (x : Vec 2) :
    transportedCoeff (chartInvJacobian ⇑((F.piece p).material t).symm)
      (F.identity v u γ).maxOrder
      (fun d I => F.dimFlux ν e E p c v u γ d I t
        (((F.piece p).material t).symm x)
        (e⁻¹ • ((F.piece p).material t).symm x)) r A x =
    transportedCoeff (chartInvJacobian ⇑((F.piece p).material t).symm)
      (F.identity v u γ).maxOrder
      (fun d I => pieceDimensionalNativeJetArray F ν e E p c v u γ t (d - 1) I
        (((F.piece p).material t).symm x)) r A x := by
  apply transportedCoeff_source_congr
  intro d hd I
  exact (pieceDimensionalNativeJetArray_source_order F ν e E p c v u γ t d
    (by have hh := Finset.mem_Icc.mp hd; omega) I _).symm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! A genuine fourth radial moment gives a summable majorant for every lattice image. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem radialMoment_image_eLpNorm_le (f : Vec 2 → E) (z : Vec 2) (R : ℝ)
    (hR : 0 < R) (hf : AEStronglyMeasurable f volume)
    (hw : AEStronglyMeasurable (fun y => (1 + ‖y - z‖) ^ 4 • f y) volume)
    (n : Fin 2 → ℤ) :
    eLpNorm (fun x => f (x + AVenhance.latticeShift n)) 2
      (volume.restrict (Metric.ball (0 : Vec 2) R)) ≤
      ENNReal.ofReal ((1 + R + ‖z‖) ^ 4 * (1 / spatialLatticeWeight n) ^ 2) *
        eLpNorm (fun y => (1 + ‖y - z‖) ^ 4 • f y) 2 volume := by
  have hfm : AEStronglyMeasurable (fun x => f (x + AVenhance.latticeShift n))
      (volume.restrict (Metric.ball (0 : Vec 2) R)) :=
    (hf.comp_measurePreserving
      (measurePreserving_add_right volume (AVenhance.latticeShift n))).restrict
  apply translatedWeighted_eLpNorm_le f (fun y => (1 + ‖y - z‖) ^ 4)
    (Metric.ball (0 : Vec 2) R) (AVenhance.latticeShift n) _ (by positivity) hfm hw
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  have hx' : ‖x‖ ≤ R := by
    have ht : ‖x‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    exact ht.le
  exact spatialImage_moment_lower_bound n x z R hR.le hx'

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Integrated finite Leibniz energy for actual localized periodic jets. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem periodic_multiplicationRawJet_integral_square_le {K : ℕ}
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C)
    (hc : HasCompactSupport C) (D : RawJet2 K E)
    (hD : HasPeriodicOrderedWeakJet D) (a : JetIndex2 K) :
    (∫ x, ‖multiplicationRawJet C D a x‖ ^ 2 ∂volume) ≤
      (Fintype.card (PositionMask a.1.val) : ℝ) *
        ∑ m : PositionMask a.1.val, ∫ x,
          ‖multiplicationTerm (Nat.le_of_lt_succ a.1.isLt) C D m a.2 x‖ ^ 2 ∂volume := by
  have hi (m : PositionMask a.1.val) :=
    (periodic_compact_multiplicationTerm_memLp (Nat.le_of_lt_succ a.1.isLt)
      C hC hc D hD m a.2).norm.integrable_sq
  have hp : MemLp (multiplicationRawJet C D a) 2 volume := by
    simpa only [Measure.restrict_univ] using
      multiplicationRawJet_periodic_compact_memL2 C hC hc D hD a
  have ht := integral_mono hp.norm.integrable_sq
    ((integrable_finsetSum Finset.univ (fun m _ => hi m)).const_mul
      (Fintype.card (PositionMask a.1.val) : ℝ))
    (fun x => multiplicationRawJet_pointwise_square_le C D a x)
  rwa [integral_const_mul, integral_finsetSum Finset.univ (fun m _ => hi m)] at ht

end AVRegularity.CycleJointProofs
end
end
