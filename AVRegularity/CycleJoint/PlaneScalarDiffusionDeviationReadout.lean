-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.CoupledWeakIdentityIntegralImageAssembly
public import AVRegularity.Statements.Intermediate.CycleJoint.HasEdgePath
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyHasDepthAtMost
import AVRegularity.CycleJoint.PeriodicOperatorLocalization
public import AVRegularity.Weighted.FluxCoordinateInjection
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

section
section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Subtracting the earlier integrated identity retains every source history at a chart seam. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem coupledWeakIdentity_restart (μ : Measure (Vec 2)) (ν a c t : ℝ)
    (hac : a ≤ c) (hct : c ≤ t) (v : ℝ → Vec 2 → Vec 2)
    (ut uc f φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (du : ℝ → Fin 2 → Vec 2 → E)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (g : ℝ → Vec 2 → E)
    (hc : CoupledWeakIdentity μ ν a c v uc f φ dφ du flux F g)
    (ht : CoupledWeakIdentity μ ν a t v ut f φ dφ du flux F g) :
    CoupledWeakIdentity μ ν c t v ut uc φ dφ du flux F g := by
  let rhs := fun s => ∫ x, weakIdentityRhs ν v φ dφ du flux F g s x ∂μ
  have hsub : Set.Ioc c t ⊆ Set.Ioc a t := fun s hs => ⟨hac.trans_lt hs.1, hs.2⟩
  have hright : IntegrableOn rhs (Set.Ioc c t) := ht.2.2.2.1.mono_set hsub
  refine ⟨ht.1, hc.1, fun s hs => ht.2.2.1 s (hsub hs), hright, ?_⟩
  have hdis : Disjoint (Set.Ioc a c) (Set.Ioc c t) := by
    apply Set.disjoint_left.mpr
    intro s hs hs'
    exact (not_lt_of_ge hs.2) hs'.1
  have hi : (∫ s in Set.Ioc a t, rhs s) =
      (∫ s in Set.Ioc a c, rhs s) + ∫ s in Set.Ioc c t, rhs s := by
    rw [← Set.Ioc_union_Ioc_eq_Ioc hac hct]
    exact setIntegral_union hdis measurableSet_Ioc hc.2.2.2.1 hright
  have hce := hc.2.2.2.2
  have hte := ht.2.2.2.2
  change (∫ x, inner ℝ (ut x) (φ x) ∂μ) - (∫ x, inner ℝ (uc x) (φ x) ∂μ) =
    ∫ s in Set.Ioc c t, rhs s
  change (∫ x, inner ℝ (uc x) (φ x) ∂μ) - (∫ x, inner ℝ (f x) (φ x) ∂μ) =
    ∫ s in Set.Ioc a c, rhs s at hce
  change (∫ x, inner ℝ (ut x) (φ x) ∂μ) - (∫ x, inner ℝ (f x) (φ x) ∂μ) =
    ∫ s in Set.Ioc a t, rhs s at hte
  rw [hi] at hte
  linarith only [hce, hte]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Local finiteness converts the physical piece sum into a measurable finite sum. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem measurable_piece_finsum_onWindow (F : ChartedFamily ι h D P Ctx)
    (tS tZ : ℝ) {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V] [MeasurableAdd₂ V]
    (f : P → Set.Icc tS tZ × Vec 2 → V)
    (hf : ∀ p, Measurable (f p))
    (hz : ∀ p z, (z.1 : ℝ) ∉ (F.piece p).output → f p z = 0) :
    Measurable (fun z => ∑ᶠ p, f p z) := by
  classical
  let s := (F.locally_finite tS tZ).toFinset
  have he (z : Set.Icc tS tZ × Vec 2) : (∑ᶠ p, f p z) = ∑ p ∈ s, f p z := by
    apply finsum_eq_sum_of_support_subset
    intro p hp
    change p ∈ (F.locally_finite tS tZ).toFinset
    rw [Set.Finite.mem_toFinset]
    have ht : (z.1 : ℝ) ∈ (F.piece p).output := by
      by_contra hout
      exact hp (hz p z hout)
    exact ⟨z.1, ht, z.1.property⟩
  simp_rw [he]
  exact Finset.measurable_sum s (fun p _ => hf p)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Genuine spatial integrability identifies the full homogeneous RHS integral with its three atoms. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem homogeneousWeakRhs_integral_readout (μ : Measure (Vec 2)) (ν s : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (du : ℝ → Fin 2 → Vec 2 → E) (flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (hd : ∀ k, Integrable (fun x => v s x k * inner ℝ (du s k x) (φ x)) μ)
    (hν : ∀ k, Integrable (fun x => inner ℝ (du s k x) (dφ k x)) μ)
    (hc : ∀ k, Integrable (fun x => inner ℝ (flux s x k) (dφ k x)) μ) :
    (∫ x, weakIdentityRhs ν v φ dφ du flux 0 0 s x ∂μ) =
      ∑ j : Fin 3, homogeneousWeakRhsIntegralAtom μ ν v φ dφ du flux j s := by
  have hi (j : Fin 3) : Integrable (homogeneousWeakRhsAtom ν v φ dφ du flux j s) μ := by
    unfold homogeneousWeakRhsAtom
    split_ifs
    · exact (integrable_finsetSum Finset.univ (fun k _ => hd k)).neg
    · exact (integrable_finsetSum Finset.univ (fun k _ => hν k)).const_mul (-ν)
    · exact (integrable_finsetSum Finset.univ (fun k _ => hc k)).neg
  rw [← homogeneousWeakRhsAtom_sum, integral_finsetSum Finset.univ (fun j _ => hi j)]
  exact Finset.sum_congr rfl (fun j _ => homogeneousWeakRhsAtom_integral μ ν s v φ dφ du flux hd hν hc j)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! Every polynomial center has an integer translate in a fixed bounded cell. -/

theorem exists_bounded_lattice_center (z : Vec 2) :
    ∃ k : Fin 2 → ℤ, ‖z - AVenhance.latticeShift k‖ ≤ 1 := by
  refine ⟨fun i => ⌊z i⌋, ?_⟩
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  change ‖z i - (⌊z i⌋ : ℝ)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Int.floor_le (z i)))]
  have hh := Int.lt_floor_add_one (z i)
  linarith only [hh]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleJointProofs

/-! Literal periodization depends only on the plane almost-everywhere class. -/

variable {E : Type*} [NormedAddCommGroup E]

theorem latticePeriodization_congr_ae {f g : Vec 2 → E} (he : f =ᵐ[volume] g) :
    latticePeriodization f =ᵐ[volume] latticePeriodization g := by
  have ht (n : Fin 2 → ℤ) :
      (fun x => f (x + AVenhance.latticeShift n)) =ᵐ[volume]
        fun x => g (x + AVenhance.latticeShift n) :=
    (measurePreserving_add_right volume (AVenhance.latticeShift n)).quasiMeasurePreserving.ae_eq_comp he
  have hall : ∀ᵐ x ∂volume, ∀ n : Fin 2 → ℤ,
      f (x + AVenhance.latticeShift n) = g (x + AVenhance.latticeShift n) :=
    ae_all_iff.mpr ht
  filter_upwards [hall] with x hx
  exact tsum_congr hx

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Zero forcing has exactly zero factorial mass energy `massNormSq`. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, MeasurableSpace (E i)]

theorem massNormSq_zero {μ : Measure (Vec 2)} (K : ι → ℕ) (ρ : ℝ) (π : ι → ℝ) :
    massNormSq (E := E) (μ := μ) (K := K) ρ π 0 = 0 := by
  simp [massNormSq, factorialNormSq, derivativeNormSq]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open MeasureTheory
namespace AVRegularity.CycleJointProofs

/-! Fixed real scaling of normed trajectories preserves continuity and time L2 integrability. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normedCurve_continuousOn_smul (c : ℝ) (f : ℝ → E) (I : Set ℝ)
    (hf : ContinuousOn f I) : ContinuousOn (fun t => c • f t) I := hf.const_smul c

theorem normedCurve_memLp_smul (c : ℝ) (f : ℝ → E) (μ : Measure ℝ)
    (hf : MemLp f 2 μ) : MemLp (fun t => c • f t) 2 μ := hf.const_smul c

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance.Infra.Torus AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The canonical covering-plane representatives are measurable everywhere. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem periodicJetRepresentative_measurable
    (D : JetL2 (volume.restrict AVenhance.unitCube) K E) (a : JetIndex2 K) :
    Measurable (periodicJetRepresentative D a) := by
  have ht : Continuous (toUnitTorus 2) := by
    unfold toUnitTorus
    fun_prop
  exact (Lp.stronglyMeasurable (D a)).measurable.comp
    ((measurable_unitTorusRepresentative 2).comp ht.measurable)

theorem torusHk_jet_measurable (w : TorusHk K E) (a : JetIndex2 K) :
    Measurable (w.toFunction.jet a) := periodicJetRepresentative_measurable w.val a

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! The family's local finiteness gives one literal finite piece sum throughout a bounded window. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}
variable {V : Type*} [AddCommMonoid V]

theorem piece_finsum_eq_window_sum (F : ChartedFamily ι h D P Ctx)
    (a b t : ℝ) (ht : t ∈ Set.Icc a b) (f : P → V)
    (hz : ∀ p, t ∉ (F.piece p).output → f p = 0) :
    (∑ᶠ p, f p) = ∑ p ∈ (F.locally_finite a b).toFinset, f p := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro p hp
  change p ∈ (F.locally_finite a b).toFinset
  rw [Set.Finite.mem_toFinset]
  have hout : t ∈ (F.piece p).output := by
    by_contra hh
    exact hp (hz p hh)
  exact ⟨t, hout, ht⟩

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Almost-everywhere finite moments admit a zero extension on the exceptional time set. -/

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

def HasRadialPlaneMoments (f : PlaneHk Set.univ K E) (z : Vec 2) : Prop :=
  ∀ a, MemLp (fun y => (1 + ‖y - z‖) ^ 4 • f.toFunction.jet a y) 2 volume

def radialMomentGoodPart (f : X → PlaneHk Set.univ K E) (z : Vec 2) (t : X) :
    PlaneHk Set.univ K E := by
  classical
  exact if HasRadialPlaneMoments (f t) z then f t else 0

theorem radialMomentGoodPart_eq (f : X → PlaneHk Set.univ K E) (z : Vec 2) (t : X)
    (ht : HasRadialPlaneMoments (f t) z) : radialMomentGoodPart f z t = f t := by
  simp only [radialMomentGoodPart, ite_eq_left ht]

theorem radialMomentGoodPart_hasMoments (f : X → PlaneHk Set.univ K E) (z : Vec 2) (t : X) :
    HasRadialPlaneMoments (radialMomentGoodPart f z t) z := by
  classical
  by_cases ht : HasRadialPlaneMoments (f t) z
  · rw [radialMomentGoodPart_eq f z t ht]
    exact ht
  · simp only [radialMomentGoodPart, ite_eq_right ht]
    intro a
    exact zeroPlaneJet_weight_memLp (fun y => (1 + ‖y - z‖) ^ 4) a

variable [MeasurableSpace X]

theorem radialMomentGoodPart_ae_eq (μ : Measure X) (f : X → PlaneHk Set.univ K E) (z : Vec 2)
    (hm : ∀ᵐ t ∂μ, HasRadialPlaneMoments (f t) z) : radialMomentGoodPart f z =ᵐ[μ] f :=
  hm.mono (fun t ht => radialMomentGoodPart_eq f z t ht)

theorem radialMomentGoodPart_memLp (μ : Measure X) (f : X → PlaneHk Set.univ K E) (z : Vec 2)
    (hf : MemLp f 2 μ) (hm : ∀ᵐ t ∂μ, HasRadialPlaneMoments (f t) z) :
    MemLp (radialMomentGoodPart f z) 2 μ :=
  hf.ae_eq (radialMomentGoodPart_ae_eq μ f z hm).symm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Fixed-reserve quadratic response estimates retain the metric and source gains separately. -/

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem shiftedResponseEnergyBudget_reserved_gain
    (a b : ℕ → ℝ≥0∞) (C η θ : ℝ≥0∞) (p N n j h : ℕ)
    (ha : ∀ k ≤ N, a k ≤ C * η ^ 2) (hb : ∀ k ≤ N, b k ≤ C * θ ^ 2)
    (hN : n + (j + h) * p ≤ N) :
    shiftedResponseEnergyBudget a b p n j h ≤
      (shiftedResponseEnergyBudget (fun _ => 1) (fun _ => 1) p n j h * C ^ (j + h)) *
        η ^ (2 * j) * θ ^ (2 * h) := by
  refine (shiftedResponseEnergyBudget_reserved_le_constant a b
    (C * η ^ 2) (C * θ ^ 2) p N n j h ha hb hN).trans_eq ?_
  rw [shiftedResponseEnergyBudget_const_homogeneous]
  simp only [mul_pow, ← pow_mul, pow_add]
  ring

theorem finiteResponse_reserved_energy_gain (M S : Module.End ℝ E)
    (energy : ℕ → E → ℝ≥0∞) (a b : ℕ → ℝ≥0∞) (C η θ : ℝ≥0∞) (p N : ℕ)
    (hadd : ∀ n x y, energy n (x + y) ≤ 2 * (energy n x + energy n y))
    (hM : ∀ n, n + p ≤ N → ∀ x, energy n (M x) ≤ a n * energy (n + p) x)
    (hS : ∀ n, n + p ≤ N → ∀ x, energy n (S x) ≤ b n * energy (n + p) x)
    (ha : ∀ k ≤ N, a k ≤ C * η ^ 2) (hb : ∀ k ≤ N, b k ≤ C * θ ^ 2)
    (f : E) (n j h : ℕ) (hN : n + (j + h) * p ≤ N) :
    energy n (finiteResponse 1 M S f j h) ≤
      ((shiftedResponseEnergyBudget (fun _ => 1) (fun _ => 1) p n j h * C ^ (j + h)) *
        η ^ (2 * j) * θ ^ (2 * h)) * energy (n + (j + h) * p) f := by
  exact (finiteResponse_reserved_energy_le M S energy a b p N hadd hM hS f n j h hN).trans
    (mul_le_mul_of_nonneg_right
      (shiftedResponseEnergyBudget_reserved_gain a b C η θ p N n j h ha hb hN) zero_le)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! The chronological response expansion counts each insertion ordering exactly once. -/

theorem responseInsertionWords_nodup (j h : ℕ) : (responseInsertionWords j h).Nodup := by
  have hinj (b : Bool) : Function.Injective (fun w : List Bool => b :: w) :=
    fun _ _ h => (List.cons.inj h).2
  induction j generalizing h with
  | zero =>
    induction h with
    | zero => simp [responseInsertionWords]
    | succ h ih =>
      rw [responseInsertionWords]
      exact List.Nodup.map (hinj true) ih
  | succ j ih =>
    induction h with
    | zero =>
      rw [responseInsertionWords]
      exact List.Nodup.map (hinj false) (ih 0)
    | succ h ihh =>
      rw [responseInsertionWords, List.nodup_append]
      refine ⟨List.Nodup.map (hinj false) (ih (h + 1)), List.Nodup.map (hinj true) ihh, ?_⟩
      intro a ha b hb
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp hb
      simp

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Actual torus Sobolev time integrability follows from its finite stored jet array. -/

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [MeasurableSpace X]

theorem torusHk_time_memLp_of_jets {K : ℕ} (μ : Measure X) (u : X → TorusHk K E)
    (hj : ∀ a, MemLp (fun t => (u t).val a) 2 μ) : MemLp u 2 μ := by
  have hv : MemLp (fun t => (u t).val) 2 μ := memLp_piLp_iff.mpr hj
  have hm : AEStronglyMeasurable u μ :=
    Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff.mp hv.aestronglyMeasurable
  exact (memLp_congr_norm hm hv.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun _ => rfl))).mpr hv

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The raw representative of the zero torus carrier vanishes on the cell almost everywhere. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem torusZero_rawJet_ae (K : ℕ) (α : JetIndex2 K) :
    (0 : TorusHk K E).toFunction.jet α =ᵐ[volume.restrict AVenhance.unitCube] 0 := by
  have hr := periodicJetRepresentative_ae (0 : TorusHk K E).val α
  exact hr.trans (by simpa using
    (Lp.coeFn_zero E 2 (volume.restrict AVenhance.unitCube)))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Summing the actual transported coefficients recovers each original native source flux once. -/

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem transportedCoeff_all_orders_flux
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (D : ℕ)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2)
    (g : ∀ r : ℕ, DerivativeWord2 r → E) (x : Vec 2) (a : Fin 2) :
    (∑ r ∈ Finset.Icc 1 D, ∑ A : DerivativeWord2 r,
      transportedCoeff K D B r A x a • g r A) =
      ∑ d ∈ Finset.Icc 2 D, ∑ I : DerivativeWord2 (d - 1), ∑ i : Fin 2,
        (K x a i * B d I i) •
          (∑ r ∈ Finset.Icc 1 (d - 1), ∑ A : DerivativeWord2 r,
            transitionT K (List.ofFn I) (List.ofFn A) x • g r A) := by
  classical
  calc
    _ = ∑ r ∈ Finset.Icc 1 D, ∑ d ∈ Finset.Icc (r + 1) D,
        ∑ I : DerivativeWord2 (d - 1), ∑ i : Fin 2,
          (K x a i * B d I i) •
            (∑ A : DerivativeWord2 r, transitionT K (List.ofFn I) (List.ofFn A) x • g r A) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact transportedCoeff_flux_expansion K D B r (g r) x a
    _ = ∑ d ∈ Finset.Icc 2 D, ∑ r ∈ Finset.Icc 1 (d - 1),
        ∑ I : DerivativeWord2 (d - 1), ∑ i : Fin 2,
          (K x a i * B d I i) •
            (∑ A : DerivativeWord2 r, transitionT K (List.ofFn I) (List.ofFn A) x • g r A) :=
      triangular_jet_order_sum D _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro I hI
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.smul_sum]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Real scaling preserves the complete integrated weak identity and its integrability clauses. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem coupledWeakIdentity_smul (μ : Measure (Vec 2)) (c ν a t : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (u f φ : Vec 2 → E)
    (dφ : Fin 2 → Vec 2 → E) (du : ℝ → Fin 2 → Vec 2 → E)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (g : ℝ → Vec 2 → E)
    (h : CoupledWeakIdentity μ ν a t v u f φ dφ du flux F g) :
    CoupledWeakIdentity μ ν a t v (c • u) (c • f) φ dφ
      (c • du) (c • flux) (c • F) (c • g) := by
  let r := weakIdentityRhs ν v φ dφ du flux F g
  have hr : weakIdentityRhs ν v φ dφ (c • du) (c • flux) (c • F) (c • g) =
      fun s x => c * r s x := by
    funext s x
    exact weakIdentityRhs_smul c ν v φ dφ du flux F g s x
  have hu : (fun x => inner ℝ ((c • u) x) (φ x)) =
      fun x => c * inner ℝ (u x) (φ x) := by
    funext x; exact real_inner_smul_left _ _ _
  have hf : (fun x => inner ℝ ((c • f) x) (φ x)) =
      fun x => c * inner ℝ (f x) (φ x) := by
    funext x; exact real_inner_smul_left _ _ _
  have ht : (fun s => ∫ x, c * r s x ∂μ) = fun s => c * ∫ x, r s x ∂μ :=
    funext (fun _ => integral_const_mul _ _)
  change Integrable _ μ ∧ Integrable _ μ ∧
    (∀ s ∈ Set.Ioc a t, Integrable
      (weakIdentityRhs ν v φ dφ (c • du) (c • flux) (c • F) (c • g) s) μ) ∧
    IntegrableOn (fun s => ∫ x,
      weakIdentityRhs ν v φ dφ (c • du) (c • flux) (c • F) (c • g) s x ∂μ)
      (Set.Ioc a t) ∧
    (∫ x, inner ℝ ((c • u) x) (φ x) ∂μ) - (∫ x, inner ℝ ((c • f) x) (φ x) ∂μ) =
      ∫ s in Set.Ioc a t, ∫ x,
        weakIdentityRhs ν v φ dφ (c • du) (c • flux) (c • F) (c • g) s x ∂μ
  rw [hu, hf, hr, ht]
  refine ⟨h.1.const_mul c, h.2.1.const_mul c,
    fun s hs => (h.2.2.1 s hs).const_mul c, h.2.2.2.1.const_mul c, ?_⟩
  rw [integral_const_mul, integral_const_mul, integral_const_mul]
  have he : (∫ x, inner ℝ (u x) (φ x) ∂μ) - (∫ x, inner ℝ (f x) (φ x) ∂μ) =
      ∫ s in Set.Ioc a t, ∫ x, r s x ∂μ := h.2.2.2.2
  rw [← mul_sub, he]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! A stationary trace with zero gradient and zero source flux satisfies the integrated identity. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem coupledWeakIdentity_stationary (μ : Measure (Vec 2)) (ν a t : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (u φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (du : ℝ → Fin 2 → Vec 2 → E)
    (flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (hpair : Integrable (fun x => inner ℝ (u x) (φ x)) μ)
    (hdu : ∀ s ∈ Set.Ioc a t, ∀ k, du s k =ᵐ[μ] 0)
    (hflux : ∀ s ∈ Set.Ioc a t, flux s =ᵐ[μ] 0) :
    CoupledWeakIdentity μ ν a t v u u φ dφ du flux 0 0 := by
  have hz : CoupledWeakIdentity μ ν a t v u u φ dφ 0 0 0 0 := by
    change Integrable _ μ ∧ Integrable _ μ ∧
      (∀ s ∈ Set.Ioc a t, Integrable (weakIdentityRhs ν v φ dφ 0 0 0 0 s) μ) ∧
      IntegrableOn (fun s => ∫ x, weakIdentityRhs ν v φ dφ 0 0 0 0 s x ∂μ) (Set.Ioc a t) ∧
      ((∫ x, inner ℝ (u x) (φ x) ∂μ) - (∫ x, inner ℝ (u x) (φ x) ∂μ) =
        ∫ s in Set.Ioc a t, ∫ x, weakIdentityRhs ν v φ dφ 0 0 0 0 s x ∂μ)
    have hr : weakIdentityRhs ν v φ dφ 0 0 0 0 = 0 := by
      funext s x
      simp only [weakIdentityRhs, WithLp.ofLp_zero, Pi.zero_apply, inner_zero_left, mul_zero,
        add_zero, Finset.sum_const_zero, neg_zero, sub_zero]
    rw [hr]
    refine ⟨hpair, hpair, fun _ _ => integrable_zero _ _ _, ?_, ?_⟩
    · simpa only [Pi.zero_apply, integral_zero] using integrableOn_zero
    · simp only [sub_self, Pi.zero_apply, integral_zero]
  apply coupledWeakIdentity_integrands_congr μ ν a t v v u u u u φ φ dφ dφ
    0 du 0 flux 0 0 0 0 Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl _ hz
  intro s hs
  exact weakIdentityRhs_congr_ae μ ν s v v φ φ dφ dφ 0 du 0 flux 0 0 0 0
    Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl (fun _ => Filter.EventuallyEq.rfl)
    (fun k => (hdu s hs k).symm) (hflux s hs).symm
    Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleJointProofs

/-! Replacing a test by its almost-everywhere Sobolev representatives preserves the weak identity. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem coupledWeakIdentity_test_congr (μ : Measure (Vec 2)) (ν a t : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (u f φ φ' : Vec 2 → E)
    (dφ dφ' : Fin 2 → Vec 2 → E) (du : ℝ → Fin 2 → Vec 2 → E)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (g : ℝ → Vec 2 → E)
    (hφ : φ =ᵐ[μ] φ') (hdφ : ∀ k, dφ k =ᵐ[μ] dφ' k)
    (h : CoupledWeakIdentity μ ν a t v u f φ dφ du flux F g) :
    CoupledWeakIdentity μ ν a t v u f φ' dφ' du flux F g := by
  apply coupledWeakIdentity_integrands_congr μ ν a t v v u u f f φ φ' dφ dφ'
    du du flux flux F F g g _ _ _ h
  · filter_upwards [hφ] with x hx
    rw [hx]
  · filter_upwards [hφ] with x hx
    rw [hx]
  · intro s _
    exact weakIdentityRhs_congr_ae μ ν s v v φ φ' dφ dφ' du du flux flux F F g g
      Filter.EventuallyEq.rfl hφ hdφ (fun _ => Filter.EventuallyEq.rfl)
      Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Time almost-everywhere source readouts suffice once spatial integrability is retained at every time. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem coupledWeakIdentity_time_ae_rhs_congr (μ : Measure (Vec 2)) (ν a t : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (u f φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (du : ℝ → Fin 2 → Vec 2 → E)
    (flux F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (g : ℝ → Vec 2 → E)
    (hF : ∀ᵐ s ∂volume.restrict (Set.Ioc a t), F s =ᵐ[μ] F' s)
    (hi : ∀ s ∈ Set.Ioc a t, Integrable (weakIdentityRhs ν v φ dφ du flux F' g s) μ)
    (hs : CoupledWeakIdentity μ ν a t v u f φ dφ du flux F g) :
    CoupledWeakIdentity μ ν a t v u f φ dφ du flux F' g := by
  have heq : (fun s => ∫ x, weakIdentityRhs ν v φ dφ du flux F g s x ∂μ) =ᵐ[
      volume.restrict (Set.Ioc a t)]
      (fun s => ∫ x, weakIdentityRhs ν v φ dφ du flux F' g s x ∂μ) := by
    filter_upwards [hF] with s hFs
    apply integral_congr_ae
    exact weakIdentityRhs_congr_ae μ ν s v v φ φ dφ dφ du du flux flux F F' g g
      Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl (fun _ => Filter.EventuallyEq.rfl)
      (fun _ => Filter.EventuallyEq.rfl) Filter.EventuallyEq.rfl hFs Filter.EventuallyEq.rfl
  exact ⟨hs.1, hs.2.1, hi, hs.2.2.2.1.congr heq,
    hs.2.2.2.2.trans (integral_congr_ae heq)⟩

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Global weak jets restrict to arbitrary domains without a boundary assumption. -/

theorem weakPartialDeriv_restrict {i : Fin 2} {u g : Vec 2 → ℝ}
    (h : HasWeakPartialDerivOn Set.univ i u g) (U : Set (Vec 2)) :
    HasWeakPartialDerivOn U i u g := by
  intro φ hφ hc hs
  have he := h φ hφ hc (Set.subset_univ _)
  simp only [Measure.restrict_univ] at he
  have hn (x : Vec 2) (hx : x ∉ U) : x ∉ tsupport φ := fun hh => hx (hs hh)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    rw [fderiv_of_notMem_tsupport ℝ (hn x hx)]
    simp), setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hz : φ x = 0 := by
        by_contra hh
        exact hn x hx (subset_closure hh)
      rw [hz, mul_zero])]
  exact he

theorem orderedWeakJet_restrict {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {K : ℕ} {D : RawJet2 K E}
    (h : HasOrderedWeakJetOn Set.univ D) (U : Set (Vec 2)) : HasOrderedWeakJetOn U D := by
  intro j w i e
  exact weakPartialDeriv_restrict (h j w i e) U

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! Product and finite-sum rules for the exact inverse-chart coordinate differential operator. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem weightedCoordinateDerivative_smul
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2)
    (c : Vec 2 → ℝ) (g : Vec 2 → E) (y : Vec 2)
    (hc : DifferentiableAt ℝ c y) (hg : DifferentiableAt ℝ g y) :
    weightedCoordinateDerivative K i (fun x => c x • g x) y =
      weightedCoordinateDerivative K i c y • g y +
        c y • weightedCoordinateDerivative K i g y := by
  rw [weightedCoordinateDerivative_eq, weightedCoordinateDerivative_eq,
    weightedCoordinateDerivative_eq, fderiv_fun_smul hc hg]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply]
  exact add_comm _ _

theorem weightedCoordinateDerivative_sum {α : Type*}
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2)
    (s : Finset α) (g : α → Vec 2 → E) (y : Vec 2)
    (hg : ∀ a ∈ s, DifferentiableAt ℝ (g a) y) :
    weightedCoordinateDerivative K i (fun x => ∑ a ∈ s, g a x) y =
      ∑ a ∈ s, weightedCoordinateDerivative K i (g a) y := by
  rw [weightedCoordinateDerivative_eq, fderiv_fun_sum hg]
  simp only [sum_apply, weightedCoordinateDerivative_eq]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! A bounded radius times mesh size gives a uniform finite-order Leibniz price. -/

theorem factorialWeight_mesh_reserve (ρ s L : ℝ) (hρ : 0 ≤ ρ) (hs : 0 ≤ s)
    (hL : 1 ≤ L) (hmesh : ρ * s ≤ L) {l r K : ℕ} (hl : l ≤ K) :
    factorialWeight ρ (l + r) * s ^ (2 * l) ≤
      L ^ (2 * K) * factorialWeight ρ r := by
  have hp : (ρ * s) ^ (2 * l) ≤ L ^ (2 * K) :=
    (pow_le_pow_left₀ (mul_nonneg hρ hs) hmesh (2 * l)).trans
      (pow_le_pow_right₀ hL (Nat.mul_le_mul_left 2 hl))
  exact (factorialWeight_mesh_price ρ s l r).trans
    (mul_le_mul_of_nonneg_right hp (factorialWeight_nonneg ρ r))

theorem factorialWeight_mask_mesh_reserve (ρ s L : ℝ) (hρ : 0 ≤ ρ) (hs : 0 ≤ s)
    (hL : 1 ≤ L) (hmesh : ρ * s ≤ L) {j K : ℕ} (hj : j ≤ K) (m : PositionMask j) :
    factorialWeight ρ j * s ^ (2 * maskLeftLength j m) ≤
      L ^ (2 * K) * factorialWeight ρ (maskRightLength j m) := by
  have ht := factorialWeight_mesh_reserve ρ s L hρ hs hL hmesh
    ((maskLeftLength_le j m).trans hj) (r := maskRightLength j m)
  rwa [mask_lengths_add] at ht

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.CycleJointProofs

/-! Exact finite orthonormal decomposition of native spatial L2 classes. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem finiteHilbert_L2_basis_decomposition (μ : Measure (Vec 2)) (u : Lp E 2 μ) :
    let b := stdOrthonormalBasis ℝ E
    (∑ k : Fin (Module.finrank ℝ E),
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (b k)).compLpL 2 μ
        ((innerSL ℝ (b k)).compLpL 2 μ u)) = u := by
  let b := stdOrthonormalBasis ℝ E
  let P := fun k => (innerSL ℝ (b k)).compLpL 2 μ
  let L := fun k => ((ContinuousLinearMap.id ℝ ℝ).smulRight (b k)).compLpL 2 μ
  change (∑ k, L k (P k u)) = u
  apply Lp.ext
  have hP : ∀ᵐ x ∂μ, ∀ k, P k u x = inner ℝ (b k) (u x) :=
    ae_all_iff.mpr fun k => ContinuousLinearMap.coeFn_compLpL (innerSL ℝ (b k)) u
  have hL : ∀ᵐ x ∂μ, ∀ k, L k (P k u) x = (P k u x) • b k :=
    ae_all_iff.mpr fun k => ContinuousLinearMap.coeFn_compLpL
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (b k)) (P k u)
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun k => L k (P k u)), hP, hL] with x hs hp hl
  rw [hs, Finset.sum_apply]
  simp_rw [hl, hp]
  exact b.sum_repr' (u x)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Spatial smoothness of a locally finite piece sum on a fixed observation window. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem piece_finsum_spatial_smooth_onWindow (F : ChartedFamily ι h D P Ctx)
    (tS tZ : ℝ) {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : P → ℝ → Vec 2 → V) (n : ℕ)
    (hf : ∀ p t, t ∈ Set.Icc tS tZ → ContDiff ℝ (n : ℕ) (f p t))
    (hz : ∀ p t x, t ∉ (F.piece p).output → f p t x = 0)
    (t : ℝ) (ht : t ∈ Set.Icc tS tZ) :
    ContDiff ℝ (n : ℕ) (fun x => ∑ᶠ p, f p t x) := by
  classical
  let s := (F.locally_finite tS tZ).toFinset
  have he (x : Vec 2) : (∑ᶠ p, f p t x) = ∑ p ∈ s, f p t x := by
    apply finsum_eq_sum_of_support_subset
    intro p hp
    change p ∈ (F.locally_finite tS tZ).toFinset
    rw [Set.Finite.mem_toFinset]
    have ht' : t ∈ (F.piece p).output := by
      by_contra hout
      exact hp (hz p t x hout)
    exact ⟨t, ht', ht⟩
  simp_rw [he]
  exact ContDiff.sum (fun p _ => hf p t ht)
end

/-! A finite source derivative row on genuine native carriers has its original order-indexed readout. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def nativeSourceScalarJetCoefficient {K : ℕ} (D : ℕ)
    (B : ∀ r : ℕ, DerivativeWord2 r → Vec 2 → Vec 2)
    (i : Fin 2) (j : JetIndex2 K) (y : Vec 2) : ℝ :=
  if 1 ≤ j.1.val ∧ j.1.val < D then B j.1.val j.2 y i else 0

theorem nativeSourceScalarJetCoefficient_flux {K : ℕ} (D : ℕ) (hD : D ≤ K + 1)
    (B : ∀ r : ℕ, DerivativeWord2 r → Vec 2 → Vec 2)
    (u : Vec 2 → E) (y : Vec 2) (i : Fin 2) :
    (∑ j : JetIndex2 K, nativeSourceScalarJetCoefficient D B i j y •
      orderedDerivative j.2 u y) =
      ∑ d ∈ Finset.Icc 2 D, ∑ I : DerivativeWord2 (d - 1),
        B (d - 1) I y i • orderedDerivative I u y := by
  classical
  simp only [nativeSourceScalarJetCoefficient, ite_smul, zero_smul]
  rw [nativeJet_source_order_sum K D hD
    (fun r A => B r A y i • orderedDerivative A u y)]
  exact native_source_order_shift D _
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! A finite, nonempty and correctly graded index set for the actual response word solves. -/

def responseWordSet (j h : ℕ) : Finset (List Bool) := (responseInsertionWords j h).toFinset

theorem mem_responseWordSet_iff (j h : ℕ) (w : List Bool) :
    w ∈ responseWordSet j h ↔ w.length = j + h ∧ w.count true = h := by
  rw [responseWordSet, List.mem_toFinset, mem_responseInsertionWords_iff]

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem nodup_word_sum_eq_finset_sum (ws : List (List Bool)) (hw : ws.Nodup)
    (T : List Bool → Module.End ℝ E) : (ws.map T).sum = ∑ w ∈ ws.toFinset, T w := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    obtain ⟨hnot, hn⟩ := List.nodup_cons.mp hw
    have hm : w ∉ ws.toFinset := by simpa using hnot
    rw [List.map_cons, List.sum_cons, List.toFinset_cons, Finset.sum_insert hm, ih hn]

theorem finiteResponseOperator_eq_responseWordSet_sum (R D S : Module.End ℝ E) (j h : ℕ) :
    finiteResponseOperator R D S j h = ∑ w ∈ responseWordSet j h, responseWordOperator R D S w := by
  rw [finiteResponseOperator_eq_word_sum]
  exact nodup_word_sum_eq_finset_sum _ (responseInsertionWords_nodup j h) _

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! Lattice product weights are controlled by the distance of a translated point. -/

theorem spatialLatticeWeight_le_shift_norm (n : Fin 2 → ℤ) :
    spatialLatticeWeight n ≤ (1 + ‖AVenhance.latticeShift n‖) ^ 2 := by
  have hc (i : Fin 2) : |(n i : ℝ)| ≤ ‖AVenhance.latticeShift n‖ := by
    simpa only [AVenhance.latticeShift, Real.norm_eq_abs] using
      norm_le_pi_norm (AVenhance.latticeShift n) i
  unfold spatialLatticeWeight
  calc
    (1 + |(n 0 : ℝ)|) * (1 + |(n 1 : ℝ)|) ≤
        (1 + ‖AVenhance.latticeShift n‖) * (1 + ‖AVenhance.latticeShift n‖) :=
      mul_le_mul (add_le_add (le_refl 1) (hc 0)) (add_le_add (le_refl 1) (hc 1))
        (by positivity) (by positivity)
    _ = _ := by ring

theorem spatialLatticeWeight_le_translated_norm (n : Fin 2 → ℤ) (x z : Vec 2) :
    spatialLatticeWeight n ≤
      (1 + ‖x‖ + ‖z‖ + ‖x + AVenhance.latticeShift n - z‖) ^ 2 := by
  have he : AVenhance.latticeShift n = (x + AVenhance.latticeShift n - z) - x + z := by
    abel
  have hn : ‖AVenhance.latticeShift n‖ ≤ ‖x + AVenhance.latticeShift n - z‖ + ‖x‖ + ‖z‖ := by
    calc
      ‖AVenhance.latticeShift n‖ = ‖(x + AVenhance.latticeShift n - z) - x + z‖ := congrArg norm he
      _ ≤ ‖(x + AVenhance.latticeShift n - z) - x‖ + ‖z‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (norm_sub_le _ _) (le_refl _)
  apply (spatialLatticeWeight_le_shift_norm n).trans
  apply pow_le_pow_left₀ (by positivity)
  linarith

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Translating a genuine global plane weak jet retains all its derivative identities. -/

theorem weakPartialDeriv_translate {i : Fin 2} {u g : Vec 2 → ℝ}
    (h : HasWeakPartialDerivOn Set.univ i u g) (a : Vec 2) :
    HasWeakPartialDerivOn Set.univ i (fun x => u (x + a)) (fun x => g (x + a)) := by
  intro φ hφ hc _
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => φ (y - a)) :=
    hφ.comp (contDiff_id.sub contDiff_const)
  have hcψ : HasCompactSupport (fun y : Vec 2 => φ (y - a)) := by
    have hh := hc.comp_homeomorph (Homeomorph.addRight (-a))
    change HasCompactSupport (fun y => φ (y + -a)) at hh
    simpa only [sub_eq_add_neg] using hh
  have he := h (fun y => φ (y - a)) hψ hcψ (Set.subset_univ _)
  simp only [Measure.restrict_univ, fderiv_comp_sub] at he ⊢
  have hi := integral_add_right_eq_self (μ := (volume : Measure (Vec 2)))
    (fun y : Vec 2 => u y * (fderiv ℝ φ (y - a)) (basisVec i)) a
  have hj := integral_add_right_eq_self (μ := (volume : Measure (Vec 2))) (fun y : Vec 2 => g y * φ (y - a)) a
  simp only [add_sub_cancel_right] at hi hj
  rw [hi, hj]
  exact he

theorem orderedWeakJet_translate {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {K : ℕ} {D : RawJet2 K E}
    (h : HasOrderedWeakJetOn Set.univ D) (a : Vec 2) :
    HasOrderedWeakJetOn Set.univ (fun b x => D b (x + a)) := by
  intro j w i e
  exact weakPartialDeriv_translate (h j w i e) a

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Finite coefficient arrays are continuous in the physical variable. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem coefficientDerivativeArray_continuous (C : Vec 2 → E →L[ℝ] F)
    (j : ℕ) (hC : ContDiff ℝ (j : ℕ) C) :
    Continuous (fun x => coefficientDerivativeArray C j x) := by
  apply continuous_clm_apply.mpr
  intro z
  have hp : Continuous (fun x => fun w : DerivativeWord2 j =>
      orderedCoefficientDerivative C j w x z) := by
    apply continuous_pi
    intro w
    exact ((orderedCoefficientDerivative_contDiff C j 0
      (by simpa only [Nat.add_zero] using hC) w).continuous).clm_apply continuous_const
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : DerivativeWord2 j => F)).symm.continuous.comp hp
end

/-! Constant scalar multiplication commutes with literal ordered coefficient arrays. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Constant scalar multiplication commutes with every ordered coefficient derivative. -/
theorem orderedCoefficientDerivative_const_smul (c : ℝ) (C : Vec 2 → E →L[ℝ] F)
    (j : ℕ) (w : DerivativeWord2 j) :
    orderedCoefficientDerivative (fun x => c • C x) j w =
      fun x => c • orderedCoefficientDerivative C j w x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [orderedCoefficientDerivative, ih]
    change (fun x => fderiv ℝ (c • orderedCoefficientDerivative C j (Fin.init w)) x
      (basisVec (w (Fin.last j)))) = _
    funext x
    rw [congrFun (fderiv_const_smul_field (𝕜 := ℝ)
      (f := orderedCoefficientDerivative C j (Fin.init w)) c) x]
    rfl

/-- The complete ordered coefficient array preserves constant scalar multiplication. -/
theorem coefficientDerivativeArray_const_smul (c : ℝ) (C : Vec 2 → E →L[ℝ] F)
    (j : ℕ) (x : Vec 2) :
    coefficientDerivativeArray (fun y => c • C y) j x = c • coefficientDerivativeArray C j x := by
  apply ContinuousLinearMap.ext
  intro z
  apply PiLp.ext
  intro w
  simp only [coefficientDerivativeArray_apply, orderedCoefficientDerivative_const_smul,
    smul_apply, PiLp.smul_apply]
end

end AVRegularity.CycleJointProofs
end
end

section
public section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Native coefficient arrays commute exactly with spatial translation. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem orderedCoefficientDerivative_comp_translation (C : Vec 2 → E →L[ℝ] F)
    (y : Vec 2) (j : ℕ) : ∀ (w : DerivativeWord2 j) (x : Vec 2),
    orderedCoefficientDerivative (fun z => C (z + y)) j w x =
      orderedCoefficientDerivative C j w (x + y) := by
  induction j with
  | zero => intro w x; rfl
  | succ j ih =>
    intro w x
    change fderiv ℝ (orderedCoefficientDerivative (fun z => C (z + y)) j (Fin.init w))
      x (basisVec (w (Fin.last j))) =
      fderiv ℝ (orderedCoefficientDerivative C j (Fin.init w)) (x + y)
        (basisVec (w (Fin.last j)))
    have hh := funext (ih (Fin.init w))
    rw [hh, fderiv_comp_add_right]

theorem coefficientDerivativeArray_comp_translation (C : Vec 2 → E →L[ℝ] F)
    (y : Vec 2) (j : ℕ) (x : Vec 2) :
    coefficientDerivativeArray (fun z => C (z + y)) j x =
      coefficientDerivativeArray C j (x + y) := by
  ext u w
  change orderedCoefficientDerivative (fun z => C (z + y)) j w x u =
    orderedCoefficientDerivative C j w (x + y) u
  rw [orderedCoefficientDerivative_comp_translation]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Every literal ordered derivative of a compact coefficient remains compactly supported. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem orderedCoefficientDerivative_compact (C : Vec 2 → E →L[ℝ] F)
    (hc : HasCompactSupport C) (n : ℕ) (w : DerivativeWord2 n) :
    HasCompactSupport (orderedCoefficientDerivative C n w) := by
  induction n with
  | zero => exact hc
  | succ n ih => exact (ih (Fin.init w)).fderiv_apply (𝕜 := ℝ) (basisVec (w (Fin.last n)))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! The declared source depth excludes every longer chronological edge path. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem not_hasEdgePath_of_depth {F : ChartedFamily ι h D P Ctx} {H n : ℕ}
    (hdepth : F.HasDepthAtMost H) (hn : H < n) (u v : ι) : ¬ HasEdgePath F n u v := by
  rintro ⟨p, _, _, hp⟩
  have hlen : H + 2 ≤ n + 1 := by omega
  have hstep : H + 1 ≤ n := by omega
  let q : Fin (H + 2) → ι := fun k => p (Fin.castLE hlen k)
  obtain ⟨k, hk⟩ := hdepth q
  have he : Nonempty (F.Γ (q k.succ) (q k.castSucc)) := by
    exact hp (Fin.castLE hstep k)
  exact hk.false he.some

end AVRegularity.CycleJointProofs
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Compact coefficient localization preserves the actual periodic ordered weak jets. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem multiplicationRawJet_periodic_compact_memL2 {K : ℕ}
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C) (hc : HasCompactSupport C)
    (D : RawJet2 K E) (hD : HasPeriodicOrderedWeakJet D) :
    JetMemL2On Set.univ (multiplicationRawJet C D) := by
  intro a
  simp only [Measure.restrict_univ]
  unfold multiplicationRawJet
  apply memLp_finsetSum
  intro m _
  let l := maskLeftLength a.1.val m
  let w := (maskWordEquiv 2 a.1.val m a.2).1
  have hle : l ≤ K := (maskLeftLength_le a.1.val m).trans (Nat.le_of_lt_succ a.1.isLt)
  have hCl : ContDiff ℝ (l + 0 : ℕ) C := hC.of_le (by exact_mod_cast (by omega : l + 0 ≤ K))
  exact periodic_compact_operator_memLp (D (maskJetIndex (Nat.le_of_lt_succ a.1.isLt) m a.2))
    (hD.2.1 _) (hD.1 _) (orderedCoefficientDerivative C l w)
    (orderedCoefficientDerivative_contDiff C l 0 hCl w).continuous
    (orderedCoefficientDerivative_compact C hc l w)

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

def localizePeriodicCoefficient {K : ℕ} (w : TorusHkFunction K E)
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C) (hc : HasCompactSupport C) :
    PlaneHkFunction Set.univ K F where
  jet := multiplicationRawJet C w.jet
  memL2 := multiplicationRawJet_periodic_compact_memL2 C hC hc w.jet w.hasPeriodicWeakJet
  hasWeakJet := multiplicationRawJet_hasOrderedWeakJetOn hC w.hasPeriodicWeakJet.2.2
    (periodicJet_scalar_locallyIntegrable w.hasPeriodicWeakJet)
end

/-! Each literal Leibniz term of a compact coefficient localizes periodic weak jets. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem periodic_compact_multiplicationTerm_memLp {K j : ℕ} (hj : j ≤ K)
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C)
    (hc : HasCompactSupport C) (D : RawJet2 K E)
    (hD : HasPeriodicOrderedWeakJet D) (m : PositionMask j) (w : DerivativeWord2 j) :
    MemLp (multiplicationTerm hj C D m w) 2 volume := by
  let l := maskLeftLength j m
  let v := (maskWordEquiv 2 j m w).1
  have hle : l ≤ K := (maskLeftLength_le j m).trans hj
  have hCl : ContDiff ℝ (l + 0 : ℕ) C :=
    hC.of_le (by exact_mod_cast (by omega : l + 0 ≤ K))
  exact periodic_compact_operator_memLp (D (maskJetIndex hj m w))
    (hD.2.1 _) (hD.1 _) (orderedCoefficientDerivative C l v)
    (orderedCoefficientDerivative_contDiff C l 0 hCl v).continuous
    (orderedCoefficientDerivative_compact C hc l v)
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The diffusion deviation reads the literal matrix difference from the identity on actual L2 gradients. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

theorem planeScalarDiffusion_deviation_ae
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hc : ∀ k j, Continuous (fun x => G x k j))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ k j x, |G x k j| ≤ M)
    (du : PlaneFluxL2 E) (k : Fin 2) :
    ((planeScalarDiffusion (E := E) G hc hM hb - ContinuousLinearMap.id ℝ (PlaneFluxL2 E)) du k)
      =ᵐ[volume] fun x => ∑ j : Fin 2,
        (G x k j - if k = j then 1 else 0) • du j x := by
  filter_upwards [Lp.coeFn_sub (planeScalarDiffusion G hc hM hb du k) (du k),
    planeScalarDiffusion_ae G hc hM hb du k] with x hs hd
  have he : (∑ j : Fin 2, G x k j • du j x) - du k x =
      ∑ j : Fin 2, (G x k j - if k = j then 1 else 0) • du j x := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    congr 1
    simp only [ite_smul, one_smul, zero_smul]
    simp
  exact hs.trans ((congrArg (fun e : E => e - du k x) hd).trans he)

end AVRegularity.CycleJointProofs
end
end
