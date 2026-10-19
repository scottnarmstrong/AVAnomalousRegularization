-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PeriodicMultiplicationJetEnergy
import AVRegularity.CycleJoint.PlaneScalarDiffusionDeviationReadout
public import AVRegularity.Statements.Intermediate.CoupledEnergy.SchurMatrix
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsTimeMeasurable
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyHasDepthAtMost
public import AVRegularity.Statements.Intermediate.Families.ConstituentPhysical
public import AVRegularity.Weighted.PlaneJetFluxOperator
public import AVRegularity.CycleReference.SpacetimeGradientPairing

section
section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Time-a.e. total-flux readouts preserve the full weak equation when their spatial L2 bounds hold. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem coupledWeakIdentity_time_ae_total_flux_congr (μ : Measure (Vec 2)) (ν a t : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (u f φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (du : ℝ → Fin 2 → Vec 2 → E)
    (flux flux' F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (g : ℝ → Vec 2 → E)
    (hdφ : ∀ k, MemLp (dφ k) 2 μ)
    (hF : ∀ s ∈ Set.Ioc a t, ∀ k, MemLp (fun x => (flux s x + F s x) k) 2 μ)
    (hF' : ∀ s ∈ Set.Ioc a t, ∀ k, MemLp (fun x => (flux' s x + F' s x) k) 2 μ)
    (heq : ∀ᵐ s ∂volume.restrict (Set.Ioc a t),
      (fun x => flux s x + F s x) =ᵐ[μ] fun x => flux' s x + F' s x)
    (hs : CoupledWeakIdentity μ ν a t v u f φ dφ du flux F g) :
    CoupledWeakIdentity μ ν a t v u f φ dφ du flux' F' g := by
  let Z : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E) := fun _ _ => 0
  have hzero : CoupledWeakIdentity μ ν a t v u f φ dφ du Z
      (fun s x => flux s x + F s x) g := by
    apply coupledWeakIdentity_flux_reallocation μ ν a t v u f φ dφ du flux Z F _ g _ hs
    intro s _
    exact Filter.Eventually.of_forall (fun x => by simp only [Z, zero_add])
  have hnew := coupledWeakIdentity_time_ae_forcing_congr μ ν a t v u f φ dφ du Z
    (fun s x => flux s x + F s x) (fun s x => flux' s x + F' s x) g hdφ hF hF' heq hzero
  apply coupledWeakIdentity_flux_reallocation μ ν a t v u f φ dφ du Z flux'
    (fun s x => flux' s x + F' s x) F' g _ hnew
  intro s _
  exact Filter.Eventually.of_forall (fun x => by simp only [Z, zero_add])

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Zero coefficients have zero literal seminorm, including every derivative order. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem coefficientDerivativeArray_zero_function (j : ℕ) (x : Vec 2) :
    coefficientDerivativeArray (fun _ : Vec 2 => (0 : E →L[ℝ] F)) j x = 0 := by
  apply ContinuousLinearMap.ext
  intro z
  apply PiLp.ext
  intro w
  simp [coefficientDerivativeArray, Weighted.orderedCoefficientDerivative_zero_function]

theorem coefficientSeminorm_zero_function (ρ : ℝ) (K : ℕ) (a b : ℝ) :
    coefficientSeminorm ρ K a b (fun _ _ => (0 : E →L[ℝ] F)) = 0 := by
  simp [coefficientSeminorm, coefficientDerivativeArray_zero_function]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Actual cell L2 representatives have integrable bounded-coefficient weak pairings. -/

variable {E F X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace X]

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
theorem integrable_inner_of_memLp_two (μ : Measure X) (f g : X → E)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => inner ℝ (f x) (g x)) μ := by
  have hi := L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)
  apply hi.congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]

omit [MeasurableSpace X] in
theorem cell_coefficient_pairing_integrable (f : Vec 2 → E) (g : Vec 2 → F)
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube))
    (hg : MemLp g 2 (volume.restrict AVenhance.unitCube))
    (C : Vec 2 → E →L[ℝ] F) (hc : Continuous C) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ x, ‖C x‖ ≤ M) :
    Integrable (fun x => inner ℝ (C x (f x)) (g x)) (volume.restrict AVenhance.unitCube) := by
  exact integrable_inner_of_memLp_two _ _ _ (memLp_operator_mul hc hf hM hb) hg

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! A finite retained response has one uniform initial-reserve price when the metric insertion gain is at most one. -/

def retainedResponseEnergyPrice (C θ : ℝ≥0∞) (J H : ℕ) : ℝ≥0∞ :=
  2 ^ (J + 1) * ∑ j ∈ Finset.range (J + 1), terminalResponseEnergyPrice C θ j H

theorem retainedResponseEnergyPrice_ne_top (C θ : ℝ≥0∞) (hC : C ≠ ⊤) (hθ : θ ≠ ⊤)
    (J H : ℕ) : retainedResponseEnergyPrice C θ J H ≠ ⊤ := by
  apply ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
  apply ENNReal.sum_ne_top.mpr
  intro j _
  exact terminalResponseEnergyPrice_ne_top C θ hC hθ j H

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem finiteResponse_retained_energy_gain (M S : Module.End ℝ E)
    (energy : ℕ → E → ℝ≥0∞) (a b : ℕ → ℝ≥0∞) (C η θ : ℝ≥0∞) (p N : ℕ)
    (hz : ∀ n, energy n 0 = 0)
    (hadd : ∀ n x y, energy n (x + y) ≤ 2 * (energy n x + energy n y))
    (hM : ∀ n, n + p ≤ N → ∀ x, energy n (M x) ≤ a n * energy (n + p) x)
    (hS : ∀ n, n + p ≤ N → ∀ x, energy n (S x) ≤ b n * energy (n + p) x)
    (ha : ∀ k ≤ N, a k ≤ C * η ^ 2) (hb : ∀ k ≤ N, b k ≤ C * θ ^ 2)
    (hη : η ≤ 1) (f : E) (G0 : ℝ≥0∞) (hinit : ∀ k ≤ N, energy k f ≤ G0)
    (n J H : ℕ) (hN : n + (J + H) * p ≤ N) :
    energy n (∑ j ∈ Finset.range (J + 1),
      ∑ h ∈ Finset.range (H + 1), finiteResponse 1 M S f j h) ≤
      retainedResponseEnergyPrice C θ J H * G0 := by
  refine (finite_quadratic_energy_sum_le (energy n) (hz n) (hadd n) _ _).trans ?_
  simp only [Finset.card_range]
  calc
    2 ^ (J + 1) * ∑ j ∈ Finset.range (J + 1),
        energy n (∑ h ∈ Finset.range (H + 1), finiteResponse 1 M S f j h) ≤
      2 ^ (J + 1) * ∑ j ∈ Finset.range (J + 1), terminalResponseEnergyPrice C θ j H * G0 := by
      apply mul_le_mul_of_nonneg_left _ zero_le
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j ≤ J := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hk : n + (j + H) * p ≤ N :=
        (Nat.add_le_add_left (Nat.mul_le_mul_right p (Nat.add_le_add_right hj' H)) n).trans hN
      have he := finiteResponse_terminal_energy_gain M S energy a b C η θ p N hz hadd
        hM hS ha hb f G0 hinit n j H hk
      have hp : η ^ (2 * j) ≤ 1 := by
        simpa only [one_pow] using pow_le_pow_left' hη (2 * j)
      exact he.trans (mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left hp zero_le).trans_eq (mul_one _)) zero_le)
    _ = retainedResponseEnergyPrice C θ J H * G0 := by
      rw [← Finset.sum_mul]
      unfold retainedResponseEnergyPrice
      ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Explicit first-order Leibniz readout for localized torus weak tests. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem multiplicationRawJet_first (C : Vec 2 → E →L[ℝ] F)
    (D : RawJet2 1 E) (k : Fin 2) (x : Vec 2) :
    multiplicationRawJet C D ⟨⟨1, by decide⟩, fun _ => k⟩ x =
      C x (D ⟨⟨1, by decide⟩, fun _ => k⟩ x) +
        fderiv ℝ C x (basisVec k) (D (valueIndex2 1) x) := by
  change (∑ m : PUnit × Bool,
    multiplicationTerm (by decide : 1 ≤ 1) C D m (Fin.snoc Fin.elim0 k) x) = _
  rw [Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool]
  rw [multiplicationTerm_snoc_true (by decide : 0 < 1),
    multiplicationTerm_snoc_false (by decide : 0 < 1)]
  simp only [orderedCoefficientDerivative_zero]
  exact add_comm _ _

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! Source grading keeps the original identity graph while allowing operators on actual native curve carriers. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

def HasSourceDegreeOn (F : ChartedFamily ι h D P Ctx) (n : ℕ)
    (T : Module.End ℝ (∀ i, V i)) : Prop :=
  ∀ (f : ∀ i, V i) v, (∀ u, HasEdgePath F n u v → f u = 0) → (T f) v = 0

theorem sourceDegreeOn_mul {F : ChartedFamily ι h D P Ctx} {a b : ℕ}
    {S T : Module.End ℝ (∀ i, V i)} (hS : HasSourceDegreeOn F a S) (hT : HasSourceDegreeOn F b T) :
    HasSourceDegreeOn F (a + b) (S * T) := by
  intro f v hf
  change (S (T f)) v = 0
  apply hS
  intro k hk
  apply hT
  intro u hu
  apply hf u
  simpa only [Nat.add_comm b a] using hasEdgePath_concat hu hk

theorem sourceDegreeOn_add {F : ChartedFamily ι h D P Ctx} {n : ℕ}
    {S T : Module.End ℝ (∀ i, V i)} (hS : HasSourceDegreeOn F n S) (hT : HasSourceDegreeOn F n T) :
    HasSourceDegreeOn F n (S + T) := by
  intro f v hf
  change (S f) v + (T f) v = 0
  rw [hS f v hf, hT f v hf, zero_add]

theorem sourceDegreeOn_gt_depth_zero {F : ChartedFamily ι h D P Ctx} {H n : ℕ}
    (hdepth : F.HasDepthAtMost H) (hn : H < n) {T : Module.End ℝ (∀ i, V i)}
    (hT : HasSourceDegreeOn F n T) : T = 0 := by
  ext f v
  exact hT f v (fun u hu => (not_hasEdgePath_of_depth hdepth hn u v hu).elim)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Measure-preserving translation acts on every genuine plane Sobolev jet. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

def planeComponentTranslation (z : Vec 2) :
    ComponentL2 (volume.restrict Set.univ) E →ₗᵢ[ℝ] ComponentL2 (volume.restrict Set.univ) E :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x : Vec 2 => x + z)
    (by simpa only [Measure.restrict_univ] using measurePreserving_add_right volume z)

def planeJetTranslation (K : ℕ) (z : Vec 2) :
    JetL2 (volume.restrict Set.univ) K E →L[ℝ] JetL2 (volume.restrict Set.univ) K E :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : JetIndex2 K => ComponentL2 (volume.restrict Set.univ) E)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun a => (planeComponentTranslation z).toContinuousLinearMap.comp
      (PiLp.proj 2 (fun _ : JetIndex2 K => ComponentL2 (volume.restrict Set.univ) E) a)))

omit [BorelSpace E] [CompleteSpace E] in
theorem planeJetTranslation_component_ae (z : Vec 2)
    (D : JetL2 (volume.restrict Set.univ) K E) (a : JetIndex2 K) :
    planeJetTranslation K z D a =ᵐ[volume.restrict Set.univ] fun x => D a (x + z) :=
  Lp.coeFn_compMeasurePreserving (D a) _

omit [BorelSpace E] in
theorem planeJetTranslation_mem_graph (z : Vec 2)
    (D : JetL2 (volume.restrict Set.univ) K E) (hD : D ∈ planeHkGraph Set.univ K) :
    planeJetTranslation K z D ∈ planeHkGraph Set.univ K := by
  apply (mem_planeHkGraph_iff _).mpr
  apply hasOrderedWeakJetOn_congr_ae
    (fun a => (planeJetTranslation_component_ae z D a).symm)
  exact orderedWeakJet_translate ((mem_planeHkGraph_iff D).mp hD) z

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleJointProofs

/-! Positive assembly also covers times outside every output interval. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem positive_piece_jet_assembly_total (F : ChartedFamily ι h D P Ctx)
    (a b t : ℝ) (ht : t ∈ Set.Icc a b)
    (f : P → Vec 2 → V) (n : ℕ) (hf : ∀ p, ContDiff ℝ (n : ℕ) (f p))
    (hz : ∀ p x, t ∉ (F.piece p).output → f p x = 0)
    (ρ B : ℝ) (hρ : 0 ≤ ρ) (hB : 0 ≤ B)
    (hjet : ∀ p x, ρ ^ n * ‖iteratedFDeriv ℝ n (f p) x‖ ≤ F.weight p t * B)
    (x : Vec 2) :
    ρ ^ n * ‖iteratedFDeriv ℝ n (fun y => ∑ᶠ p, f p y) x‖ ≤ B := by
  classical
  by_cases hc : ∃ p, t ∈ (F.piece p).output
  · exact positive_piece_jet_assembly F a b t ht hc f n hf hz ρ B hρ hjet x
  · have he : (fun y => ∑ᶠ p, f p y) = fun _ => (0 : V) := by
      funext y
      have hp : ∀ p, f p y = 0 := fun p => hz p y (fun hh => hc ⟨p, hh⟩)
      simp only [hp, finsum_zero]
    rw [he]
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero] using hB

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! The longest incoming path gives an explicit bounded rank for every original source edge. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

def sourceDepthRank (F : ChartedFamily ι h D P Ctx) (H : ℕ) (v : ι) : ℕ := by
  classical
  exact Finset.univ.sup (fun j : Fin (H + 1) =>
    if ∃ u, HasEdgePath F j.val u v then j.val else 0)

theorem sourceDepthRank_le (F : ChartedFamily ι h D P Ctx) (H : ℕ) (v : ι) :
    sourceDepthRank F H v ≤ H := by
  classical
  apply Finset.sup_le
  intro j _
  split_ifs
  · exact Nat.le_of_lt_succ j.isLt
  · exact Nat.zero_le H

theorem path_length_le_sourceDepthRank {F : ChartedFamily ι h D P Ctx} {H n : ℕ}
    (hdepth : F.HasDepthAtMost H) {u v : ι} (hp : HasEdgePath F n u v) :
    n ≤ sourceDepthRank F H v := by
  classical
  have hn : n ≤ H := by
    by_contra hh
    exact not_hasEdgePath_of_depth hdepth (by omega) u v hp
  have ht := Finset.le_sup (s := Finset.univ)
    (f := fun j : Fin (H + 1) => if ∃ w, HasEdgePath F j.val w v then j.val else 0)
    (Finset.mem_univ (⟨n, Nat.lt_succ_of_le hn⟩ : Fin (H + 1)))
  simpa only [sourceDepthRank, ite_eq_left (show ∃ w, HasEdgePath F n w v from ⟨u, hp⟩)] using ht

theorem sourceDepthRank_edge_lt {F : ChartedFamily ι h D P Ctx} {H : ℕ}
    (hdepth : F.HasDepthAtMost H) {u v : ι} (he : Nonempty (F.Γ v u)) :
    sourceDepthRank F H u < sourceDepthRank F H v := by
  classical
  have hz : HasEdgePath F 0 v v := ⟨fun _ => v, rfl, rfl, fun i => Fin.elim0 i⟩
  have h1 : HasEdgePath F 1 u v := hasEdgePath_prepend hz he
  have hv : 0 < sourceDepthRank F H v := lt_of_lt_of_le (by omega : 0 < 1)
    (path_length_le_sourceDepthRank hdepth h1)
  by_contra hn
  have hle : sourceDepthRank F H v ≤ sourceDepthRank F H u := Nat.le_of_not_gt hn
  obtain ⟨j, _, hj⟩ := (Finset.le_sup_iff hv).mp hle
  by_cases hp : ∃ w, HasEdgePath F j.val w u
  · simp only [ite_eq_left hp] at hj
    obtain ⟨w, hw⟩ := hp
    have hs := path_length_le_sourceDepthRank hdepth (hasEdgePath_concat hw h1)
    omega
  · simp only [ite_eq_right hp] at hj
    omega

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Literal zero forcing can be replaced by the canonical zero torus carriers. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem torusHomogeneous_forcing_readout (K : ℕ) (ν a t : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (u f φ : Vec 2 → E)
    (dφ : Fin 2 → Vec 2 → E) (du : ℝ → Fin 2 → Vec 2 → E)
    (flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (hs : CoupledWeakIdentity (volume.restrict AVenhance.unitCube)
      ν a t v u f φ dφ du flux 0 0) :
    CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν a t v u f φ dφ du flux
      (fun _ => (0 : TorusHk K (PiLp 2 (fun _ : Fin 2 => E))).toFunction.jet (valueIndex2 K))
      (fun _ => (0 : TorusHk K E).toFunction.jet (valueIndex2 K)) := by
  apply coupledWeakIdentity_integrands_congr _ ν a t v v u u f f φ φ dφ dφ
    du du flux flux 0 _ 0 _ Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl _ hs
  intro s _
  exact weakIdentityRhs_congr_ae _ ν s v v φ φ dφ dφ du du flux flux 0 _ 0 _
    Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl (fun _ => Filter.EventuallyEq.rfl)
    (fun _ => Filter.EventuallyEq.rfl) Filter.EventuallyEq.rfl
    (torusZero_rawJet_ae K (valueIndex2 K)).symm
    (torusZero_rawJet_ae K (valueIndex2 K)).symm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Every literal ordered coefficient derivative has its exact affine cell price. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem orderedCoefficientDerivative_affine (C : Vec 2 → E →L[ℝ] F)
    (j : ℕ) (w : DerivativeWord2 j) (e : ℝ) (y x : Vec 2) :
    orderedCoefficientDerivative (fun z => C (y + e • z)) j w x =
      e ^ j • orderedCoefficientDerivative C j w (y + e • x) := by
  induction j generalizing x with
  | zero => simp only [orderedCoefficientDerivative, pow_zero, one_smul]
  | succ j ih =>
    have he : orderedCoefficientDerivative (fun z => C (y + e • z)) j (Fin.init w) =
        fun z => e ^ j • orderedCoefficientDerivative C j (Fin.init w) (y + e • z) :=
      funext (fun z => ih (Fin.init w) z)
    rw [orderedCoefficientDerivative, he]
    change fderiv ℝ (e ^ j • (fun z => orderedCoefficientDerivative C j (Fin.init w)
      (y + e • z))) x (basisVec (w (Fin.last j))) = _
    rw [congrFun (fderiv_const_smul_field (𝕜 := ℝ)
      (f := fun z => orderedCoefficientDerivative C j (Fin.init w) (y + e • z)) (e ^ j)) x]
    have hcomp : (fun z => orderedCoefficientDerivative C j (Fin.init w) (y + e • z)) =
        (fun z => orderedCoefficientDerivative C j (Fin.init w) (z + y)) ∘ (fun z => e • z) := by
      funext z
      simp only [Function.comp_apply, add_comm]
    rw [hcomp]
    simp only [Pi.smul_apply, Function.comp_def]
    rw [fderiv_comp_smul (f := fun z => orderedCoefficientDerivative C j (Fin.init w) (z + y)),
      fderiv_comp_add_right]
    simp only [smul_apply, smul_smul, pow_succ, orderedCoefficientDerivative, add_comm]

theorem coefficientDerivativeArray_affine (C : Vec 2 → E →L[ℝ] F)
    (j : ℕ) (e : ℝ) (y x : Vec 2) :
    coefficientDerivativeArray (fun z => C (y + e • z)) j x =
      e ^ j • coefficientDerivativeArray C j (y + e • x) := by
  apply ContinuousLinearMap.ext
  intro z
  apply PiLp.ext
  intro w
  simp only [coefficientDerivativeArray_apply, orderedCoefficientDerivative_affine,
    smul_apply, PiLp.smul_apply]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Uniform finite response prices allow the source size to be removed from
preparation constants before the actual family is chosen. -/

theorem terminalResponseEnergyPrice_mono {C C' θ θ' : ℝ≥0∞}
    (hC : C ≤ C') (hθ : θ ≤ θ') (J H : ℕ) :
    terminalResponseEnergyPrice C θ J H ≤ terminalResponseEnergyPrice C' θ' J H := by
  unfold terminalResponseEnergyPrice
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul' (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ zero_le hC _) zero_le)
    (pow_le_pow_left₀ zero_le hθ _)

theorem retainedResponseEnergyPrice_mono {C C' θ θ' : ℝ≥0∞}
    (hC : C ≤ C') (hθ : θ ≤ θ') (J H : ℕ) :
    retainedResponseEnergyPrice C θ J H ≤ retainedResponseEnergyPrice C' θ' J H := by
  unfold retainedResponseEnergyPrice
  apply mul_le_mul_of_nonneg_left _ zero_le
  exact Finset.sum_le_sum (fun _ _ => terminalResponseEnergyPrice_mono hC hθ _ H)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Every literal product jet remains within the original coefficient support. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem multiplicationRawJet_zero_of_not_tsupport {K : ℕ}
    (C : Vec 2 → E →L[ℝ] F) (D : RawJet2 K E) (a : JetIndex2 K)
    (x : Vec 2) (hx : x ∉ tsupport C) : multiplicationRawJet C D a x = 0 := by
  unfold multiplicationRawJet
  apply Finset.sum_eq_zero
  intro m _
  unfold multiplicationTerm
  have hz : orderedCoefficientDerivative C (maskLeftLength a.1.val m)
      (maskWordEquiv 2 a.1.val m a.2).1 x = 0 := by
    by_contra hn
    exact hx (orderedCoefficientDerivative_tsupport_subset C _ _ (subset_tsupport _ hn))
  rw [hz]
  rfl

theorem multiplicationRawJet_support_subset {K : ℕ}
    (C : Vec 2 → E →L[ℝ] F) (D : RawJet2 K E) (a : JetIndex2 K) :
    Function.support (multiplicationRawJet C D a) ⊆ tsupport C := by
  intro x hx
  by_contra hn
  exact hx (multiplicationRawJet_zero_of_not_tsupport C D a x hn)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! Actual component response maps compose with retained forcing rows on the original source graph. -/

variable {ι : Type*} {h V Q : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
  [∀ i, AddCommGroup (Q i)] [∀ i, Module ℝ (Q i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

def nativeComponentResponseOperator (R : ∀ i, Q i →ₗ[ℝ] V i)
    (S : ∀ i, (∀ j, V j) →ₗ[ℝ] Q i) : Module.End ℝ (∀ i, V i) :=
  LinearMap.pi (fun i => (R i).comp (S i))

theorem nativeComponentResponseOperator_sourceDegree
    (F : ChartedFamily ι h D P Ctx) (n : ℕ)
    (R : ∀ i, Q i →ₗ[ℝ] V i) (S : ∀ i, (∀ j, V j) →ₗ[ℝ] Q i)
    (hS : ∀ f v, (∀ u, HasEdgePath F n u v → f u = 0) → S v f = 0) :
    HasSourceDegreeOn F n (nativeComponentResponseOperator R S) := by
  intro f v hf
  change R v (S v f) = 0
  rw [hS f v hf, map_zero]

def nativeDiagonalResponseOperator (R : ∀ i, Q i →ₗ[ℝ] V i)
    (M : ∀ i, V i →ₗ[ℝ] Q i) : Module.End ℝ (∀ i, V i) :=
  LinearMap.pi (fun i => (R i).comp ((M i).comp (LinearMap.proj i)))

theorem nativeDiagonalResponseOperator_sourceDegree
    (F : ChartedFamily ι h D P Ctx)
    (R : ∀ i, Q i →ₗ[ℝ] V i) (M : ∀ i, V i →ₗ[ℝ] Q i) :
    HasSourceDegreeOn F 0 (nativeDiagonalResponseOperator R M) := by
  intro f v hf
  change R v (M v (f v)) = 0
  have hv : f v = 0 := hf v ⟨fun _ => v, rfl, rfl, fun k => Fin.elim0 k⟩
  rw [hv, map_zero, map_zero]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Actual continuous linear isometric translations of plane Sobolev carriers. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

def planeCarrierTranslation (K : ℕ) (z : Vec 2) :
    PlaneHk Set.univ K E →L[ℝ] PlaneHk Set.univ K E :=
  ((planeJetTranslation K z).comp (planeHkGraph (E := E) Set.univ K).toSubmodule.subtypeL).codRestrict
    (planeHkGraph (E := E) Set.univ K).toSubmodule
    (fun f => planeJetTranslation_mem_graph z f.val f.property)

theorem planeCarrierTranslation_jet_ae (z : Vec 2) (f : PlaneHk Set.univ K E) (a : JetIndex2 K) :
    (planeCarrierTranslation K z f).toFunction.jet a =ᵐ[volume]
      fun x => f.toFunction.jet a (x + z) := by
  have hv : (planeCarrierTranslation K z f).val = planeJetTranslation K z f.val := rfl
  change ((planeCarrierTranslation K z f).val a : Vec 2 → E) =ᵐ[volume]
    fun x => f.val a (x + z)
  rw [hv]
  simpa only [Measure.restrict_univ] using planeJetTranslation_component_ae z f.val a

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Restricting a finite coefficient window decreases every original-mass Schur entry. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

theorem schurMatrix_time_mono (ν ρ : ℝ) (hν : 0 < ν) (hρ : 0 < ρ)
    (π : ι → ℝ) (K : ι → ℕ) (D : ℕ) (a b c d : ℝ)
    (hsub : Set.Icc a b ⊆ Set.Icc c d)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i j r, coefficientSeminorm ρ (K i) c d (A i j r) ≠ ⊤)
    (i j : ι) : schurMatrix ν ρ π K D a b A i j ≤ schurMatrix ν ρ π K D c d A i j := by
  unfold schurMatrix
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Finset.sum_le_sum
  intro r _
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact ENNReal.toReal_mono (hA i j r)
    (coefficientSeminorm_time_mono ρ (K i) a b c d hsub (A i j r))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleJointProofs

/-! Integer-image weak pairings on the literal unit cube of the solution predicate. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integral_unitCube_periodization (f : Vec 2 → E) (hf : Integrable f volume) :
    (∫ x in AVenhance.unitCube, latticePeriodization f x ∂volume) = ∫ x, f x ∂volume := by
  have he := integral_cell_periodization f hf
  rwa [Measure.restrict_congr_set Applications.cellI_ae_eq_unitCube] at he

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! A scalar moment weight commutes with the algebraic coefficient multiplication jet. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- An arbitrary scalar weight commutes with the raw Leibniz jet array. -/
theorem multiplicationRawJet_smul_weight {K : ℕ}
    (C : Vec 2 → E →L[ℝ] F) (D : RawJet2 K E) (q : Vec 2 → ℝ)
    (α : JetIndex2 K) (x : Vec 2) :
    multiplicationRawJet C (fun β y => q y • D β y) α x =
      q x • multiplicationRawJet C D α x := by
  simp only [multiplicationRawJet, multiplicationTerm, map_smul, Finset.smul_sum]

/-- Weighted source jets stay in L² after multiplication by a bounded finite coefficient jet. -/
theorem multiplicationRawJet_weight_memL2On [MeasurableSpace E] [MeasurableSpace F]
    {K : ℕ} {U : Set (Vec 2)} (C : Vec 2 → E →L[ℝ] F)
    (hC : ContDiff ℝ (K : ℕ) C) (D : RawJet2 K E) (q : Vec 2 → ℝ)
    (hD : JetMemL2On U (fun β y => q y • D β y))
    {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l) :
    JetMemL2On U (fun β y => q y • multiplicationRawJet C D β y) := by
  intro β
  have hm := multiplicationRawJet_memL2On hC hD hb β
  have he : multiplicationRawJet C (fun α x => q x • D α x) β =
      fun y => q y • multiplicationRawJet C D β y :=
    funext (fun y => multiplicationRawJet_smul_weight C D q β y)
  rw [he] at hm
  exact hm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The three genuine residual estimates have one finite price, independent
of the actual source size, and retain their separate small powers. -/

def coupledRetainedResidualPrice (C cm cs ct : ℝ≥0∞) (J H : ℕ) : ℝ≥0∞ :=
  (cm + cs) * retainedResponseEnergyPrice C 1 J H +
    ct * terminalResponseEnergyPrice C 1 J H

theorem coupledRetainedResidualPrice_ne_top (C cm cs ct : ℝ≥0∞)
    (hC : C ≠ ⊤) (hm : cm ≠ ⊤) (hs : cs ≠ ⊤) (ht : ct ≠ ⊤) (J H : ℕ) :
    coupledRetainedResidualPrice C cm cs ct J H ≠ ⊤ := by
  apply ENNReal.add_ne_top.mpr
  constructor
  · exact ENNReal.mul_ne_top (ENNReal.add_ne_top.mpr ⟨hm, hs⟩)
      (retainedResponseEnergyPrice_ne_top C 1 hC (by norm_num) J H)
  · exact ENNReal.mul_ne_top ht
      (terminalResponseEnergyPrice_ne_top C 1 hC (by norm_num) J H)

theorem coupledRetainedResidualPrice_budget (C cm cs ct θ ζ η G0 : ℝ≥0∞)
    (hθ : θ ≤ 1) (p J H : ℕ) :
    (cm * ζ ^ (2 * p) * retainedResponseEnergyPrice C θ J H) * G0 +
      (cs * ζ ^ (2 * p) * retainedResponseEnergyPrice C θ J H) * G0 +
      (ct * terminalResponseEnergyPrice C θ J H * η ^ (2 * (J + 1))) * G0 ≤
    coupledRetainedResidualPrice C cm cs ct J H *
      (ζ ^ (2 * p) + η ^ (2 * (J + 1))) * G0 := by
  have hr := retainedResponseEnergyPrice_mono (le_refl C) hθ J H
  have ht := terminalResponseEnergyPrice_mono (le_refl C) hθ J H
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hr (show 0 ≤ cm * ζ ^ (2 * p) from zero_le)) (show 0 ≤ G0 from zero_le)
  have hs := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hr (show 0 ≤ cs * ζ ^ (2 * p) from zero_le)) (show 0 ≤ G0 from zero_le)
  have hterm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (show 0 ≤ ct from zero_le))
      (show 0 ≤ η ^ (2 * (J + 1)) from zero_le)) (show 0 ≤ G0 from zero_le)
  refine (add_le_add (add_le_add hm hs) hterm).trans ?_
  let a := (cm + cs) * retainedResponseEnergyPrice C 1 J H
  let b := ct * terminalResponseEnergyPrice C 1 J H
  have ha : a ≤ a + b := le_add_right le_rfl
  have hb : b ≤ a + b := le_add_left le_rfl
  have hh := add_le_add
    (mul_le_mul_of_nonneg_right ha (show 0 ≤ ζ ^ (2 * p) from zero_le))
    (mul_le_mul_of_nonneg_right hb (show 0 ≤ η ^ (2 * (J + 1)) from zero_le))
  have hfinal := mul_le_mul_of_nonneg_right hh (show 0 ≤ G0 from zero_le)
  dsimp only [a, b] at hfinal
  unfold coupledRetainedResidualPrice
  convert hfinal using 1 <;> ring

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! A fixed Schur multiplier is absorbed in the common insertion constant,
leaving unit source size in the finite response prices. -/

theorem terminalResponseEnergyPrice_source_scale (C θ θcap : ℝ≥0∞)
    (hθ : θ ≤ θcap) (J H : ℕ) :
    terminalResponseEnergyPrice C θ J H ≤
      terminalResponseEnergyPrice (C * (1 + θcap ^ 2)) 1 J H := by
  unfold terminalResponseEnergyPrice
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply Finset.sum_le_sum
  intro k _
  have hbase : 1 ≤ 1 + θcap ^ 2 := le_add_right le_rfl
  have hpow : θ ^ (2 * k) ≤ (1 + θcap ^ 2) ^ (J + k) := by
    rw [pow_mul]
    exact (pow_le_pow_left₀ zero_le
      ((pow_le_pow_left₀ zero_le hθ 2).trans (le_add_left le_rfl)) k).trans
      (pow_le_pow_right₀ hbase (Nat.le_add_left k J))
  rw [one_pow, mul_one, mul_pow]
  exact (mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ shiftedResponseEnergyBudget (fun _ => 1) (fun _ => 1) 0 0 J k * C ^ (J + k) from zero_le)).trans_eq
      (by ac_rfl)

theorem retainedResponseEnergyPrice_source_scale (C θ θcap : ℝ≥0∞)
    (hθ : θ ≤ θcap) (J H : ℕ) :
    retainedResponseEnergyPrice C θ J H ≤
      retainedResponseEnergyPrice (C * (1 + θcap ^ 2)) 1 J H := by
  unfold retainedResponseEnergyPrice
  apply mul_le_mul_of_nonneg_left _ zero_le
  exact Finset.sum_le_sum (fun _ _ => terminalResponseEnergyPrice_source_scale C θ θcap hθ _ H)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Zero extension at inactive partition times preserves the original identities, pieces and weighted independent fields. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

def inactiveTimeZeroFamily (F : ChartedFamily ι h D P Ctx) : ChartedFamily ι h D P Ctx := by
  classical
  exact { F with
    flux := fun p c v u γ d I t X z =>
      if F.weight p t = 0 then 0 else F.flux p c v u γ d I t X z
    flux_periodic := by
      intro p c v u γ d I t X n z
      by_cases ht : F.weight p t = 0
      · simp only [ht, ite_true]
      · simp only [ht, ite_false]
        exact F.flux_periodic p c v u γ d I t X n z
    flux_zero := by
      intro p c v u γ d I hd
      funext t X z
      by_cases ht : F.weight p t = 0
      · simp only [ht, ite_true]
      · simp only [ht, ite_false]
        exact congrFun (congrFun (congrFun (F.flux_zero p c v u γ d I hd) t) X) z }

theorem inactiveTimeZeroFamily_flux_of_weight_ne_zero (F : ChartedFamily ι h D P Ctx)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (t : ℝ) (ht : F.weight p t ≠ 0) :
    (inactiveTimeZeroFamily F).flux p c v u γ d I t = F.flux p c v u γ d I t := by
  funext X z
  simp only [inactiveTimeZeroFamily, ht, ite_false]

theorem inactiveTimeZeroFamily_weight_ne_zero_mem_output (F : ChartedFamily ι h D P Ctx)
    (p : P) (t : ℝ) (ht : F.weight p t ≠ 0) : t ∈ (F.piece p).output := by
  by_contra ho
  exact ht (F.weight_zero p t ho)

theorem inactiveTimeZeroFamily_time_measurable (F : ChartedFamily ι h D P Ctx)
    (hw : ∀ p, Measurable (F.weight p)) (hm : F.IsTimeMeasurable) :
    (inactiveTimeZeroFamily F).IsTimeMeasurable := by
  classical
  intro p c v u γ d I X z
  exact Measurable.ite (measurableSet_eq_fun (hw p)
    (measurable_const : Measurable (fun _ : ℝ => (0 : ℝ))))
    measurable_const (hm p c v u γ d I X z)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! Actual native edge maps assembled on the original constituent graph give a source-degree-one response. -/

variable {ι : Type*} [Fintype ι] {h V Q : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
  [∀ i, AddCommGroup (Q i)] [∀ i, Module ℝ (Q i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

def nativeFamilyEdgeForcingMap (L : ∀ v u, V u →ₗ[ℝ] Q v) (v : ι) :
    (∀ i, V i) →ₗ[ℝ] Q v := ∑ u, (L v u).comp (LinearMap.proj u)

theorem nativeFamilyEdgeForcingMap_apply (L : ∀ v u, V u →ₗ[ℝ] Q v)
    (v : ι) (f : ∀ i, V i) : nativeFamilyEdgeForcingMap L v f = ∑ u, L v u (f u) := by
  simp only [nativeFamilyEdgeForcingMap, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]

theorem nativeFamilyEdgeForcingMap_original_graph_support
    (F : ChartedFamily ι h D P Ctx) (L : ∀ v u, V u →ₗ[ℝ] Q v)
    (hL : ∀ v u, ¬ Nonempty (F.Γ v u) → L v u = 0)
    (f : ∀ i, V i) (v : ι) (hf : ∀ u, HasEdgePath F 1 u v → f u = 0) :
    nativeFamilyEdgeForcingMap L v f = 0 := by
  classical
  rw [nativeFamilyEdgeForcingMap_apply]
  apply Finset.sum_eq_zero
  intro u _
  by_cases hΓ : Nonempty (F.Γ v u)
  · have hu := hf u (hasEdgePath_prepend
      ⟨fun _ => v, rfl, rfl, fun k => Fin.elim0 k⟩ hΓ)
    rw [hu, map_zero]
  · rw [hL v u hΓ, LinearMap.zero_apply]

theorem nativeFamilyEdgeResponse_sourceDegree
    (F : ChartedFamily ι h D P Ctx) (L : ∀ v u, V u →ₗ[ℝ] Q v)
    (hL : ∀ v u, ¬ Nonempty (F.Γ v u) → L v u = 0) (R : ∀ v, Q v →ₗ[ℝ] V v) :
    HasSourceDegreeOn F 1 (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap L)) :=
  nativeComponentResponseOperator_sourceDegree F 1 R _
    (nativeFamilyEdgeForcingMap_original_graph_support F L hL)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Translation retains the exact higher-to-lower Sobolev lift. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K L : ℕ}

theorem planeCarrierTranslation_truncate (hKL : K ≤ L) (z : Vec 2)
    (f : PlaneHk Set.univ L E) :
    planeCarrierTranslation K z (truncatePlaneHk hKL f) =
      truncatePlaneHk hKL (planeCarrierTranslation L z f) := by
  apply Subtype.ext
  apply PiLp.ext
  intro α
  rfl

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The actual coupled weak RHS is cell-integrable for cell L2 jets and bounded drift. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem cell_weakIdentityRhs_integrable (ν s : ℝ) (v : ℝ → Vec 2 → Vec 2) (φ : Vec 2 → E)
    (dφ : Fin 2 → Vec 2 → E) (du : ℝ → Fin 2 → Vec 2 → E)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (g : ℝ → Vec 2 → E)
    (hv : Continuous (v s)) (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ x, ‖v s x‖ ≤ V)
    (hφ : MemLp φ 2 (volume.restrict AVenhance.unitCube))
    (hdφ : ∀ k, MemLp (dφ k) 2 (volume.restrict AVenhance.unitCube))
    (hdu : ∀ k, MemLp (du s k) 2 (volume.restrict AVenhance.unitCube))
    (hflux : ∀ k, MemLp (fun x => flux s x k) 2 (volume.restrict AVenhance.unitCube))
    (hF : ∀ k, MemLp (fun x => F s x k) 2 (volume.restrict AVenhance.unitCube))
    (hg : MemLp (g s) 2 (volume.restrict AVenhance.unitCube)) :
    Integrable (weakIdentityRhs ν v φ dφ du flux F g s) (volume.restrict AVenhance.unitCube) := by
  have hdrift (k : Fin 2) : Integrable (fun x => v s x k * inner ℝ (du s k x) (φ x))
      (volume.restrict AVenhance.unitCube) := by
    let C : Vec 2 → E →L[ℝ] E := fun x => v s x k • ContinuousLinearMap.id ℝ E
    have hC : Continuous C := (continuous_apply k |>.comp hv).smul continuous_const
    have hbC (x : Vec 2) : ‖C x‖ ≤ V := by
      calc
        _ = ‖v s x k‖ * ‖ContinuousLinearMap.id ℝ E‖ := norm_smul _ _
        _ ≤ ‖v s x k‖ * 1 := mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
        _ ≤ V := by simpa only [mul_one] using (norm_le_pi_norm (v s x) k).trans (hbv x)
    have hi := cell_coefficient_pairing_integrable _ _ (hdu k) hφ C hC V hV hbC
    simpa only [C, smul_apply, ContinuousLinearMap.id_apply, real_inner_smul_left] using hi
  have hdiff (k : Fin 2) := integrable_inner_of_memLp_two _ _ _ (hdu k) (hdφ k)
  have hfl (k : Fin 2) := integrable_inner_of_memLp_two _ _ _ ((hflux k).add (hF k)) (hdφ k)
  have hgφ := integrable_inner_of_memLp_two _ _ _ hg hφ
  exact (((integrable_finsetSum Finset.univ (fun k _ => hdrift k)).neg.sub
    ((integrable_finsetSum Finset.univ (fun k _ => hdiff k)).const_mul ν)).sub
    (integrable_finsetSum Finset.univ (fun k _ => hfl k))).add hgφ

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Constituents with zero original maps vanish before any molecular finiteness readout. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem constituentPhysical_zero_map (F : ChartedFamily ι h D P Ctx)
    (ν e E : ℝ) (actual : ∀ p, Ctx p) (v u : ι) (γ : F.Γ v u)
    (hγ : (F.identity v u γ).map = 0) (d : ℕ) (t : ℝ) (x : Vec 2) :
    constituentPhysical F ν e E actual v u γ d t x = 0 := by
  unfold constituentPhysical
  apply finsum_eq_zero_of_forall_eq_zero
  intro p
  ext z k
  simp [hγ, ContinuousLinearMap.comp_apply, PiLp.continuousLinearEquiv_symm_apply]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The finite scalar native array assembles continuously into its operator coefficient. -/

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def nativeArrayAssembly (r : ℕ) (C : U →L[ℝ] V) :
    (Fin 2 → DerivativeWord2 r → ℝ) →ₗ[ℝ]
      ((PiLp 2 (fun _ : DerivativeWord2 r => U)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => V))) where
  toFun b := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => V)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun k => ∑ A : DerivativeWord2 r,
      b k A • C.comp (PiLp.proj 2 (fun _ : DerivativeWord2 r => U) A))
  map_add' b c := by
    ext g k
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' w b := by
    ext g k
    simp [smul_smul, Finset.smul_sum]

theorem nativeArrayAssembly_continuous (r : ℕ) (C : U →L[ℝ] V) :
    Continuous (nativeArrayAssembly r C) :=
  (nativeArrayAssembly r C).continuous_of_finiteDimensional

theorem nativeArrayAssembly_measurable {X : Type*} [MeasurableSpace X]
    (r : ℕ) (C : U →L[ℝ] V) (b : X → Fin 2 → DerivativeWord2 r → ℝ)
    (hb : ∀ k A, Measurable (fun x => b x k A)) :
    Measurable (fun x => nativeArrayAssembly r C (b x)) := by
  exact (nativeArrayAssembly_continuous r C).measurable.comp
    (measurable_pi_iff.mpr (fun k => measurable_pi_iff.mpr (hb k)))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! A native family map is exactly the sum of its original component injections. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V Q : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
  [∀ i, AddCommGroup (Q i)] [∀ i, Module ℝ (Q i)]

def nativeFamilyMapEdge (T : ∀ v, (∀ u, V u) →ₗ[ℝ] Q v) (v u : ι) :
    V u →ₗ[ℝ] Q v := (T v).comp (LinearMap.single ℝ V u)

theorem nativeFamilyMapEdge_assembly (T : ∀ v, (∀ u, V u) →ₗ[ℝ] Q v) (v : ι) :
    nativeFamilyEdgeForcingMap (nativeFamilyMapEdge T) v = T v := by
  apply LinearMap.ext
  intro x
  rw [nativeFamilyEdgeForcingMap_apply]
  have hx : x = ∑ u, Pi.single u (x u) := (Finset.univ_sum_single x).symm
  conv_rhs => rw [hx, map_sum]
  rfl

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
namespace AVRegularity.CycleJointProofs

/-! Literal central and five-term forcing maps on component families. -/

variable {ι : Type*} {V Q : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
  [∀ i, AddCommGroup (Q i)] [∀ i, Module ℝ (Q i)]

def nativeDiagonalForcingMap (diag : ∀ i, V i →ₗ[ℝ] Q i) (i : ι) :
    (∀ j, V j) →ₗ[ℝ] Q i := (diag i).comp (LinearMap.proj i)

variable [Fintype ι]

def nativeMetricSourceFiveTermForcingMap
    (diag positive : ∀ i, V i →ₗ[ℝ] Q i) (Ledge : ∀ i j, V j →ₗ[ℝ] Q i)
    (Rm : ∀ i, V i →ₗ[ℝ] Q i) (Rs : ∀ i, (∀ j, V j) →ₗ[ℝ] Q i) (i : ι) :
    (∀ j, V j) →ₗ[ℝ] Q i :=
  nativeDiagonalForcingMap diag i + nativeDiagonalForcingMap positive i +
    nativeFamilyEdgeForcingMap Ledge i + nativeDiagonalForcingMap Rm i + Rs i

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! Native curve response operators retain the original source graph grading at every causal insertion. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem sourceDegreeOn_one (F : ChartedFamily ι h D P Ctx) :
    HasSourceDegreeOn F 0 (1 : Module.End ℝ (∀ i, V i)) := by
  intro f v hf
  change f v = 0
  apply hf v
  refine ⟨fun _ => v, rfl, rfl, ?_⟩
  intro k
  exact Fin.elim0 k

theorem finiteNativeResponseOperator_sourceDegree (F : ChartedFamily ι h D P Ctx)
    (R M S : Module.End ℝ (∀ i, V i))
    (hR : HasSourceDegreeOn F 0 R) (hM : HasSourceDegreeOn F 0 M)
    (hS : HasSourceDegreeOn F 1 S) (j n : ℕ) :
    HasSourceDegreeOn F n (finiteResponseOperator R M S j n) := by
  have hRM : HasSourceDegreeOn F 0 (R * M) := sourceDegreeOn_mul hR hM
  have hRS : HasSourceDegreeOn F 1 (R * S) := sourceDegreeOn_mul hR hS
  induction j generalizing n with
  | zero =>
    induction n with
    | zero =>
      rw [finiteResponseOperator]
      exact sourceDegreeOn_one F
    | succ n ihn =>
      rw [finiteResponseOperator]
      simpa only [Nat.add_comm 1 n] using sourceDegreeOn_mul hRS ihn
  | succ j ih =>
    induction n with
    | zero =>
      rw [finiteResponseOperator]
      exact sourceDegreeOn_mul hRM (ih 0)
    | succ n ihn =>
      rw [finiteResponseOperator]
      apply sourceDegreeOn_add
      · simpa only [Nat.zero_add] using sourceDegreeOn_mul hRM (ih (n + 1))
      · simpa only [Nat.add_comm 1 n] using sourceDegreeOn_mul hRS ihn

end AVRegularity.CycleJointProofs
end
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Weighted AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The measure-preserving material flow acts isometrically on the native plane flux carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E]

def planeFluxFlowPull {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (t s : ℝ) : PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2)))).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun i =>
        (Lp.compMeasurePreservingₗᵢ ℝ (fun y => AVRegularity.streamFlow φ hφ t y s)
          (streamFlow_measurePreserving hφ t s)).toContinuousLinearMap.comp
            (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2))) i)))

theorem planeFluxFlowPull_ae {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (t s : ℝ) (F : PlaneFluxL2 E) (i : Fin 2) :
    (planeFluxFlowPull hφ t s F i : Vec 2 → E) =ᵐ[volume]
      fun y => F i (AVRegularity.streamFlow φ hφ t y s) :=
  Lp.coeFn_compMeasurePreserving _ _

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! A transported original constituent contributes no physical order above its retained maximum. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem constituentPhysical_zero_above_max
    (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ) (actual : ∀ p, Ctx p)
    (v u : ι) (γ : F.Γ v u) (d : ℕ) (hd : (F.identity v u γ).maxOrder < d)
    (t : ℝ) (x : Vec 2) : constituentPhysical F ν e E actual v u γ d t x = 0 := by
  let b (p : P) (k : Fin 2) (A : DerivativeWord2 (d - 1)) :=
    transportedCoeff (chartInvJacobian ⇑((F.piece p).material t).symm)
      (F.identity v u γ).maxOrder
      (fun d' I => F.dimFlux ν e E p (actual p) v u γ d' I t
        (((F.piece p).material t).symm x) (e⁻¹ • ((F.piece p).material t).symm x))
      (d - 1) A x k
  have hb (p : P) : b p = 0 := by
    funext k A
    dsimp only [b]
    rw [transportedCoeff_zero_at_or_above _ _ _ (d - 1) (by omega) A x]
    rfl
  change (∑ᶠ p, F.weight p t • nativeArrayAssembly (d - 1) (F.identity v u γ).map (b p)) = 0
  simp only [hb, map_zero]
  have hz (p : P) : F.weight p t • (0 :
      (PiLp 2 (fun _ : DerivativeWord2 (d - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))) = 0 := by
    ext g k
    simp only [smul_apply, zero_apply, PiLp.zero_apply, smul_zero]
  simp only [hz]
  exact (finsum_zero : (∑ᶠ _ : P, (0 :
    (PiLp 2 (fun _ : DerivativeWord2 (d - 1) => h u)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h v)))) = 0)

end AVRegularity.CycleJointProofs
end
end
