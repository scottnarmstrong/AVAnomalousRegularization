-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.TransitionAffineSampling
public import AVRegularity.CycleJoint.PlaneH1Average
import AVRegularity.Analysis.Convolution.Kernel.ApproximationBounds
public import AVRegularity.CoupledEnergyPlane.Variational.DerivativeTensorOperator
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Positive native-order majorants for the literal transported coefficient array. -/

theorem transportedCoeff_molecular_jet_bound
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun x => K x i j))
    (N Dγ n r : ℕ) (C E ρ : ℝ) (hC : 0 ≤ C) (hE : 0 < E)
    (hρ : 0 ≤ ρ) (hρE : ρ ≤ E) (hn : n + Dγ ≤ N)
    (hKC : ∀ a b j, j ≤ N → ∀ x,
      E ^ j * ‖iteratedFDeriv ℝ j (fun y => K y a b) x‖ ≤ C)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2 → Vec 2)
    (hB : ∀ d I i, ContDiff ℝ (n : ℕ) (fun x => B d I x i))
    (MB : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ)
    (hBj : ∀ d ∈ Finset.Icc (r + 1) Dγ, ∀ I i j, j ≤ n → ∀ y,
      ρ ^ j * ‖iteratedFDeriv ℝ j (fun x => B d I x i) y‖ ≤ MB d I)
    (A : DerivativeWord2 r) (a : Fin 2) (x : Vec 2) :
    ρ ^ n * ‖iteratedFDeriv ℝ n (fun y =>
      transportedCoeff K Dγ (fun d I => B d I y) r A y a) x‖ ≤
      ∑ d ∈ Finset.Icc (r + 1) Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
        ((n + 1 : ℕ) * (2 : ℝ) ^ n) ^ 2 * C * MB d I *
          ((3 * (N + 1 : ℕ) * 2 ^ N * C) ^ (d - 1) * E⁻¹ ^ (d - 1 - r)) := by
  let f := fun d (I : DerivativeWord2 (d - 1)) (i : Fin 2) (y : Vec 2) =>
    K y a i * B d I y i * transitionT K (List.ofFn I) (List.ofFn A) y
  have hf d I i : ContDiff ℝ (n : ℕ) (f d I i) :=
    (((hK a i).of_le (by simp)).mul (hB d I i)).mul
      ((transitionT_spatial_smooth K hK _ _).of_le (by simp))
  have hfi d I : ContDiff ℝ (n : ℕ) (fun y => ∑ i, f d I i y) :=
    ContDiff.sum (fun i _ => hf d I i)
  have hfd d : ContDiff ℝ (n : ℕ) (fun y => ∑ I, ∑ i, f d I i y) :=
    ContDiff.sum (fun I _ => hfi d I)
  change ρ ^ n * ‖iteratedFDeriv ℝ n
    (fun y => ∑ d ∈ Finset.Icc (r + 1) Dγ, ∑ I, ∑ i, f d I i y) x‖ ≤ _
  apply (mul_le_mul_of_nonneg_left
    (finite_jet_finset_sum_norm_le _ _ n (fun d _ => hfd d) x) (pow_nonneg hρ n)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  apply (mul_le_mul_of_nonneg_left
    (finite_jet_sum_norm_le _ n (hfi d) x) (pow_nonneg hρ n)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro I _
  apply (mul_le_mul_of_nonneg_left
    (finite_jet_sum_norm_le _ n (hf d I) x) (pow_nonneg hρ n)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hd' := Finset.mem_Icc.mp hd
  have hh := native_piola_summand_molecular_jet_bound K hK N C E ρ hC hE hρ hρE hKC
    (List.ofFn I) (List.ofFn A) (by simp; omega) n (by simp; omega)
    (fun y => B d I y i) (hB d I i) (MB d I) (hBj d hd I i) a i x
  simpa only [List.length_ofFn] using hh

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleJointProofs

/-! Window-local physical coefficient bounds suffice for spacetime transfer on that window. -/

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace X]

def windowedPhysicalCoefficient (S : Set X) (C : X → Vec 2 → E →L[ℝ] F) :
    X → Vec 2 → E →L[ℝ] F := by
  classical
  exact fun t x => if t ∈ S then C t x else 0

omit [MeasurableSpace X] in
theorem windowedPhysicalCoefficient_eq (S : Set X) (C : X → Vec 2 → E →L[ℝ] F)
    (t : X) (ht : t ∈ S) : windowedPhysicalCoefficient S C t = C t := by
  classical
  funext x
  simp only [windowedPhysicalCoefficient, ite_eq_left ht]

omit [MeasurableSpace X] in
theorem windowedPhysicalCoefficient_continuous (S : Set X)
    (C : X → Vec 2 → E →L[ℝ] F) (hc : ∀ t ∈ S, Continuous (C t)) (t : X) :
    Continuous (windowedPhysicalCoefficient S C t) := by
  classical
  by_cases ht : t ∈ S
  · rw [windowedPhysicalCoefficient_eq S C t ht]
    exact hc t ht
  · have he : windowedPhysicalCoefficient S C t = fun _ => (0 : E →L[ℝ] F) := by
      funext x
      simp only [windowedPhysicalCoefficient, ite_eq_right ht]
    rw [he]
    exact continuous_const

theorem windowedPhysicalCoefficient_joint_measurable (S : Set X) (hS : MeasurableSet S)
    (C : X → Vec 2 → E →L[ℝ] F) (hj : Measurable (Function.uncurry C)) :
    Measurable (Function.uncurry (windowedPhysicalCoefficient S C)) := by
  classical
  exact Measurable.ite (measurable_fst hS) hj measurable_const

omit [MeasurableSpace X] in
theorem windowedPhysicalCoefficient_norm_le (S : Set X) (C : X → Vec 2 → E →L[ℝ] F)
    (MC : ℝ) (hMC : 0 ≤ MC) (hC : ∀ t ∈ S, ∀ x, ‖C t x‖ ≤ MC) (t : X) (x : Vec 2) :
    ‖windowedPhysicalCoefficient S C t x‖ ≤ MC := by
  classical
  by_cases ht : t ∈ S
  · simpa only [windowedPhysicalCoefficient, ite_eq_left ht] using hC t ht x
  · simpa only [windowedPhysicalCoefficient, ite_eq_right ht, norm_zero] using hMC

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.CycleWords AVRegularity.ChartTransport
namespace AVRegularity.CycleJointProofs

/-! Polynomially weighted jets under a scale-controlled spatial chart. -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem polynomialMoment_scaled_comp_bound
    {g : Vec 2 → V} {Ψ : Vec 2 → Vec 2} {n d : ℕ}
    (hg : ContDiff ℝ (n : ℕ∞) g) (hΨ : ContDiff ℝ (n : ℕ∞) Ψ)
    {D R s ϖ L B : ℝ} (hD : 1 ≤ D) (hs : 0 < s) (hsR : s ≤ R)
    (hϖ : 0 ≤ ϖ) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hjet : ∀ p, 1 ≤ p → p ≤ n → ∀ x,
      ‖iteratedFDeriv ℝ p Ψ x‖ ≤ D * R⁻¹ ^ (p - 1))
    (hgjet : ∀ j, j ≤ n → ∀ y,
      s ^ j * ‖iteratedFDeriv ℝ j g y‖ ≤ B * polynomialMomentRoot ϖ y ^ d)
    (x : Vec 2) (hnorm : ‖Ψ x‖ ≤ L * ‖x‖) :
    s ^ n * ‖iteratedFDeriv ℝ n (g ∘ Ψ) x‖ ≤
      (n.factorial : ℝ) * D ^ n * ((n + 1 : ℕ) * B) *
        (1 + 2 * L) ^ d * polynomialMomentRoot ϖ x ^ d := by
  have hh := scaled_comp_bound hg hΨ hD hs hsR x (fun p hp hpn => hjet p hp hpn x)
  have hsum : (∑ j ∈ Finset.range (n + 1), s ^ j * ‖iteratedFDeriv ℝ j g (Ψ x)‖) ≤
      (n + 1 : ℕ) * (B * polynomialMomentRoot ϖ (Ψ x) ^ d) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (n + 1), B * polynomialMomentRoot ϖ (Ψ x) ^ d :=
        Finset.sum_le_sum (fun j hj => hgjet j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) _)
      _ = _ := by simp
  have hroot := polynomialMomentRoot_le_of_norm_le ϖ L hϖ hL (Ψ x) x hnorm
  have hpow := pow_le_pow_left₀ ((by norm_num : (0 : ℝ) ≤ 1).trans (polynomialMomentRoot_one_le ϖ (Ψ x))) hroot d
  have hscale : 0 ≤ (n.factorial : ℝ) * D ^ n := by positivity
  calc
    _ ≤ (n.factorial : ℝ) * D ^ n * ((n + 1 : ℕ) * (B * polynomialMomentRoot ϖ (Ψ x) ^ d)) :=
      hh.trans (mul_le_mul_of_nonneg_left hsum hscale)
    _ ≤ (n.factorial : ℝ) * D ^ n * ((n + 1 : ℕ) * (B *
        ((1 + 2 * L) * polynomialMomentRoot ϖ x) ^ d)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpow hB) (by positivity)) hscale
    _ = _ := by rw [mul_pow]; ring

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleJointProofs

/-! Joint measurability on the original time window suffices for the actual zero extension. -/

variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace X]

theorem windowedPhysicalCoefficient_joint_measurable_of_restricted (S : Set X)
    (hS : MeasurableSet S) (C : X → Vec 2 → E →L[ℝ] F)
    (hj : Measurable (fun p : S × Vec 2 => C p.1 p.2)) :
    Measurable (Function.uncurry (windowedPhysicalCoefficient S C)) := by
  classical
  let B : Set (X × Vec 2) := Prod.fst ⁻¹' S
  have hB : MeasurableSet B := measurable_fst hS
  apply measurable_of_restrict_of_restrict_compl hB
  · have hm : Measurable (fun z : B =>
        ((⟨z.val.1, z.property⟩ : S), z.val.2)) := by
      have hfst : Measurable (fun z : B => (⟨z.val.1, z.property⟩ : S)) :=
        (measurable_fst.comp measurable_subtype_coe).subtype_mk
      exact hfst.prodMk (measurable_snd.comp measurable_subtype_coe)
    have he : B.domRestrict (Function.uncurry (windowedPhysicalCoefficient S C)) =
        fun z : B => C z.val.1 z.val.2 := by
      funext z
      change (if z.val.1 ∈ S then C z.val.1 z.val.2 else 0) = C z.val.1 z.val.2
      exact ite_eq_left z.property
    rw [he]
    exact hj.comp hm
  · have he : (Bᶜ).domRestrict (Function.uncurry (windowedPhysicalCoefficient S C)) =
        fun _ : (Bᶜ : Set (X × Vec 2)) => (0 : E →L[ℝ] F) := by
      funext z
      change (if z.val.1 ∈ S then C z.val.1 z.val.2 else 0) = 0
      exact ite_eq_right z.property
    rw [he]
    exact measurable_const

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Each homogeneous weak direction has a genuine spatial pairing integral. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem homogeneous_directional_pairings_integrable {U : Set (Vec 2)} (s : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (du : ℝ → Fin 2 → Vec 2 → E) (flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (hv : Continuous (v s)) (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ x, ‖v s x‖ ≤ V)
    (hφ : MemLp φ 2 (volume.restrict U))
    (hdφ : ∀ k, MemLp (dφ k) 2 (volume.restrict U))
    (hdu : ∀ k, MemLp (du s k) 2 (volume.restrict U))
    (hflux : ∀ k, MemLp (fun x => flux s x k) 2 (volume.restrict U)) :
    (∀ k, Integrable (fun x => v s x k * inner ℝ (du s k x) (φ x)) (volume.restrict U)) ∧
    (∀ k, Integrable (fun x => inner ℝ (du s k x) (dφ k x)) (volume.restrict U)) ∧
    ∀ k, Integrable (fun x => inner ℝ (flux s x k) (dφ k x)) (volume.restrict U) := by
  have hdrift (k : Fin 2) : Integrable (fun x => v s x k * inner ℝ (du s k x) (φ x))
      (volume.restrict U) := by
    have hm := memLp_operator_mul (driftPairingCoefficient_continuous (E := E) (v s) hv k)
      (hdu k) hV (fun x => (driftPairingCoefficient_norm_le (E := E) (v s x) k).trans (hbv x))
    have hi := integrable_inner_of_memLp_two _ _ _ hm hφ
    simpa only [driftPairingCoefficient_inner] using hi
  have hdiff (k : Fin 2) := integrable_inner_of_memLp_two _ _ _ (hdu k) (hdφ k)
  have hfl (k : Fin 2) := integrable_inner_of_memLp_two _ _ _ (hflux k) (hdφ k)
  exact ⟨hdrift, hdiff, hfl⟩

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleJointProofs

/-! Native H1 convolution averages have smooth literal value and gradient representatives. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def planeH1AverageLiteral (R : Vec 2 ≃L[ℝ] Vec 2) (κ : Vec 2 → ℝ)
    (u : PlaneHk univ 1 E) : Vec 2 → E :=
  fun x => ∫ z : Vec 2, κ z • planeHkValueOperator 1 u (x - R z)

omit [FiniteDimensional ℝ E] in
theorem planeH1AverageLiteral_smooth (R : Vec 2 ≃L[ℝ] Vec 2) (κ : Vec 2 → ℝ)
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ) (u : PlaneHk univ 1 E) :
    ContDiff ℝ (⊤ : ℕ∞) (planeH1AverageLiteral R κ u) :=
  contDiff_literalAverage R hc hd ((Lp.memLp (planeHkValueOperator 1 u)).locallyIntegrable
    (by norm_num))

omit [FiniteDimensional ℝ E] in
theorem planeH1AverageLiteral_value_ae (R : Vec 2 ≃L[ℝ] Vec 2) (κ : Vec 2 → ℝ)
    (hκ : Integrable κ) (u : PlaneHk univ 1 E) :
    (planeHkValueOperator 1 (planeH1Average R.toLinearEquiv.toAddHom R.continuous κ hκ u)
      : Vec 2 → E) =ᵐ[volume] planeH1AverageLiteral R κ u := by
  rw [planeH1Average_value]
  exact averagingOperator_plane_literal_ae R hκ _

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Divergence-free transport moves onto a compact smooth test for actual H1 readouts. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeH1_compact_weak_transport (u : PlaneHk univ 1 E) (e : E)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hdiv : ∀ x, ∑ i : Fin 2, fderiv ℝ (fun y => v y i) x (basisVec i) = 0)
    (q : Vec 2 → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hs : HasCompactSupport q) :
    (∫ x, q x * ∑ i : Fin 2, v x i * inner ℝ e (planeH1GradientOperator u i x)) =
      -(∫ x, (∑ i : Fin 2, v x i * fderiv ℝ q x (basisVec i)) *
        inner ℝ e (planeHkValueOperator 1 u x)) := by
  apply compact_weak_divfree_transport
    ((innerSL ℝ e).comp_memLp' (Lp.memLp (planeHkValueOperator 1 u)))
    (fun i => (innerSL ℝ e).comp_memLp' (Lp.memLp (planeH1GradientOperator u i)))
    (fun i => planeH1_value_gradient_weakPartial u i e) v hv hdiv q hq hs

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The actual order-zero torus-to-plane patch maps satisfy the sharp total energy budget. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem spatialPatchLocalization_norm_sq_sum {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) (f : TorusHk 0 E) :
    (∑ j : Fin 2 → Fin N,
      ‖spatialPatchLocalization hζ N hN (fun i => (j i : ℤ)) 0 f‖ ^ 2) ≤ ‖f‖ ^ 2 := by
  have he (j : Fin 2 → Fin N) :
      ‖spatialPatchLocalization hζ N hN (fun i => (j i : ℤ)) 0 f‖ ^ 2 =
      ∫ x, ‖spatialPatchCutoff ζ N (fun i => (j i : ℤ)) x •
        f.toFunction.jet (valueIndex2 0) x‖ ^ 2 ∂volume := by
    rw [planeHk_zero_norm_sq]
    simp only [Measure.restrict_univ]
    apply integral_congr_ae
    have hv := localizeTorusCarrier_value_ae f
      (spatialPatchCoefficient ζ N (fun i => (j i : ℤ)))
      (spatialPatchCoefficient_smooth hζ N _ 0) (spatialPatchCoefficient_compact hζ N hN _)
    filter_upwards [hv] with x hx
    change ‖(localizeTorusCarrier f _ _ _).toFunction.jet (valueIndex2 0) x‖ ^ 2 = _
    rw [hx]
    rfl
  simp_rw [he]
  rw [torusHk_zero_norm_sq]
  exact periodic_patch_l2_integral_budget hζ N hN _ (torusHk_jet_measurable f _)
    (f.toFunction.hasPeriodicWeakJet.2.1 _) (f.toFunction.hasPeriodicWeakJet.1 _)

theorem spatialPatchLocalization_zero_bound {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N) (f : TorusHk 0 E) :
    ‖spatialPatchLocalization hζ N hN (fun i => (j i : ℤ)) 0 f‖ ≤ ‖f‖ := by
  have hs := (Finset.single_le_sum (fun k _ => sq_nonneg
    ‖spatialPatchLocalization hζ N hN (fun i => (k i : ℤ)) 0 f‖)
    (Finset.mem_univ j)).trans (spatialPatchLocalization_norm_sq_sum hζ N hN f)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

def spatialPatchLocalizationCLM {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) (j : Fin 2 → Fin N) :
    TorusHk 0 E →L[ℝ] PlaneHk Set.univ 0 E :=
  (spatialPatchLocalization hζ N hN (fun i => (j i : ℤ)) 0).mkContinuous 1
    (fun f => by simpa only [one_mul] using spatialPatchLocalization_zero_bound hζ N hN j f)

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleJointProofs

/-! Restricting the actual translated carrier gives exactly its established local image readout. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem translated_local_jet_readout (U : Set (Vec 2)) (z : Vec 2)
    (f : PlaneHk Set.univ K E) (α : JetIndex2 K) :
    restrictPlaneLpCLM U (planeJetReadoutOperator K α (planeCarrierTranslation K z f)) =
      planeImageJetCLM U z α f := by
  apply Lp.ext
  have hr := restrictPlaneLpCLM_ae U
    (planeJetReadoutOperator K α (planeCarrierTranslation K z f))
  have hu := (univToPlane_ae ((planeCarrierTranslation K z f).val α)).restrict (s := U)
  have ht := (planeCarrierTranslation_jet_ae z f α).restrict (s := U)
  exact ((hr.trans hu).trans ht).trans (planeImageJetCLM_ae U z α f).symm

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Tensor assembly reads every actual Sobolev jet component. -/

variable {J E : Type*} [Fintype J] [DecidableEq J]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The finite tensor carrier has the literal array of all jets, at every stored order. -/
theorem planeFamilyTensor_jet_ae {K : ℕ} (w : J → PlaneHk Set.univ K E) (β : JetIndex2 K) :
    (planeFamilyTensor w).val β =ᵐ[volume.restrict Set.univ]
      fun x => (WithLp.toLp 2 (fun j => (w j).val β x) : PiLp 2 (fun _ : J => E)) := by
  rw [planeFamilyTensor_jet]
  have hs := Lp.coeFn_finsetSum Finset.univ (fun j : J =>
    (tensorEntryCLM (J := J) (E := E) j).compLpL 2 (volume.restrict Set.univ) ((w j).val β))
  have ht : ∀ᵐ x ∂volume.restrict Set.univ, ∀ j : J,
      ((tensorEntryCLM (J := J) (E := E) j).compLpL 2 (volume.restrict Set.univ)
        ((w j).val β)) x = tensorEntryCLM (J := J) (E := E) j ((w j).val β x) :=
    ae_all_iff.mpr (fun j => ContinuousLinearMap.coeFn_compLpL
      (tensorEntryCLM (J := J) (E := E) j) _)
  filter_upwards [hs, ht] with x hx hterms
  rw [hx, Finset.sum_apply]
  apply PiLp.ext
  intro j
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  simp_rw [hterms]
  change (∑ k : J, PiLp.single 2 k ((w k).val β x) j) = _
  simp

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory Set Filter AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
open scoped Topology
namespace AVRegularity.CycleJointProofs

/-! Shrinking normalized convolution averages converge strongly in the actual native H1 norm. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeH1Average_tendsto (ρ : ℕ → Vec 2 →+ Vec 2)
    (hρ : ∀ n, Continuous (ρ n))
    (hzero : ∀ x, Tendsto (fun n => ρ n x) atTop (𝓝 0))
    (κ : Vec 2 → ℝ) (hκ : Integrable κ) (hmass : ∫ x, κ x = 1)
    (u : PlaneHk univ 1 E) :
    Tendsto (fun n => planeH1Average (ρ n) (hρ n) κ hκ u) atTop (𝓝 u) := by
  apply planeH1_tendsto_of_readouts
  · simp_rw [planeH1Average_value]
    exact tendsto_averagingOperator_of_tendsto_zero ρ hρ hzero hκ hmass _
  · have hc : Tendsto
        (fun n => fun i : Fin 2 => planeH1GradientOperator
          (planeH1Average (ρ n) (hρ n) κ hκ u) i)
        atTop (𝓝 (fun i : Fin 2 => planeH1GradientOperator u i)) := by
      apply tendsto_pi_nhds.mpr
      intro i
      simp_rw [planeH1Average_gradient]
      exact tendsto_averagingOperator_of_tendsto_zero ρ hρ hzero hκ hmass _
    have hp := (PiLp.continuous_toLp 2
      (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2)))).tendsto
        (fun i : Fin 2 => planeH1GradientOperator u i) |>.comp hc
    simpa only [Function.comp_def, WithLp.toLp_ofLp] using hp

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The literal coupled raw flux is linear in its coefficient array, including diagonal metric arrays. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable (K : ι → ℕ) (D : ℕ)
    (A B : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (t : ℝ) (w : ∀ i, PlaneHk Set.univ (K i + 1) (h i)) (i : ι) (x : Vec 2)

theorem planeRawCouplingFlux_add :
    planeRawCouplingFlux K D t (fun v u d r y => A v u d r y + B v u d r y) w i x =
      planeRawCouplingFlux K D t A w i x + planeRawCouplingFlux K D t B w i x := by
  simp only [planeRawCouplingFlux, add_apply, Finset.sum_add_distrib]

omit B in
theorem planeRawCouplingFlux_smul (c : ℝ) :
    planeRawCouplingFlux K D t (fun v u d r y => c • A v u d r y) w i x =
      c • planeRawCouplingFlux K D t A w i x := by
  simp only [planeRawCouplingFlux, smul_apply, Finset.smul_sum]

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Each homogeneous weak atom is genuinely integrable for the actual L2 spatial readouts. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem homogeneousWeakRhsAtom_integrable {U : Set (Vec 2)} (ν s : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (du : ℝ → Fin 2 → Vec 2 → E) (flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (hv : Continuous (v s)) (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ x, ‖v s x‖ ≤ V)
    (hφ : MemLp φ 2 (volume.restrict U))
    (hdφ : ∀ k, MemLp (dφ k) 2 (volume.restrict U))
    (hdu : ∀ k, MemLp (du s k) 2 (volume.restrict U))
    (hflux : ∀ k, MemLp (fun x => flux s x k) 2 (volume.restrict U)) (j : Fin 3) :
    Integrable (homogeneousWeakRhsAtom ν v φ dφ du flux j s) (volume.restrict U) := by
  have hdrift (k : Fin 2) : Integrable (fun x => v s x k * inner ℝ (du s k x) (φ x))
      (volume.restrict U) := by
    have hm := memLp_operator_mul (driftPairingCoefficient_continuous (E := E) (v s) hv k)
      (hdu k) hV (fun x => (driftPairingCoefficient_norm_le (E := E) (v s x) k).trans (hbv x))
    have hi := integrable_inner_of_memLp_two _ _ _ hm hφ
    simpa only [driftPairingCoefficient_inner] using hi
  have hdiff (k : Fin 2) := integrable_inner_of_memLp_two _ _ _ (hdu k) (hdφ k)
  have hfl (k : Fin 2) := integrable_inner_of_memLp_two _ _ _ (hflux k) (hdφ k)
  unfold homogeneousWeakRhsAtom
  split_ifs
  · exact (integrable_finsetSum Finset.univ (fun k _ => hdrift k)).neg
  · exact (integrable_finsetSum Finset.univ (fun k _ => hdiff k)).const_mul (-ν)
  · exact (integrable_finsetSum Finset.univ (fun k _ => hfl k)).neg

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The computed diagonal order-two array reads precisely the scalar matrix action on the stored native first jets. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem planeDiagonalGradientCoefficient_of_component_ne (K : ι → ℕ) (D : ℕ)
    (G : ∀ _v : ι, ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (v u : ι) (d : admissibleOrders K D v u) (t : ℝ) (x : Vec 2) (huv : u ≠ v) :
    planeDiagonalGradientCoefficient (h := h) K D G v u d t x = 0 := by
  apply ContinuousLinearMap.ext
  intro q
  apply PiLp.ext
  intro k
  change planeDiagonalGradientCoefficient K D G v u d t x (WithLp.toLp 2 q.ofLp) k = 0
  by_cases hd : d.1 = 2
  · rw [planeDiagonalGradientCoefficient_apply_of_two K D G v u d t x hd q.ofLp k,
      familyDiagonalIdentity_of_ne v u huv]
    simp only [zero_apply, smul_zero, Finset.sum_const_zero]
  · rw [planeDiagonalGradientCoefficient_of_order_ne K D G v u d t x hd]
    rfl

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem planeRawCouplingFlux_diagonal_gradient (K : ι → ℕ) (D : ℕ) (hD : 2 ≤ D)
    (G : ∀ _v : ι, ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (w : ∀ i, PlaneHk Set.univ (K i + 1) (h i)) (i : ι) (t : ℝ) (x : Vec 2) (k : Fin 2) :
    planeRawCouplingFlux K D t (planeDiagonalGradientCoefficient K D G) w i x k =
      ∑ j : Fin 2, G i t x k j •
        (w i).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => j⟩ x := by
  classical
  let d2 : admissibleOrders K D i i := ⟨2, by simp [admissibleOrders, hD]⟩
  unfold planeRawCouplingFlux
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single d2]
    · rw [planeDiagonalGradientCoefficient_apply_of_two K D G i i d2 t x rfl _ k,
        familyDiagonalIdentity_self]
      simp only [ContinuousLinearMap.id_apply]
      rfl
    · intro d hd hne
      have horder : d.1 ≠ 2 := by
        intro he
        exact hne (Subtype.ext he)
      rw [planeDiagonalGradientCoefficient_of_order_ne K D G i i d t x horder]
      rfl
    · intro hh
      exact (hh (Finset.mem_univ d2)).elim
  · intro u hu hne
    apply Finset.sum_eq_zero
    intro d hd
    rw [planeDiagonalGradientCoefficient_of_component_ne K D G i u d t x hne]
    rfl
  · intro hh
    exact (hh (Finset.mem_univ i)).elim

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleJointProofs

/-! Global translated raw-jet pairings are the established local Hilbert image pairings. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K L : ℕ}

theorem translated_compact_jet_pairing (U : Set (Vec 2)) (z : Vec 2)
    (f : PlaneHk Set.univ K E) (α : JetIndex2 K) (φ : PlaneHk Set.univ L E) (β : JetIndex2 L)
    (hφ : ∀ᵐ x ∂volume, x ∉ U → φ.toFunction.jet β x = 0) :
    (∫ x, inner ℝ ((planeCarrierTranslation K z f).toFunction.jet α x) (φ.toFunction.jet β x)) =
      inner ℝ (planeImageJetCLM U z α f)
        (restrictPlaneLpCLM U (planeJetReadoutOperator L β φ)) := by
  have hf := univToPlane_ae ((planeCarrierTranslation K z f).val α)
  have hg := univToPlane_ae (φ.val β)
  have hz : ∀ᵐ x ∂volume, x ∉ U → planeJetReadoutOperator L β φ x = 0 := by
    filter_upwards [hg, hφ] with x hx hzero hxu
    exact hx.trans (hzero hxu)
  calc
    _ = ∫ x, inner ℝ (planeJetReadoutOperator K α (planeCarrierTranslation K z f) x)
        (planeJetReadoutOperator L β φ x) := by
      apply integral_congr_ae
      filter_upwards [hf, hg] with x hx hy
      exact congrArg₂ (inner ℝ) hx.symm hy.symm
    _ = inner ℝ (restrictPlaneLpCLM U (planeJetReadoutOperator K α (planeCarrierTranslation K z f)))
        (restrictPlaneLpCLM U (planeJetReadoutOperator L β φ)) :=
      plane_pairing_eq_local_inner U _ _ hz
    _ = _ := by rw [translated_local_jet_readout]

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! An actual coupled equation has the exact singleton-level presentation required by chain consumers. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

def planeOneLevelCoefficient (K : ι → ℕ) (D : ℕ)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (p p' : Fin 1 × ι) (d : admissibleOrders (fun q : Fin 1 × ι => K q.2) D p p')
    (t : ℝ) (z : Vec 2) :
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h p'.2) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h p.2) := A p.2 p'.2 d t z

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem planeRawCouplingFlux_oneLevel (K : ι → ℕ) (D : ℕ)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (W : ∀ i, PlaneHk Set.univ (K i + 1) (h i)) (p : Fin 1 × ι) (t : ℝ) (z : Vec 2) :
    planeRawCouplingFlux (fun q : Fin 1 × ι => K q.2) D t
      (planeOneLevelCoefficient K D A) (fun q => W q.2) p z =
      planeRawCouplingFlux K D t A W p.2 z := by
  classical
  simp only [planeRawCouplingFlux, planeOneLevelCoefficient, Fintype.sum_prod_type,
    Fin.sum_univ_one]
  rfl

theorem planeWeakSolution_oneLevel (K : ι → ℕ) (D : ℕ) (ν a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w) :
    IsCoupledWeakSolutionPlane ν a b v D (fun q : Fin 1 × ι => K q.2)
      (planeOneLevelCoefficient K D A) (fun q => f q.2) (fun q => F q.2)
      (fun q => g q.2) (fun q => u q.2) (fun q => w q.2) := by
  refine ⟨fun q => hs.1 q.2, fun q => hs.2.1 q.2,
    fun q => hs.2.2.1 q.2, fun q => hs.2.2.2.1 q.2, ?_⟩
  intro q t ht φ
  have hold := hs.2.2.2.2 q.2 t ht φ
  change CoupledWeakIdentity (volume.restrict Set.univ) ν a t v
    ((u q.2 t).toFunction.jet (valueIndex2 (K q.2))) ((f q.2).toFunction.jet (valueIndex2 (K q.2)))
    (φ.toFunction.jet (valueIndex2 1)) (fun k => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩)
    (fun r k => (w q.2 r).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
    (fun r => planeRawCouplingFlux (fun q : Fin 1 × ι => K q.2) D r
      (planeOneLevelCoefficient K D A) (fun q => w q.2 r) q)
    (fun r => (F q.2 r).toFunction.jet (valueIndex2 (K q.2)))
    (fun r => (g q.2 r).toFunction.jet (valueIndex2 (K q.2)))
  have hflux : (fun r => planeRawCouplingFlux (fun q : Fin 1 × ι => K q.2) D r
      (planeOneLevelCoefficient K D A) (fun q => w q.2 r) q) =
      (fun r => planeRawCouplingFlux K D r A (fun j => w j r) q.2) := by
    funext r z
    exact planeRawCouplingFlux_oneLevel K D A (fun j => w j r) q r z
  rw [hflux]
  exact hold
end

/-! Recover the genuine coupled equation from its singleton-level presentation. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeWeakSolution_of_oneLevel (K : ι → ℕ) (D : ℕ) (ν a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D (fun q : Fin 1 × ι => K q.2)
      (planeOneLevelCoefficient K D A) (fun q => f q.2) (fun q => F q.2)
      (fun q => g q.2) (fun q => u q.2) (fun q => w q.2)) :
    IsCoupledWeakSolutionPlane ν a b v D K A f F g u w := by
  refine ⟨fun i => hs.1 (0, i), fun i => hs.2.1 (0, i),
    fun i => hs.2.2.1 (0, i), fun i => hs.2.2.2.1 (0, i), ?_⟩
  intro i t ht φ
  have hold := hs.2.2.2.2 (0, i) t ht φ
  have hflux : (fun r => planeRawCouplingFlux (fun q : Fin 1 × ι => K q.2) D r
      (planeOneLevelCoefficient K D A) (fun q => w q.2 r) (0, i)) =
      (fun r => planeRawCouplingFlux K D r A (fun j => w j r) i) := by
    funext r z
    exact planeRawCouplingFlux_oneLevel K D A (fun j => w j r) (0, i) r z
  change CoupledWeakIdentity _ _ _ _ _ _ _ _ _ _
    (fun r => planeRawCouplingFlux (fun q : Fin 1 × ι => K q.2) D r
      (planeOneLevelCoefficient K D A) (fun q => w q.2 r) (0, i)) _ _ at hold
  rw [hflux] at hold
  exact hold
end

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The literal physical plane coupling flux is additive on genuine Sobolev carriers. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeRawCouplingFlux_add_ae (K : ι → ℕ) (D : ℕ) (r : ℝ)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (w w' : ∀ i, PlaneHk Set.univ (K i + 1) (h i)) (i : ι) :
    planeRawCouplingFlux K D r A (w + w') i =ᵐ[volume]
      planeRawCouplingFlux K D r A w i + planeRawCouplingFlux K D r A w' i := by
  have hall : ∀ᵐ x ∂volume, ∀ u, ∀ α : JetIndex2 (K u + 1),
      (w u + w' u).toFunction.jet α x =
        (w u).toFunction.jet α x + (w' u).toFunction.jet α x := by
    apply ae_all_iff.mpr
    intro u
    apply ae_all_iff.mpr
    intro α
    exact planeCarrier_jet_add_ae (w u) (w' u) α
  filter_upwards [hall] with x hx
  unfold planeRawCouplingFlux
  simp only [Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro d _
  rw [← map_add]
  congr 1
  apply (WithLp.ext_iff 2).mpr
  funext word
  exact hx u _
end

/-! The literal finite coupled flux commutes with simultaneous coefficient and carrier translation. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeRawCouplingFlux_translate_ae (K : ι → ℕ) (D : ℕ) (r : ℝ) (z : Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (w : ∀ i, PlaneHk Set.univ (K i + 1) (h i)) (i : ι) :
    planeRawCouplingFlux K D r (fun v u d s x => A v u d s (x + z))
      (fun u => planeCarrierTranslation (K u + 1) z (w u)) i =ᵐ[volume]
      fun x => planeRawCouplingFlux K D r A w i (x + z) := by
  have hall : ∀ᵐ x ∂volume, ∀ u, ∀ α : JetIndex2 (K u + 1),
      (planeCarrierTranslation (K u + 1) z (w u)).toFunction.jet α x =
        (w u).toFunction.jet α (x + z) := by
    apply ae_all_iff.mpr
    intro u
    apply ae_all_iff.mpr
    intro α
    exact planeCarrierTranslation_jet_ae z (w u) α
  filter_upwards [hall] with x hx
  unfold planeRawCouplingFlux
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  congr 1
  funext word
  exact hx u _
end

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Homogeneous plane solutions have the literal zero forcing in every weak test. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeHomogeneous_weak_test (K : ι → ℕ) (D : ℕ) (ν a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f (fun _ _ => 0) (fun _ _ => 0) u w)
    (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) (ψ : PlaneHk Set.univ 1 (h i)) :
    CoupledWeakIdentity volume ν a t v
      ((u i t).toFunction.jet (valueIndex2 (K i)))
      ((f i).toFunction.jet (valueIndex2 (K i)))
      (ψ.toFunction.jet (valueIndex2 1))
      (fun k => ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => k⟩)
      (fun s k => (w i s).toFunction.jet
        ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩)
      (fun s => planeRawCouplingFlux K D s A (fun j => w j s) i) 0 0 := by
  have hFz : (0 : PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))).toFunction.jet
      (valueIndex2 (K i)) =ᵐ[volume] 0 := by
    change (fun x => (0 : Lp (PiLp 2 (fun _ : Fin 2 => h i)) 2
      (volume.restrict (Set.univ : Set (Vec 2)))) x) =ᵐ[volume] 0
    simpa only [Measure.restrict_univ] using
      Lp.coeFn_zero (PiLp 2 (fun _ : Fin 2 => h i)) 2
        (volume.restrict (Set.univ : Set (Vec 2)))
  have hgz : (0 : PlaneHk Set.univ (K i) (h i)).toFunction.jet
      (valueIndex2 (K i)) =ᵐ[volume] 0 := by
    change (fun x => (0 : Lp (h i) 2
      (volume.restrict (Set.univ : Set (Vec 2)))) x) =ᵐ[volume] 0
    simpa only [Measure.restrict_univ] using
      Lp.coeFn_zero (h i) 2 (volume.restrict (Set.univ : Set (Vec 2)))
  have hw := hs.2.2.2.2 i t ht ψ
  simp only [Measure.restrict_univ] at hw
  apply coupledWeakIdentity_integrands_congr volume ν a t v v _ _ _ _ _ _ _ _
    _ _ _ _ _ 0 _ 0 Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl _ hw
  intro s _
  exact weakIdentityRhs_congr_ae volume ν s v v _ _ _ _ _ _ _ _ _ 0 _ 0
    Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl
    (fun _ => Filter.EventuallyEq.rfl) (fun _ => Filter.EventuallyEq.rfl)
    Filter.EventuallyEq.rfl hFz hgz
end

/-! The literal finite-family plane flux is spatially L2 for every actual lift value. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeRawCouplingFlux_component_memLp (K : ι → ℕ) (D : ℕ) (s : ℝ)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i)) (i : ι)
    (hc : ∀ i' d, Continuous (A i i' d s))
    (M : ∀ i', admissibleOrders K D i i' → ℝ)
    (hM : ∀ i' d, 0 ≤ M i' d) (hb : ∀ i' d x, ‖A i i' d s x‖ ≤ M i' d)
    (w : ∀ i, PlaneHk Set.univ (K i + 1) (h i)) (k : Fin 2) :
    MemLp (fun x => planeRawCouplingFlux K D s A w i x k) 2
      (volume.restrict Set.univ) := by
  have hi (i' : ι) (d : admissibleOrders K D i i') :
      MemLp (fun x => A i i' d s x (WithLp.toLp 2
        (fun word : DerivativeWord2 (d.1 - 1) => (w i').toFunction.jet
          ⟨⟨d.1 - 1, by have hd := admissibleOrders_reserve K D i i' d; omega⟩, word⟩ x)) k)
        2 (volume.restrict Set.univ) := by
    apply couplingFlux_component_memLp i i' Set.univ (A i i' d s)
      (hc i' d) (M i' d) (hM i' d) (hb i' d)
    intro word
    exact (w i').toFunction.memL2 _
  simp only [planeRawCouplingFlux, WithLp.ofLp_sum, Finset.sum_apply]
  exact memLp_finsetSum Finset.univ (fun i' _ =>
    memLp_finsetSum Finset.univ (fun d _ => hi i' d))
end

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory Filter AVRegularity.Weighted
open scoped Topology
namespace AVRegularity.CycleJointProofs

/-! Scalar multipliers whose uniform bounds vanish converge strongly to zero on every plane L2 class. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

theorem planeScalarMultiplier_tendsto_zero (c : ℕ → Vec 2 → ℝ)
    (hc : ∀ n, Continuous (c n)) (D : ℕ → ℝ) (hD : ∀ n, 0 ≤ D n)
    (hb : ∀ n x, |c n x| ≤ D n) (hlim : Tendsto D atTop (𝓝 0))
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    Tendsto (fun n => planeScalarMultiplier (c n) (hc n) (hD n) (hb n) u) atTop (𝓝 0) := by
  let L : ℕ → Lp E 2 (volume : Measure (Vec 2)) →L[ℝ]
      Lp E 2 (volume : Measure (Vec 2)) :=
    fun n => planeScalarMultiplier (c n) (hc n) (hD n) (hb n)
  have hLn (n : ℕ) : ‖L n‖ ≤ D n :=
    planeScalarMultiplier_norm_le (c n) (hc n) (hD n) (hb n)
  have hLu (n : ℕ) : ‖L n u‖ ≤ D n * ‖u‖ :=
    ((L n).le_opNorm u).trans (mul_le_mul_of_nonneg_right (hLn n) (norm_nonneg u))
  change Tendsto (fun n => L n u) atTop (𝓝 0)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hh : Tendsto (fun n => D n * ‖u‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using hlim.mul_const ‖u‖
  exact squeeze_zero (fun n => norm_nonneg (L n u)) hLu hh

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergyPlane
namespace AVRegularity.CycleJointProofs

/-! Restriction commutes with the actual bounded spatial coefficient operator. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

omit [BorelSpace E] [CompleteSpace E] [BorelSpace F] [CompleteSpace F] in
theorem local_coefficient_restriction (U : Set (Vec 2))
    (C : Vec 2 → E →L[ℝ] F) (hc : Continuous C)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, ‖C x‖ ≤ M)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    restrictPlaneLpCLM U (planeCoefficientOperator C hc hM hb u) =
      boundedCoefficientL2CLM (U := U) C hc M hM hb (restrictPlaneLpCLM U u) := by
  apply Lp.ext
  filter_upwards [restrictPlaneLpCLM_ae U (planeCoefficientOperator C hc hM hb u),
    (planeCoefficientOperator_ae C hc hM hb u).restrict (s := U),
    boundedCoefficientL2_ae C hc M hM hb (restrictPlaneLpCLM U u),
    restrictPlaneLpCLM_ae U u] with x hr hp hl hu
  exact (hr.trans hp).trans ((congrArg (C x) hu).symm.trans hl.symm)

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The genuine natural-flow remainder is the centred slow remainder evaluated in cell coordinates. -/

variable {φ : ℝ → Vec 2 → ℝ}

theorem naturalPreparation_slow_remainder_coordinates
    (hφ : IsAdmissibleStream φ) (r σ e E : ℝ) (he : e ≠ 0)
    (yc z : Vec 2) (K : ℕ) (f : Vec 2 → Vec 2 → ℝ) :
    let Y := streamFlow φ hφ r (yc + e • z) σ
    let Yc := streamFlow φ hφ r yc σ
    let Ψ := naturalPreparationCellFlow hφ r σ e yc z
    let X0 := E⁻¹ • Yc
    let phase := e⁻¹ • Yc
    f (E⁻¹ • Y) (e⁻¹ • Y) -
      taylorSlow 0 K (fun X => f X (e⁻¹ • Y)) X0 (E⁻¹ • (Y - Yc)) =
    f (X0 + (e / E) • Ψ) (Ψ + phase) -
      taylorSlow 0 K (fun X => f X (Ψ + phase)) X0 ((e / E) • Ψ) := by
  dsimp only
  rw [naturalPreparationCellFlow_slow_coordinates hφ r σ e E he yc z,
    naturalPreparationCellFlow_fast_coordinates hφ r σ e he yc z]
  have hd : E⁻¹ • (streamFlow φ hφ r (yc + e • z) σ - streamFlow φ hφ r yc σ) =
      (e / E) • naturalPreparationCellFlow hφ r σ e yc z := by
    unfold naturalPreparationCellFlow
    rw [smul_smul]
    congr 1
    field_simp
  rw [hd, add_comm (e⁻¹ • streamFlow φ hφ r yc σ)]

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Real scaling of a genuine plane family scales its literal coupling flux. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeRawCouplingFlux_smul_ae (K : ι → ℕ) (D : ℕ) (c r : ℝ)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (w : ∀ i, PlaneHk Set.univ (K i + 1) (h i)) (i : ι) :
    planeRawCouplingFlux K D r A (fun u => c • w u) i =ᵐ[volume]
      fun x => c • planeRawCouplingFlux K D r A w i x := by
  have hall : ∀ᵐ x ∂volume, ∀ u, ∀ α : JetIndex2 (K u + 1),
      (c • w u).toFunction.jet α x = c • (w u).toFunction.jet α x := by
    apply ae_all_iff.mpr
    intro u
    apply ae_all_iff.mpr
    intro α
    exact planeCarrier_jet_smul_ae c (w u) α
  filter_upwards [hall] with x hx
  unfold planeRawCouplingFlux
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [← map_smul]
  congr 1
  apply (WithLp.ext_iff 2).mpr
  funext word
  exact hx u _

end AVRegularity.CycleJointProofs
end
