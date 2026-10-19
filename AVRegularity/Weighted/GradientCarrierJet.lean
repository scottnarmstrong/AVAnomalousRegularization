-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Weighted.PlaneH1CoefficientOperator
public import AVRegularity.Weighted.SlowBasisProjectionBound
import AVRegularity.Weighted.MetricWordCoefficientArrayBound
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.KernelEnergy
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! The same literal scalar weight acts consistently on the `L²` and `H¹` carriers. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The Sobolev coefficient operator has its literal scalar value on ambient plane `L²`. -/
theorem planeH1ScalarMultiplier_value_ae
    (c : Vec 2 → ℝ) (hC : ContDiff ℝ 1 (fun x => scalarFiberCoefficient (E := E) (c x)))
    (Jb : Fin 2 → ℝ)
    (hb : ∀ l x, ‖coefficientDerivativeArray
      (fun x => scalarFiberCoefficient (E := E) (c x)) l.val x‖ ≤ Jb l)
    (u : PlaneHk Set.univ 1 E) :
    planeHkValueOperator (E := E) 1
      (planeH1CoefficientOperator (fun x => scalarFiberCoefficient (E := E) (c x)) hC Jb hb u) =ᵐ[volume]
      fun x => c x • planeHkValueOperator (E := E) 1 u x := by
  have hm := planeMulCoefficient_toFunction_value_ae u
    (fun x => scalarFiberCoefficient (E := E) (c x)) hC hb
  change (∀ᵐ x ∂volume.restrict (Set.univ : Set (Vec 2)),
    (u.mulCoefficient (fun x => scalarFiberCoefficient (E := E) (c x)) hC hb).toFunction.jet
      (valueIndex2 1) x = scalarFiberCoefficient (E := E) (c x)
        (u.toFunction.jet (valueIndex2 1) x)) at hm
  have hm' : ∀ᵐ x ∂volume,
      (u.mulCoefficient (fun x => scalarFiberCoefficient (E := E) (c x)) hC hb).toFunction.jet
        (valueIndex2 1) x = c x • u.toFunction.jet (valueIndex2 1) x := by
    simpa only [Measure.restrict_univ, scalarFiberCoefficient_apply] using hm
  filter_upwards [hm',
    univToPlane_ae ((u.mulCoefficient (fun x => scalarFiberCoefficient (E := E) (c x)) hC hb).val
      (valueIndex2 1)), univToPlane_ae (u.val (valueIndex2 1))] with x hmx ho hi
  exact ho.trans (hmx.trans (congrArg (fun e => c x • e) hi.symm))

/-- Squared `L²` multiplication and `H¹` multiplication by the squared weight intertwine exactly. -/
theorem planeScalarMultiplier_square_H1
    (c : Vec 2 → ℝ) (hc : Continuous c) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |c x| ≤ M)
    (hC : ContDiff ℝ 1 (fun x => scalarFiberCoefficient (E := E) (c x ^ 2)))
    (Jb : Fin 2 → ℝ)
    (hJb : ∀ l x, ‖coefficientDerivativeArray
      (fun x => scalarFiberCoefficient (E := E) (c x ^ 2)) l.val x‖ ≤ Jb l)
    (u : PlaneHk Set.univ 1 E) :
    (planeScalarMultiplier (E := E) c hc hM hb).adjoint
      (planeScalarMultiplier c hc hM hb (planeHkValueOperator (E := E) 1 u)) =
      planeHkValueOperator (E := E) 1
        (planeH1CoefficientOperator (fun x => scalarFiberCoefficient (E := E) (c x ^ 2)) hC Jb hJb u) := by
  rw [planeScalarMultiplier_adjoint]
  apply Lp.ext
  exact (planeScalarMultiplier_square_ae c hc hM hb _).trans
    (planeH1ScalarMultiplier_value_ae (fun x => c x ^ 2) hC Jb hJb u).symm

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! The actual interval drift and metric supply an energy dual without extra PDE premises. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The prescribed interval velocity, extended only in time, acts on the true plane gradient. -/
def planeIntervalTransport (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hvc : ∀ t ∈ Set.Icc a b, Continuous (v t))
    (M : ℝ) (hvb : ∀ t ∈ Set.Icc a b, ∀ z, ‖v t z‖ ≤ M) :
    ℝ → PlaneFluxL2 E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)) :=
  fun t => planeScalarTransport (planeIntervalCoefficient a b hab v t)
    (planeIntervalVelocity_continuous a b hab v hvc t) (le_max_right _ _)
    (planeIntervalVelocity_bound a b hab v M hvb t)

/-- The prescribed symmetric near-identity interval metric acts on the true plane gradient. -/
def planeIntervalDiffusion (a b : ℝ) (hab : a ≤ b)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGc : ∀ t ∈ Set.Icc a b, ∀ k j, Continuous (fun z => G t z k j))
    (g : ℝ) (hg4 : g ≤ 1 / 4) (hG : IsMetricNearIdentity G g)
    (hsym : ∀ t ∈ Set.Icc a b, ∀ z, (G t z).IsSymm) :
    ℝ → PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E :=
  fun t => planeScalarDiffusion (planeIntervalCoefficient a b hab G t)
    (planeIntervalMetric_continuous a b hab G hGc t) (by norm_num : (0 : ℝ) ≤ 5 / 4)
    (planeIntervalMetric_bound a b hab G g hg4 hG hsym t)

/-- The exact hypotheses on measurable-time coefficients suffice for the weak dual time class. -/
theorem planeIntervalDual_memLp (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hvc : ∀ t ∈ Set.Icc a b, Continuous (v t))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (M : ℝ) (hvb : ∀ t ∈ Set.Icc a b, ∀ z, ‖v t z‖ ≤ M)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGc : ∀ t ∈ Set.Icc a b, ∀ k j, Continuous (fun z => G t z k j))
    (hGm : Measurable (fun p : Set.Icc a b × Vec 2 => G p.1 p.2))
    (g : ℝ) (hg4 : g ≤ 1 / 4) (hG : IsMetricNearIdentity G g)
    (hsym : ∀ t ∈ Set.Icc a b, ∀ z, (G t z).IsSymm)
    (u : ℝ → PlaneHk Set.univ 1 E) (K : ℕ)
    (F : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hu : MemLp u 2 (volume.restrict (Set.Icc a b)))
    (hF : MemLp F 2 (volume.restrict (Set.Icc a b))) :
    MemLp (fun t => planeWeakDualRepresentative
      (planeIntervalTransport a b hab v hvc M hvb t)
      (planeIntervalDiffusion a b hab G hGc g hg4 hG hsym t)
      (u t) (planeFluxValueOperator (E := E) K (F t)))
      2 (volume.restrict (Set.Icc a b)) := by
  apply planeScalarDual_memLp
    (planeIntervalCoefficient a b hab v) (planeIntervalCoefficient a b hab G)
    (planeIntervalVelocity_continuous a b hab v hvc)
    (planeIntervalMetric_continuous a b hab G hGc)
  · intro k
    exact (measurable_pi_apply k).comp (planeIntervalCoefficient_measurable a b hab v hvm)
  · intro k j
    exact (measurable_pi_apply j).comp ((measurable_pi_apply k).comp
      (planeIntervalCoefficient_measurable a b hab G hGm))
  · exact hu
  · exact planeFluxValueOperator_memLp K F hF
end

/-! Actual plane metric multiplication retains the uniform energy coercivity. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- The squared flux Hilbert norm is the integral of its component gradient energies. -/
theorem planeFlux_normSq_eq_integral (u : PlaneFluxL2 E) :
    ‖u‖ ^ 2 = ∫ x, ∑ k : Fin 2, ‖u k x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, planeFlux_inner_eq_integral]
  simp only [real_inner_self_eq_norm_sq]

omit [BorelSpace E] [CompleteSpace E] in
/-- Metric multiplication has the exact near-identity coercivity on the actual plane flux carrier. -/
theorem planeScalarDiffusion_energy_lower
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ)
    (hg4 : g ≤ 1 / 4) (hG : IsMetricNearIdentity G g) (t : ℝ)
    (hc : ∀ k j, Continuous (fun x => G t x k j)) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ k j x, |G t x k j| ≤ M) (u : PlaneFluxL2 E) :
    (3 / 4 : ℝ) * ‖u‖ ^ 2 ≤ inner ℝ (planeScalarDiffusion (G t) hc hM hb u) u := by
  let D := planeScalarDiffusion (G t) hc hM hb u
  have hD : Integrable (fun x => ∑ k : Fin 2, inner ℝ (D k x) (u k x)) volume :=
    integrable_finsetSum _ (fun k _ => L2.integrable_inner (D k) (u k))
  have hm : ∀ᵐ x ∂volume, ∀ k : Fin 2, D k x = ∑ j : Fin 2, G t x k j • u j x :=
    ae_all_iff.mpr (fun k => planeScalarDiffusion_ae (G t) hc hM hb u k)
  have hQ : Integrable (fun x => ∑ k : Fin 2, ∑ j : Fin 2,
      G t x k j * inner ℝ (u j x) (u k x)) volume := by
    apply hD.congr
    filter_upwards [hm] with x hx
    apply Finset.sum_congr rfl
    intro k _
    rw [hx k]
    simp only [sum_inner, real_inner_smul_left]
  have he : Integrable (fun x => ∑ k : Fin 2, ‖u k x‖ ^ 2) volume := by
    apply integrable_finsetSum
    intro k _
    simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) (u k) (u k)
  rw [planeFlux_normSq_eq_integral, planeScalarDiffusion_inner_eq_integral,
    ← integral_const_mul]
  apply integral_mono (he.const_mul _) hQ
  intro x
  simpa only [real_inner_comm] using
    nearIdentity_hilbert_quadratic_lower G g hg4 hG t x (fun k => u k x)
end

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization
namespace AVRegularity.Weighted

/-! Actual coefficient operators do not depend on the chosen uniform norm budget. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
theorem planeScalarTransport_congr
    (v v' : Vec 2 → Vec 2) (he : v = v')
    (hc : ∀ k, Continuous (fun x => v x k)) (hc' : ∀ k, Continuous (fun x => v' x k))
    {M M' : ℝ} (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hb : ∀ k x, |v x k| ≤ M) (hb' : ∀ k x, |v' x k| ≤ M') :
    planeScalarTransport (E := E) v hc hM hb = planeScalarTransport v' hc' hM' hb' := by
  subst v'
  apply ContinuousLinearMap.ext
  intro z
  apply Lp.ext
  exact (planeScalarTransport_ae v hc hM hb z).trans
    (planeScalarTransport_ae v hc' hM' hb' z).symm

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
theorem planeScalarDiffusion_congr
    (G G' : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (he : G = G')
    (hc : ∀ k j, Continuous (fun x => G x k j))
    (hc' : ∀ k j, Continuous (fun x => G' x k j))
    {M M' : ℝ} (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hb : ∀ k j x, |G x k j| ≤ M) (hb' : ∀ k j x, |G' x k j| ≤ M') :
    planeScalarDiffusion (E := E) G hc hM hb = planeScalarDiffusion G' hc' hM' hb' := by
  subst G'
  apply ContinuousLinearMap.ext
  intro z
  apply PiLp.ext
  intro k
  apply Lp.ext
  exact (planeScalarDiffusion_ae G hc hM hb z k).trans
    (planeScalarDiffusion_ae G hc' hM' hb' z k).symm

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.Weighted

/-! Compact spatial scalar weights have actual Sobolev multiplier budgets. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem compact_spatial_coefficient_bounds
    (C : Vec 2 → E →L[ℝ] E) (hC : ContDiff ℝ 1 C) (hs : HasCompactSupport C) :
    ∃ A : Fin 2 → ℝ, ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l := by
  obtain ⟨M0, h0⟩ := hC.continuous.bounded_above_of_compact_support hs
  obtain ⟨M1, h1⟩ := (hC.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (hs.fderiv ℝ)
  let M := max 0 (max M0 M1)
  have hM : 0 ≤ M := le_max_left _ _
  refine ⟨fun _ => 2 * M, fun l x => planeH1_coefficient_array_bound C hM ?_ ?_ l x⟩
  · intro y
    exact (h0 y).trans ((le_max_left M0 M1).trans (le_max_right _ _))
  · intro y
    exact (h1 y).trans ((le_max_right M0 M1).trans (le_max_right _ _))

theorem planeH1_eq_of_value_ae (u z : PlaneHk Set.univ 1 E)
    (he : planeHkValueOperator (E := E) 1 u =ᵐ[volume]
      planeHkValueOperator (E := E) 1 z) : u = z := by
  apply PlaneHk.ext_value isOpen_univ
  apply univToPlane.injective
  exact Lp.ext he

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Window-only coefficients give the principal time actions for every actual H1 derivative slice. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeIntervalActions_memLp (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hvc : ∀ t ∈ Set.Icc a b, Continuous (v t))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (M : ℝ) (hvb : ∀ t ∈ Set.Icc a b, ∀ z, ‖v t z‖ ≤ M)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGc : ∀ t ∈ Set.Icc a b, ∀ k j, Continuous (fun z => G t z k j))
    (hGm : Measurable (fun p : Set.Icc a b × Vec 2 => G p.1 p.2))
    (g : ℝ) (hg4 : g ≤ 1 / 4) (hG : IsMetricNearIdentity G g)
    (hsym : ∀ t ∈ Set.Icc a b, ∀ z, (G t z).IsSymm)
    (u : ℝ → PlaneHk Set.univ 1 E)
    (hu : MemLp u 2 (volume.restrict (Set.Icc a b))) :
    MemLp (fun t => planeIntervalTransport a b hab v hvc M hvb t
      (planeH1GradientOperator (u t))) 2 (volume.restrict (Set.Icc a b)) ∧
    MemLp (fun t => planeIntervalDiffusion a b hab G hGc g hg4 hG hsym t
      (planeH1GradientOperator (u t))) 2 (volume.restrict (Set.Icc a b)) := by
  apply planeScalarActions_memLp
    (planeIntervalCoefficient a b hab v) (planeIntervalCoefficient a b hab G)
    (planeIntervalVelocity_continuous a b hab v hvc)
    (planeIntervalMetric_continuous a b hab G hGc)
  · intro k
    exact (measurable_pi_apply k).comp (planeIntervalCoefficient_measurable a b hab v hvm)
  · intro k j
    exact (measurable_pi_apply j).comp ((measurable_pi_apply k).comp
      (planeIntervalCoefficient_measurable a b hab G hGm))
  · exact hu

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization Set
namespace AVRegularity.Weighted

/-! On the solution window, clamped measurable-time operators are the prescribed operators. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
theorem planeIntervalTransport_eq_of_mem (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hvc : ∀ t ∈ Icc a b, Continuous (v t))
    (M : ℝ) (hM : 0 ≤ M) (hvb : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ M)
    (t : ℝ) (ht : t ∈ Icc a b)
    (hc : ∀ k, Continuous (fun x => v t x k))
    (hb : ∀ k x, |v t x k| ≤ M) :
    planeIntervalTransport (E := E) a b hab v hvc M hvb t =
      planeScalarTransport (v t) hc hM hb := by
  exact planeScalarTransport_congr _ _ (planeIntervalCoefficient_of_mem a b hab v t ht)
    _ hc (le_max_right M 0) hM _ hb

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
theorem planeIntervalDiffusion_eq_of_mem (a b : ℝ) (hab : a ≤ b)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGc : ∀ t ∈ Icc a b, ∀ k j, Continuous (fun x => G t x k j))
    (g : ℝ) (hg4 : g ≤ 1 / 4) (hG : IsMetricNearIdentity G g)
    (hsym : ∀ t ∈ Icc a b, ∀ x, (G t x).IsSymm)
    (t : ℝ) (ht : t ∈ Icc a b)
    (hc : ∀ k j, Continuous (fun x => G t x k j))
    (hb : ∀ k j x, |G t x k j| ≤ 5 / 4) :
    planeIntervalDiffusion (E := E) a b hab G hGc g hg4 hG hsym t =
      planeScalarDiffusion (G t) hc (by norm_num : (0 : ℝ) ≤ 5 / 4) hb := by
  exact planeScalarDiffusion_congr _ _ (planeIntervalCoefficient_of_mem a b hab G t ht)
    _ hc (by norm_num) (by norm_num) _ hb

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.Weighted

/-! The actual Sobolev representatives in the scalar weak equation. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The raw scalar weak RHS keeps the weak identity's separate diffusion terms and zero carrier. -/
def planeScalarRawRhs (K : ℕ) (v : Vec 2 → Vec 2)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (w : PlaneHk Set.univ (K + 1) E)
    (F : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (φ : PlaneHk Set.univ 1 E) (x : Vec 2) : ℝ :=
  -(∑ k : Fin 2, v x k * inner ℝ
      (w.toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩ x)
      (φ.toFunction.jet (valueIndex2 1) x))
    - (∑ k : Fin 2, inner ℝ
      (w.toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩ x)
      (φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩ x))
    - (∑ k : Fin 2, inner ℝ
      ((∑ j : Fin 2, (G x - 1) k j •
        w.toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => j⟩ x) +
        F.toFunction.jet (valueIndex2 K) x k)
      (φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩ x))
    + inner ℝ ((0 : PlaneHk Set.univ K E).toFunction.jet (valueIndex2 K) x)
      (φ.toFunction.jet (valueIndex2 1) x)

/-- The actual scalar Riesz representative pairs to the exact raw spatial RHS. -/
theorem planeScalarDual_pair_eq_raw (K : ℕ)
    (v : Vec 2 → Vec 2) (hvc : ∀ k, Continuous (fun x => v x k))
    {Mv : ℝ} (hMv : 0 ≤ Mv) (hvb : ∀ k x, |v x k| ≤ Mv)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGc : ∀ k j, Continuous (fun x => G x k j))
    {MG : ℝ} (hMG : 0 ≤ MG) (hGb : ∀ k j x, |G x k j| ≤ MG)
    (w : PlaneHk Set.univ (K + 1) E)
    (F : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (φ : PlaneHk Set.univ 1 E) :
    inner ℝ (planeWeakDualRepresentative
      (planeScalarTransport v hvc hMv hvb) (planeScalarDiffusion G hGc hMG hGb)
      (truncatePlaneHk (E := E) (by omega) w) (planeFluxValueOperator (E := E) K F)) φ =
      ∫ x, planeScalarRawRhs K v G w F φ x := by
  rw [planeScalarDual_pair_eq_integral]
  have hw : ∀ᵐ x ∂volume, ∀ k : Fin 2,
      planeH1GradientOperator (E := E) (truncatePlaneHk (by omega) w) k x =
        w.toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩ x := by
    apply ae_all_iff.mpr
    intro k
    exact univToPlane_ae _
  have hφ : ∀ᵐ x ∂volume, ∀ k : Fin 2,
      planeH1GradientOperator (E := E) φ k x =
        φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩ x :=
    ae_all_iff.mpr (fun k => univToPlane_ae _)
  have hF : ∀ᵐ x ∂volume, ∀ k : Fin 2,
      planeFluxValueOperator (E := E) K F k x = F.toFunction.jet (valueIndex2 K) x k :=
    ae_all_iff.mpr (fun k => planeFluxValueOperator_ae K F k)
  have hzero : (0 : PlaneHk Set.univ K E).toFunction.jet (valueIndex2 K) =ᵐ[volume]
      fun _ => 0 := by
    change (fun x => ((0 : JetL2 (volume.restrict Set.univ) K E) (valueIndex2 K)) x) =ᵐ[volume] _
    simp only [PiLp.zero_apply]
    have hz := Lp.coeFn_zero E 2 (volume.restrict (Set.univ : Set (Vec 2)))
    change (∀ᵐ x ∂volume.restrict (Set.univ : Set (Vec 2)),
      (0 : Lp E 2 (volume.restrict Set.univ)) x = 0) at hz
    rw [ae_restrict_iff' MeasurableSet.univ] at hz
    filter_upwards [hz] with x hx
    exact hx (Set.mem_univ x)
  apply integral_congr_ae
  filter_upwards [hw, hφ, hF, hzero, univToPlane_ae (φ.val (valueIndex2 1))]
    with x hwx hφx hFx hzx hvx
  simp only [planeHkValueOperator_apply, hvx, planeScalarRawRhs, hzx, inner_zero_left, add_zero]
  simp_rw [hwx, hφx, hFx]
  have ha := metricDeviation_weak_pairing (G x)
    (fun k => w.toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩ x)
    (fun k => φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩ x)
    (fun k => F.toFunction.jet (valueIndex2 K) x k)
  simp only [PlaneHk.toFunction, planeJetRepresentative] at ha ⊢
  linarith [ha]

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Weighted

/-! Multiply the stored derivative array by a testing weight without differentiating the weight. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def scaledRawJet {K : ℕ} (s : Vec 2 → ℝ) (D : RawJet2 K E) : RawJet2 K E :=
  fun a x => s x • D a x

theorem scaledRawJet_memL2 {K : ℕ} {U : Set (Vec 2)}
    (s : Vec 2 → ℝ) (hs : Continuous s) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, |s x| ≤ M) (D : RawJet2 K E) (hD : JetMemL2On U D) :
    JetMemL2On U (scaledRawJet s D) := by
  intro a
  change MemLp (fun x => s x • D a x) 2 (volume.restrict U)
  have hh := memLp_operator_mul (C := fun x => scalarFiberCoefficient (E := E) (s x))
    (hs.smul continuous_const) (hD a) hM
    (fun x => (scalarFiberCoefficient_norm_le (E := E) (s x)).trans (hb x))
  simpa only [scalarFiberCoefficient_apply] using hh

theorem driftMaskTerm_scaledRawJet {K j : ℕ} (hj : j ≤ K)
    (v : Vec 2 → Vec 2) (s : Vec 2 → ℝ) (D : RawJet2 (K + 1) E)
    (m : PositionMask j) (w : DerivativeWord2 j) (x : Vec 2) :
    driftMaskTerm hj v (scaledRawJet s D) m w x = s x • driftMaskTerm hj v D m w x := by
  unfold driftMaskTerm scalarArrayAct driftMaskGradient scaledRawJet
  dsimp only
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact smul_comm _ _ _

theorem metricMaskTerm_scaledRawJet {K j : ℕ} (hj : j ≤ K)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (s : Vec 2 → ℝ)
    (D : RawJet2 (K + 1) E) (m : PositionMask j) (w : DerivativeWord2 j) (x : Vec 2) :
    metricMaskTerm hj G (scaledRawJet s D) m w x = s x • metricMaskTerm hj G D m w x := by
  apply PiLp.ext
  intro a
  unfold metricMaskTerm finiteMetricFlux driftMaskGradient scaledRawJet
  simp only [PiLp.smul_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact smul_comm _ _ _

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
namespace AVRegularity.Weighted

/-! The energy of a scaled raw derivative array is the literal weighted spatial energy. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

theorem scaledRawJet_derivativeNormSq {K : ℕ} {U : Set (Vec 2)}
    (s : Vec 2 → ℝ) (D : RawJet2 K E) (hD : JetMemL2On U (scaledRawJet s D))
    (j : Fin (K + 1)) :
    derivativeNormSq (jetToL2 (scaledRawJet s D) hD) j =
      ∫ x, s x ^ 2 * (∑ w : DerivativeWord2 j.val, ‖D ⟨j, w⟩ x‖ ^ 2)
        ∂volume.restrict U := by
  have he (w : DerivativeWord2 j.val) :
      ‖(hD ⟨j, w⟩).toLp (scaledRawJet s D ⟨j, w⟩)‖ ^ 2 =
        ∫ x, s x ^ 2 * ‖D ⟨j, w⟩ x‖ ^ 2 ∂volume.restrict U := by
    rw [normSq_toLp_eq_integral (hD ⟨j, w⟩)]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by
      simp only [scaledRawJet, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs])
  have hi (w : DerivativeWord2 j.val) : Integrable
      (fun x => s x ^ 2 * ‖D ⟨j, w⟩ x‖ ^ 2) (volume.restrict U) := by
    convert integrable_normSq_of_memLp (hD ⟨j, w⟩) using 1
    funext x
    simp only [scaledRawJet, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  change (∑ w : DerivativeWord2 j.val,
    ‖(hD ⟨j, w⟩).toLp (scaledRawJet s D ⟨j, w⟩)‖ ^ 2) = _
  simp_rw [he]
  rw [← integral_finsetSum Finset.univ (fun w _ => hi w)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => (Finset.mul_sum _ _ _).symm)

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Bounded testing weights preserve integrability of every actual metric mask. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem scaledMetricMasks_memLp {K : ℕ} {U : Set (Vec 2)}
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k a, ContDiff ℝ (K : ℕ) (fun x => G x k a))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ (l : Fin (K + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G y k a) x‖ ≤ M l)
    (s : Vec 2 → ℝ) (hs : Continuous s) {C : ℝ} (hC : 0 ≤ C)
    (hsb : ∀ x, |s x| ≤ C) (D : RawJet2 (K + 1) E) (hD : JetMemL2On U D) :
    ∀ (j : Fin (K + 1)) (m : PositionMask j.val) (w : DerivativeWord2 j.val),
      MemLp (metricMaskTerm (Nat.le_of_lt_succ j.isLt) G (scaledRawJet s D) m w)
        2 (volume.restrict U) := by
  have hscaled := scaledRawJet_memL2 s hs hC hsb D hD
  intro j m w
  let l : Fin (K + 1) := ⟨maskLeftLength j.val m,
    Nat.lt_succ_of_le ((maskLeftLength_le j.val m).trans (Nat.le_of_lt_succ j.isLt))⟩
  apply metricMaskTerm_memLp (Nat.le_of_lt_succ j.isLt) G hG
    (scaledRawJet s D) hscaled m w (M l)
  intro x k a
  simpa only [Real.norm_eq_abs] using
    (orderedScalarDerivative_norm_le (fun y => G y k a) l.val
      ((hG k a).of_le (by exact_mod_cast Nat.le_of_lt_succ l.isLt))
      (maskWordEquiv 2 j.val m w).1 x).trans (hb l x k a)

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Stored gradients after scalar weighting have exactly the retained factorial production. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

theorem scaledRawJet_gradFactorialNormSq {K : ℕ} {U : Set (Vec 2)}
    (ρ : ℝ) (s : Vec 2 → ℝ) (D : RawJet2 (K + 1) E)
    (hD : JetMemL2On U (scaledRawJet s D)) :
    gradFactorialNormSq ρ (jetToL2 (scaledRawJet s D) hD) =
      ∑ j : Fin (K + 1), factorialWeight ρ j.val *
        (∫ x, s x ^ 2 * (∑ w : DerivativeWord2 j.val,
          ‖(WithLp.toLp 2 (fun k : Fin 2 =>
            D ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, Fin.snoc w k⟩ x) :
            PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) ∂volume.restrict U) := by
  unfold gradFactorialNormSq
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change derivativeNormSq (jetToL2 (scaledRawJet s D) hD)
    ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ = _
  rw [scaledRawJet_derivativeNormSq]
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  simp only [PiLp.norm_sq_eq_of_L2]
  rw [← (Fin.snocEquiv (fun _ : Fin (j.val + 1) => Fin 2)).sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  rfl
end

/-! Literal factorial energy budgets for stored raw arrays. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def rawWeightedFactorialEnergy {K : ℕ} (ρ : ℝ) (q : Vec 2 → ℝ)
    (D : RawJet2 K E) : ℝ :=
  ∑ j : Fin (K + 1), factorialWeight ρ j.val *
    ∑ w : DerivativeWord2 j.val, ∫ x, q x * ‖D ⟨j, w⟩ x‖ ^ 2

def rawWeightedGradientEnergy {K : ℕ} (ρ : ℝ) (q : Vec 2 → ℝ)
    (D : RawJet2 (K + 1) E) : ℝ :=
  ∑ j : Fin (K + 1), factorialWeight ρ j.val *
    ∑ w : DerivativeWord2 j.val, ∫ x, q x *
      ‖(WithLp.toLp 2 (fun k : Fin 2 =>
        D ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, Fin.snoc w k⟩ x) :
        PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2

omit [InnerProductSpace ℝ E] in
theorem rawWeightedFactorialEnergy_nonneg {K : ℕ} (ρ : ℝ) (q : Vec 2 → ℝ)
    (hq : ∀ x, 0 ≤ q x) (D : RawJet2 K E) : 0 ≤ rawWeightedFactorialEnergy ρ q D := by
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (factorialWeight_nonneg _ _)
  apply Finset.sum_nonneg
  intro w _
  exact integral_nonneg (fun x => mul_nonneg (hq x) (sq_nonneg _))

omit [InnerProductSpace ℝ E] in
theorem rawWeightedGradientEnergy_nonneg {K : ℕ} (ρ : ℝ) (q : Vec 2 → ℝ)
    (hq : ∀ x, 0 ≤ q x) (D : RawJet2 (K + 1) E) : 0 ≤ rawWeightedGradientEnergy ρ q D := by
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (factorialWeight_nonneg _ _)
  apply Finset.sum_nonneg
  intro w _
  exact integral_nonneg (fun x => mul_nonneg (hq x) (sq_nonneg _))
end

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.KernelEnergy
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.Weighted

/-! Literal first derivatives of the actual Sobolev coefficient multiplier. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem scalarFiberCoefficient_fderiv_apply
    (c : Vec 2 → ℝ) (hc : Differentiable ℝ c) (x z : Vec 2) (e : E) :
    fderiv ℝ (fun y => scalarFiberCoefficient (E := E) (c y)) x z e =
      fderiv ℝ c x z • e := by
  let L : ℝ →L[ℝ] (E →L[ℝ] E) :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (ContinuousLinearMap.id ℝ E)
  have hC : (fun y => scalarFiberCoefficient (E := E) (c y)) = L ∘ c := rfl
  rw [hC, (L.hasFDerivAt.comp x (hc x).hasFDerivAt).fderiv]
  rfl

theorem planeH1CoefficientOperator_gradient_ae
    (C : Vec 2 → E →L[ℝ] E) (hC : ContDiff ℝ 1 C) (A : Fin 2 → ℝ)
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l)
    (u : PlaneHk Set.univ 1 E) (i : Fin 2) :
    planeH1GradientOperator (E := E) (planeH1CoefficientOperator C hC A hb u) i =ᵐ[volume]
      fun x => C x (planeH1GradientOperator (E := E) u i x) +
        fderiv ℝ C x (basisVec i) (planeHkValueOperator (E := E) 1 u x) := by
  have h := PlaneHkFunction.toHk_toFunction_ae (u.toFunction.mulCoefficient C hC hb)
    (⟨⟨1, by omega⟩, fun _ : Fin 1 => i⟩ : JetIndex2 1)
  have hraw : (planeH1CoefficientOperator C hC A hb u).toFunction.jet
      ⟨⟨1, by omega⟩, fun _ : Fin 1 => i⟩ =ᵐ[volume]
      multiplicationRawJet C u.toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => i⟩ := by
    simpa only [Measure.restrict_univ, planeH1CoefficientOperator_apply,
      PlaneHk.mulCoefficient, PlaneHkFunction.mulCoefficient] using h
  have hi := univToPlane_ae (u.val ⟨⟨1, by omega⟩, fun _ : Fin 1 => i⟩)
  have hv := univToPlane_ae (u.val (valueIndex2 1))
  have ho := univToPlane_ae ((planeH1CoefficientOperator C hC A hb u).val
    ⟨⟨1, by omega⟩, fun _ : Fin 1 => i⟩)
  filter_upwards [hraw, hi, hv, ho] with x hr hi hv ho
  rw [multiplicationRawJet_first_snoc (E := E) (F := E) (K := 1)
    (by omega) C u.toFunction.jet i x] at hr
  apply ho.trans
  apply hr.trans
  change C x (u.val ⟨⟨1, by omega⟩, fun _ : Fin 1 => i⟩ x) +
    fderiv ℝ C x (basisVec i) (u.val (valueIndex2 1) x) =
    C x (univToPlane (u.val ⟨⟨1, by omega⟩, fun _ : Fin 1 => i⟩) x) +
    fderiv ℝ C x (basisVec i) (univToPlane (u.val (valueIndex2 1)) x)
  rw [hi, hv]

theorem planeH1ScalarMultiplier_gradient_ae
    (c : Vec 2 → ℝ) (hc : ContDiff ℝ 1 c)
    (hC : ContDiff ℝ 1 (fun x => scalarFiberCoefficient (E := E) (c x)))
    (A : Fin 2 → ℝ)
    (hb : ∀ l x, ‖coefficientDerivativeArray
      (fun x => scalarFiberCoefficient (E := E) (c x)) l.val x‖ ≤ A l)
    (u : PlaneHk Set.univ 1 E) (i : Fin 2) :
    planeH1GradientOperator (E := E)
      (planeH1CoefficientOperator (fun x => scalarFiberCoefficient (E := E) (c x)) hC A hb u) i =ᵐ[volume]
      fun x => c x • planeH1GradientOperator (E := E) u i x +
        fderiv ℝ c x (basisVec i) • planeHkValueOperator (E := E) 1 u x := by
  have h := planeH1CoefficientOperator_gradient_ae _ hC A hb u i
  filter_upwards [h] with x hx
  rw [hx, scalarFiberCoefficient_apply,
    scalarFiberCoefficient_fderiv_apply c (hc.differentiable (by norm_num))]

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! The integral of the complete gradient tensor is its finite stored-word energy sum. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

omit [InnerProductSpace ℝ E] [MeasurableSpace E] in
theorem rawWeightedGradient_integral_sum {K : ℕ} (ρ : ℝ) (q : Vec 2 → ℝ)
    (hq : AEStronglyMeasurable q volume) {M : ℝ} (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ M)
    (D : RawJet2 (K + 1) E) (hD : JetMemL2On Set.univ D) :
    (∑ j : Fin (K + 1), factorialWeight ρ j.val *
      (∫ x, q x * (∑ w : DerivativeWord2 j.val,
        ‖(WithLp.toLp 2 (fun k : Fin 2 =>
          D ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, Fin.snoc w k⟩ x) :
          PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2))) =
      rawWeightedGradientEnergy ρ q D := by
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply weightedSource_integral_sum q hq hb
  intro w
  apply memLp_piLp_iff.mpr
  intro k
  simpa only [WithLp.ofLp_toLp, Measure.restrict_univ] using
    hD ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, Fin.snoc w k⟩

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization
namespace AVRegularity.Weighted

/-! Spatial integrability of the compact energy test and its bounded error budgets. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem finiteLp_normSq_integrable (U : PiLp 2 (fun _ : Fin 2 => Lp E 2
    (volume : Measure (Vec 2)))) :
    Integrable (fun x => ‖(WithLp.toLp 2 (fun i => U i x) :
      PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) volume := by
  have he : (fun x => ‖(WithLp.toLp 2 (fun i => U i x) :
      PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) = fun x => ∑ i : Fin 2, ‖U i x‖ ^ 2 := by
    funext x
    exact PiLp.norm_sq_eq_of_L2 _ _
  rw [he]
  apply integrable_finsetSum
  intro i _
  simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) (U i) (U i)

theorem bounded_scalar_finiteLp_normSq_integrable
    (U : PiLp 2 (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2))))
    (q : Vec 2 → ℝ) (hq : AEStronglyMeasurable q volume) {M : ℝ}
    (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ M) :
    Integrable (fun x => q x * ‖(WithLp.toLp 2 (fun i => U i x) :
      PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) volume :=
  (finiteLp_normSq_integrable U).bdd_mul hq hb

theorem bounded_scalar_Lp_normSq_integrable
    (U : Lp E 2 (volume : Measure (Vec 2)))
    (q : Vec 2 → ℝ) (hq : AEStronglyMeasurable q volume) {M : ℝ}
    (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ M) :
    Integrable (fun x => q x * ‖U x‖ ^ 2) volume := by
  have hi : Integrable (fun x => ‖U x‖ ^ 2) volume := by
    simpa only [real_inner_self_eq_norm_sq] using L2.integrable_inner (𝕜 := ℝ) U U
  exact hi.bdd_mul hq hb

theorem compact_scalar_gradient_pairing_integrable
    (du : PiLp 2 (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2))))
    (U : Lp E 2 (volume : Measure (Vec 2)))
    (c : Fin 2 → Vec 2 → ℝ) (hc : ∀ i, Continuous (c i))
    (hs : ∀ i, HasCompactSupport (c i)) :
    Integrable (fun x => inner ℝ (∑ i : Fin 2, c i x • du i x) (U x)) volume := by
  have he : (fun x => inner ℝ (∑ i : Fin 2, c i x • du i x) (U x)) =
      fun x => ∑ i : Fin 2, c i x * inner ℝ (du i x) (U x) := by
    funext x
    simp only [sum_inner, real_inner_smul_left]
  rw [he]
  apply integrable_finsetSum
  intro i _
  obtain ⟨M, hM⟩ := (hc i).bounded_above_of_compact_support (hs i)
  exact (L2.integrable_inner (𝕜 := ℝ) (du i) U).bdd_mul
    (hc i).aestronglyMeasurable (Filter.Eventually.of_forall hM)
end

/-! Integrability of bounded metric quadratic forms on the actual L2 components. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem bounded_metric_quadratic_integrable
    (du : PiLp 2 (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2))))
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k j, Continuous (fun x => G x k j))
    {MG : ℝ} (_hMG : 0 ≤ MG) (hGb : ∀ k j x, |G x k j| ≤ MG)
    (q : Vec 2 → ℝ) (hq : Continuous q) {Mq : ℝ} (hMq : 0 ≤ Mq)
    (hqb : ∀ x, |q x| ≤ Mq) :
    Integrable (fun x => q x * ∑ k : Fin 2, ∑ j : Fin 2,
      G x k j * inner ℝ (du k x) (du j x)) volume := by
  have he : (fun x => q x * ∑ k : Fin 2, ∑ j : Fin 2,
      G x k j * inner ℝ (du k x) (du j x)) =
      fun x => ∑ k : Fin 2, ∑ j : Fin 2,
        (q x * G x k j) * inner ℝ (du k x) (du j x) := by
    funext x
    simp only [Finset.mul_sum, mul_assoc]
  rw [he]
  apply integrable_finsetSum
  intro k _
  apply integrable_finsetSum
  intro j _
  apply (L2.integrable_inner (𝕜 := ℝ) (du k) (du j)).bdd_mul (c := Mq * MG)
    (hq.mul (hG k j)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    change ‖q x * G x k j‖ ≤ Mq * MG
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (hqb x) (hGb k j x) (abs_nonneg _) hMq)
end

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Actual scalar divergence-form dual production and cancellation of common forcing. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
/-- Subtracting two weak right-hand sides cancels their common flux forcing. -/
theorem planeWeakDualRepresentative_sub
    (T : PlaneFluxL2 E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))
    (D : PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E)
    (u u' : PlaneHk Set.univ 1 E) (F : PlaneFluxL2 E) :
    planeWeakDualRepresentative T D u F - planeWeakDualRepresentative T D u' F =
      planeWeakDualRepresentative T D (u - u') 0 := by
  simp only [planeWeakDualRepresentative_eq_adjoint, map_sub, map_add, map_zero]
  abel

/-- The true scalar weak dual has nonpositive production when the flux forcing is zero. -/
theorem planeScalarDual_zeroFlux_nonpositive
    (v : Vec 2 → Vec 2) (hvc : ∀ k, Continuous (fun z => v z k))
    {Mv : ℝ} (hMv : 0 ≤ Mv) (hvb : ∀ k z, |v z k| ≤ Mv)
    (hv : ContDiff ℝ 1 v) (hvbound : ∃ B : ℝ, ∀ z, ‖v z‖ ≤ B)
    (hdiv : ∀ z, ∑ k : Fin 2, fderiv ℝ v z (basisVec k) k = 0)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ)
    (hg4 : g ≤ 1 / 4) (hG : IsMetricNearIdentity G g) (t : ℝ)
    (hGc : ∀ k j, Continuous (fun z => G t z k j))
    {MG : ℝ} (hMG : 0 ≤ MG) (hGb : ∀ k j z, |G t z k j| ≤ MG)
    (u : PlaneHk Set.univ 1 E) :
    inner ℝ (planeWeakDualRepresentative
      (planeScalarTransport v hvc hMv hvb) (planeScalarDiffusion (G t) hGc hMG hGb) u 0) u ≤ 0 := by
  rw [planeWeakDualRepresentative_pair, planeScalarTransport_energy_zero v hvc hMv hvb
    hv hvbound hdiv u, add_zero, neg_zero, zero_sub]
  apply neg_nonpos.mpr
  exact (by positivity : (0 : ℝ) ≤ (3 / 4) * ‖planeH1GradientOperator (E := E) u‖ ^ 2).trans
    (planeScalarDiffusion_energy_lower G g hg4 hG t hGc hMG hGb _)

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! The finite sum of actual carrier readouts equals the raw stored-array energy. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeStoredWord_factorial_energy {K : ℕ} (ρ : ℝ) (q : Vec 2 → ℝ)
    (U : PlaneHk Set.univ K E) :
    (∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
      (∫ x, q x * ‖planeJetReadoutOperator K α U x‖ ^ 2)) =
      rawWeightedFactorialEnergy ρ q U.toFunction.jet := by
  rw [Fintype.sum_sigma]
  unfold rawWeightedFactorialEnergy
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  apply integral_congr_ae
  filter_upwards [univToPlane_ae (U.val ⟨j, w⟩)] with x hx
  rw [planeJetReadoutOperator_apply, hx]
  rfl

theorem planeStoredWord_gradient_energy {K : ℕ} (ρ : ℝ) (q : Vec 2 → ℝ)
    (W : PlaneHk Set.univ (K + 1) E) :
    (∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
      (∫ x, q x * ‖(WithLp.toLp 2 (fun k : Fin 2 =>
        planeH1GradientOperator (planeWordH1SliceOperator K α W) k x) :
        PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2)) =
      rawWeightedGradientEnergy ρ q W.toFunction.jet := by
  rw [Fintype.sum_sigma]
  unfold rawWeightedGradientEnergy
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  apply integral_congr_ae
  have hh : ∀ᵐ x ∂volume, ∀ k : Fin 2,
      planeH1GradientOperator (planeWordH1SliceOperator K ⟨j, w⟩ W) k x =
        W.toFunction.jet ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, Fin.snoc w k⟩ x := by
    apply ae_all_iff.mpr
    intro k
    rw [planeWordH1Slice_gradient]
    exact univToPlane_ae _
  filter_upwards [hh] with x hx
  simp_rw [hx]

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! The value commutator production is controlled by its weighted spatial product. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem bounded_weight_value_product_integrable
    (g u : Lp E 2 (volume : Measure (Vec 2)))
    (q : Vec 2 → ℝ) (hq : AEStronglyMeasurable q volume) {M : ℝ}
    (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ M) :
    Integrable (fun x => q x * (‖g x‖ * ‖u x‖)) volume := by
  have hi : Integrable (fun x => ‖g x‖ * ‖u x‖) volume :=
    memLp_one_iff_integrable.mp ((Lp.memLp g).norm.fun_mul (Lp.memLp u).norm)
  exact hi.bdd_mul hq hb

theorem planeValueForcing_weighted_pair_abs_le
    (g u : Lp E 2 (volume : Measure (Vec 2)))
    (z : PlaneHk Set.univ 1 E)
    (q : Vec 2 → ℝ) (hq : AEStronglyMeasurable q volume) {M : ℝ}
    (hb : ∀ᵐ x ∂volume, ‖q x‖ ≤ M) (hp : ∀ᵐ x ∂volume, 0 ≤ q x)
    (hz : planeHkValueOperator (E := E) 1 z =ᵐ[volume] fun x => q x • u x) :
    |inner ℝ ((planeHkValueOperator (E := E) 1).adjoint g) z| ≤
      ∫ x, q x * (‖g x‖ * ‖u x‖) := by
  rw [planeValueForcing_pair_of_value g z u q hz]
  have hi := (L2.integrable_inner (𝕜 := ℝ) g u).bdd_mul hq hb
  have hj := bounded_weight_value_product_integrable g u q hq hb
  apply (abs_integral_le_integral_abs).trans
  apply integral_mono_ae hi.abs hj
  filter_upwards [hp] with x hx
  rw [abs_mul, abs_of_nonneg hx]
  exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm (g x) (u x)) hx

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! The weighted energy of the stored flux carrier has its literal raw-array readout. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeStoredWord_flux_energy {K : ℕ} (ρ : ℝ) (q : Vec 2 → ℝ)
    (F : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) :
    (∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
      (∫ x, q x * ‖(WithLp.toLp 2 (fun k : Fin 2 => planeJetFluxOperator K α F k x) :
        PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2)) =
      rawWeightedFactorialEnergy ρ q F.toFunction.jet := by
  rw [storedWord_sum_weighted (fun j : Fin (K + 1) => factorialWeight ρ j.val)]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  apply integral_congr_ae
  have hh : ∀ᵐ x ∂volume, ∀ k : Fin 2,
      planeJetFluxOperator K ⟨j, w⟩ F k x = F.val ⟨j, w⟩ x k := by
    apply ae_all_iff.mpr
    intro k
    exact planeJetFluxOperator_ae ⟨j, w⟩ F k
  filter_upwards [hh] with x hx
  simp_rw [hx]
  rfl

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.Weighted

/-! Every gradient carrier jet is the original word with the gradient direction appended. -/

theorem prefix_single_jet_eq_cons {K : ℕ} (j : Fin (K + 1))
    (w : DerivativeWord2 j.val) (k : Fin 2) :
    prefixJetIndex (fun _ : Fin 1 => k) (⟨j, w⟩ : JetIndex2 K) =
      (⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, Fin.cons k w⟩ : JetIndex2 (K + 1)) := by
  apply Sigma.ext (Fin.ext (Nat.add_comm 1 j.val))
  apply (Fin.heq_fun_iff (Nat.add_comm 1 j.val)).mpr
  intro a
  simp only [prefixJetIndex, Fin.append_left_eq_cons, Function.comp_apply]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeGradientTensor_jet_ae {K : ℕ} (p : PlaneHk Set.univ (K + 1) E)
    (j : Fin (K + 1)) (w : DerivativeWord2 j.val) :
    (planeGradientTensor p).val ⟨j, w⟩ =ᵐ[volume.restrict Set.univ] fun x =>
      WithLp.toLp 2 (fun k : Fin 2 =>
        p.val ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, Fin.snoc w k⟩ x) := by
  have hi (k : Fin 2) :
      (derivativePlaneHk (fun _ : Fin 1 => k) p).val ⟨j, w⟩ =
        p.val ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, Fin.snoc w k⟩ := by
    rw [derivativePlaneHk_apply]
    rw [prefix_single_jet_eq_cons]
    exact planeHk_jet_cons_eq_snoc (by omega) p w k
  have ht := planeFamilyTensor_jet_ae (fun k : Fin 2 =>
    derivativePlaneHk (fun _ : Fin 1 => k) p) ⟨j, w⟩
  simpa only [planeGradientTensor, hi] using ht

end AVRegularity.Weighted
end
