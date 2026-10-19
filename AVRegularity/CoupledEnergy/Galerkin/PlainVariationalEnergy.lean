-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergy.Galerkin.PlainSynthesis
import AVRegularity.CoupledEnergy.Variational.DriftCarrierBudget
public import AVRegularity.Statements.Intermediate.CoupledEnergy.AdmissibleOrders

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Contract the explicit Fourier rows with arbitrary plain finite test coefficients. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

/-- A finite coefficient test is exactly its synthesized spatial test field. -/
theorem plainTestJet_inner_sum (N : ℕ) (z : CoupledPlainCoefficients (h := h) N)
    (m : ℕ) (w : DerivativeWord2 m) (U : ∀ i, h i) (x : Vec 2) :
    (∑ r, z r * ∑ i, inner ℝ (U i) (coupledModeJet N r i m w x)) =
      ∑ i, inner ℝ (U i) (coupledPlainRawJet N z i m w x) := by
  simp only [coupledPlainRawJet, inner_sum, real_inner_smul_right]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Direction-indexed flux rows contract to the actual gradient of the finite test. -/
theorem plainTestGradient_inner_sum (N : ℕ) (z : CoupledPlainCoefficients (h := h) N)
    (U : ∀ i, Fin 2 → h i) (x : Vec 2) :
    (∑ r, z r * ∑ i, ∑ k : Fin 2, inner ℝ (U i k) (coupledModeJet N r i 1 (fun _ => k) x)) =
      ∑ i, ∑ k : Fin 2, inner ℝ (U i k) (coupledPlainRawJet N z i 1 (fun _ => k) x) := by
  simp only [coupledPlainRawJet, inner_sum, real_inner_smul_right]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
end

/-! Classical vector calculus for the all-order finite Fourier lift. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The all-order finite Fourier lift is spatially smooth as a vector-valued field. -/
theorem smoothFourierJet_contDiff {K L : ℕ} (N : ℕ) (f : TorusHk K E)
    (a : JetIndex2 L) : ContDiff ℝ (↑(⊤ : ℕ∞)) (smoothFourierJet N f a) := by
  apply ContDiff.sum
  intro k _
  exact (smoothFourierCoordinate_contDiff N f a.1 a.2
    ((stdOrthonormalBasis ℝ E) k)).smul contDiff_const

/-- The vector derivative agrees with the already proved scalar weak-word derivative. -/
theorem smoothFourierJet_fderiv {K L : ℕ} (N : ℕ) (f : TorusHk K E)
    (j : Fin L) (w : DerivativeWord2 j.val) (k : Fin 2) (x : Vec 2) :
    fderiv ℝ (smoothFourierJet N f (lowerIndex2 j w)) x (basisVec k) =
      smoothFourierJet N f (nextIndex2 j w k) x := by
  apply ext_inner_left ℝ
  intro e
  let T := InnerProductSpace.toDual ℝ E e
  have hd := T.hasFDerivAt.comp x
    ((smoothFourierJet_contDiff N f (lowerIndex2 j w)).differentiable (by simp) x).hasFDerivAt
  have hscalar := smoothFourierJet_inner_derivative N f j w e k x
  change (fderiv ℝ (fun y => inner ℝ e (smoothFourierJet N f (lowerIndex2 j w) y)) x)
    (basisVec k) = _ at hscalar
  change (fderiv ℝ (T ∘ smoothFourierJet N f (lowerIndex2 j w)) x) (basisVec k) = _ at hscalar
  rw [hd.fderiv] at hscalar
  exact hscalar

/-- Testing a projected weak jet against a fixed finite Fourier test preserves the pairing. -/
theorem galerkinProj_jet_pairing_of_fixed {K : ℕ} (N : ℕ) (f : TorusHk K E)
    (a : JetIndex2 K) (z : ComponentL2 (volume.restrict AVenhance.unitCube) E)
    (hz : cellVectorFourierProjection N z = z) :
    inner ℝ ((galerkinProj N f).val a) z = inner ℝ (f.val a) z := by
  change inner ℝ (cellVectorFourierProjection N (f.val a)) z = _
  rw [cellVectorFourierProjection_inner, hz]

/-- Every jet of a synthesized finite carrier is a fixed Fourier test. -/
theorem galerkinProj_jet_fixed {K : ℕ} (N : ℕ) (f : TorusHk K E)
    (hf : galerkinProj N f = f) (a : JetIndex2 K) :
    cellVectorFourierProjection N (f.val a) = f.val a :=
  congrArg (fun z : TorusHk K E => z.val a) hf

/-- The graph projection has the all-order smooth Fourier representative at each retained jet. -/
theorem galerkinProj_jet_ae_smooth {K : ℕ} (N : ℕ) (f : TorusHk K E) (a : JetIndex2 K) :
    (galerkinProj N f).val a =ᵐ[volume.restrict AVenhance.unitCube]
      smoothFourierJet (L := K) N f a := by
  have heq : smoothFourierLift (L := K) N f = galerkinProj N f := by
    apply TorusHk.ext_value
    exact smoothFourierLift_value_eq_projection (le_refl K) N f
  rw [← heq]
  exact torusJetToL2_ae _ _ a
end

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Actual Fourier projection errors vanish in time L² in the Sobolev graph. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem galerkinProj_time_tail_square_tendsto (K : ℕ) (a b : ℝ)
    (u : ℝ → TorusHk K E) (hu : MemLp u 2 (volume.restrict (Set.Icc a b))) :
    Tendsto (fun N => ∫ t in Set.Icc a b, ‖galerkinProj N (u t) - u t‖ ^ 2) atTop (𝓝 0) :=
  Variational.contractingProjection_integral_tail_square_tendsto _
    (fun N => galerkinProj N) galerkinProj_norm_le galerkinProj_tendsto u hu

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Move the actual Fourier cutoff between value tests of possibly different
Sobolev orders, using the orthogonal cell projection. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem torusHkValue_galerkinProj (K N : ℕ) (u : TorusHk K E) :
    torusHkValueCLM (galerkinProj N u) = cellVectorFourierProjection N (torusHkValueCLM u) := rfl

theorem galerkinProj_value_inner_move (K L N : ℕ) (u : TorusHk K E) (φ : TorusHk L E) :
    inner ℝ (torusHkValueCLM (galerkinProj N u)) (torusHkValueCLM φ) =
      inner ℝ (torusHkValueCLM u) (torusHkValueCLM (galerkinProj N φ)) := by
  rw [torusHkValue_galerkinProj, torusHkValue_galerkinProj]
  exact cellVectorFourierProjection_inner N _ _

/-- A trial already in the cutoff range may be paired with the original H¹ test. -/
theorem galerkinProj_fixed_value_pairing (K L N : ℕ) (u : TorusHk K E) (φ : TorusHk L E)
    (hu : galerkinProj N u = u) :
    inner ℝ (torusHkValueCLM u) (torusHkValueCLM (galerkinProj N φ)) =
      inner ℝ (torusHkValueCLM u) (torusHkValueCLM φ) := by
  rw [← galerkinProj_value_inner_move K L N u φ, hu]
end

/-! Explicit scalar Fourier integrals for the coupled Galerkin matrix. Rows are test modes,
columns are trial modes. The value basis is orthonormal, so the coefficient mass matrix is
identity once the Fourier mode orthogonality bridge is proved. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Full ordered derivative array of a trial Fourier mode. -/
def coupledModeTensor (N : ℕ) (c : CoupledFourierModeIndex (h := h) N)
    (i : ι) (m : ℕ) (x : Vec 2) : PiLp 2 (fun _ : DerivativeWord2 m => h i) :=
  WithLp.toLp 2 fun w => coupledModeJet N c i m w x

omit [Fintype ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem coupledModeTensor_continuous (N : ℕ)
    (c : CoupledFourierModeIndex (h := h) N) (i : ι) (m : ℕ) :
    Continuous (coupledModeTensor N c i m) :=
  (PiLp.continuous_toLp 2 (fun _ : DerivativeWord2 m => h i)).comp
    (continuous_pi fun w => (coupledModeJet_contDiff N c i m w).continuous)

/-- Spatial integrand for the projected diffusion entry. -/
def plainDiffusionIntegrand (N : ℕ) (ν : ℝ)
    (r c : CoupledFourierModeIndex (h := h) N) (x : Vec 2) : ℝ :=
  -ν * ∑ i, ∑ k : Fin 2,
    inner ℝ (coupledModeJet N c i 1 (fun _ => k) x)
      (coupledModeJet N r i 1 (fun _ => k) x)

/-- Spatial integrand for the projected drift entry. -/
def plainDriftIntegrand (N : ℕ) (v : Vec 2 → Vec 2)
    (r c : CoupledFourierModeIndex (h := h) N) (x : Vec 2) : ℝ :=
  -∑ i, ∑ k : Fin 2, v x k *
    inner ℝ (coupledModeJet N c i 1 (fun _ => k) x)
      (coupledModeJet N r i 0 Fin.elim0 x)

/-- Spatial integrand for every admissible higher-order coupling entry. -/
def plainCouplingIntegrand (N D : ℕ) (K : ι → ℕ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (r c : CoupledFourierModeIndex (h := h) N) (x : Vec 2) : ℝ :=
  -∑ i, ∑ i', ∑ d : admissibleOrders K D i i', ∑ k : Fin 2,
    inner ℝ (A i i' d x (coupledModeTensor N c i' (d.1 - 1) x) k)
      (coupledModeJet N r i 1 (fun _ => k) x)

/-- The literal Fourier coefficient matrix for diffusion, drift and coupling. -/
def plainFourierMatrix (N D : ℕ) (ν : ℝ) (K : ι → ℕ)
    (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (t : ℝ) (r c : CoupledFourierModeIndex (h := h) N) : ℝ :=
  ∫ x in AVenhance.unitCube,
    plainDiffusionIntegrand N ν r c x + plainDriftIntegrand N (v t) r c x +
      plainCouplingIntegrand N D K (fun i i' d => A i i' d t) r c x

/-- Scalar Fourier pairing of the literal flux and value forcing. -/
def plainFourierForcing (N : ℕ)
    (F : ∀ i, Vec 2 → PiLp 2 (fun _ : Fin 2 => h i))
    (g : ∀ i, Vec 2 → h i)
    (r : CoupledFourierModeIndex (h := h) N) : ℝ :=
  ∫ x in AVenhance.unitCube, ∑ i,
    (inner ℝ (g i x) (coupledModeJet N r i 0 Fin.elim0 x) -
      ∑ k : Fin 2, inner ℝ (F i x k) (coupledModeJet N r i 1 (fun _ => k) x))
end

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set AVenhance.Infra.ODE
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Factorial variational energy identities for synthesized plain coefficient ODEs.
Reconstruction is a fixed
linear observable and its norm-square derivative is twice the Hilbert pairing.
Here each ordered jet is treated separately, allowing measurable coefficients
and L¹ value forcing while retaining the factorial norm exactly. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The single Hilbert observable for an ordered jet of the synthesized field. -/
def plainJetSynthesisCLM (N : ℕ) (i : ι) (K : ℕ) (j : JetIndex2 K) :
    CoupledPlainCoefficients (h := h) N →L[ℝ]
      ComponentL2 (volume.restrict AVenhance.unitCube) (h i) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : JetIndex2 K =>
    ComponentL2 (volume.restrict AVenhance.unitCube) (h i)) j).comp
      ((torusHkGraph (E := h i) K).toSubmodule.subtypeL.comp (coupledPlainSynthesis N i K))

@[simp] theorem plainJetSynthesisCLM_apply (N : ℕ) (i : ι) (K : ℕ) (j : JetIndex2 K)
    (c : CoupledPlainCoefficients (h := h) N) :
    plainJetSynthesisCLM N i K j c = (coupledPlainSynthesis N i K c).val j := rfl

end AVRegularity.CoupledEnergy.Galerkin
end
