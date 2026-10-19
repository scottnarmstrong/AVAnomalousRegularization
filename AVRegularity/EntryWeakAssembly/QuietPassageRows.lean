-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryWeakAssembly.QuietWordIntegral
public import AVRegularity.EntryWeakAssembly.QuietDuhamel
import AVRegularity.Proofs.WeakGen.Comparison.RowCoefficients
import AVRegularity.Proofs.WeakGen.Reduction.ScalarIdentification
import AVRegularity.CycleComparison.Reconstruction.Continuity
public import AVRegularity.EntryWeakAssembly.Assembly.WeakComparisonDescending
import AVRegularity.CycleComparison.Error.WeakSolution

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.CycleComparison.Coarse
namespace AVRegularity.WeakEntryProofs

/-! Native primal-adjoint source pairing, extended from smooth periodic tests
by strong Fourier graph approximation. -/

private theorem weakQuiet_value_test_projection {K : ℕ} (f : TorusHk K ℝ)
    (φ : TorusHk 1 ℝ) (N : ℕ) :
    inner ℝ (torusHkValueCLM f) (torusHkValueCLM (galerkinProj N φ)) =
      cellInner (tval f) (smoothFourierJet (L := 1) N φ (valueIndex2 1)) := by
  rw [L2.inner_def]
  unfold cellInner
  apply integral_congr_ae
  filter_upwards [tval_ae f, galerkinProj_jet_ae_smooth N φ (valueIndex2 1)] with y hf hφ
  rw [hf]
  exact congrArg (fun z => inner ℝ (f.val (valueIndex2 K) y) z) hφ

private theorem weakQuiet_projection_gradient (φ : TorusHk 1 ℝ) (N : ℕ) :
    torusH1GradientL2CLM (E := ℝ) (galerkinProj N φ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => WithLp.toLp 2 (fun k : Fin 2 =>
        partialOp k (smoothFourierJet (L := 1) N φ (valueIndex2 1)) y) := by
  have hj := ae_all_iff.mpr fun k : Fin 2 => galerkinProj_jet_ae_smooth N φ
    (nextIndex2 (⟨0, Nat.one_pos⟩ : Fin 1) Fin.elim0 k)

  filter_upwards [torusH1GradientL2CLM_ae (galerkinProj N φ), hj] with y hy hjy
  apply PiLp.ext
  intro k
  rw [hy]
  change (galerkinProj N φ).val (⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ : JetIndex2 1) y = _
  have hi : (⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ : JetIndex2 1) =
      nextIndex2 (⟨0, Nat.one_pos⟩ : Fin 1) Fin.elim0 k := by
    apply Sigma.ext rfl
    apply heq_of_eq
    funext j
    fin_cases j
    rfl
  rw [hi, hjy k]
  exact (smoothFourierJet_fderiv N φ (⟨0, Nat.one_pos⟩ : Fin 1) Fin.elim0 k y).symm

/-- Genuine periodic H1-H1 integration by parts for the native divergence. -/
theorem weak_quiet_native_divergence_pair {K : ℕ}
    (F : TorusHk (K + 1) (PiLp 2 (fun _ : Fin 2 => ℝ))) (φ : TorusHk 1 ℝ) :
    inner ℝ (torusHkValueCLM (weakQuietNativeDivergence K F)) (torusHkValueCLM φ) =
      -inner ℝ (torusHkValueCLM F) (torusH1GradientL2CLM (E := ℝ) φ) := by
  have hN (N : ℕ) :
      inner ℝ (torusHkValueCLM (weakQuietNativeDivergence K F))
        (torusHkValueCLM (galerkinProj N φ)) =
      -inner ℝ (torusHkValueCLM F) (torusH1GradientL2CLM (E := ℝ) (galerkinProj N φ)) := by
    rw [weakQuiet_value_test_projection, ← weak_quiet_native_gradient_adjoint_apply]
    rw [(weakQuietNativeGradientAdj (F := ℝ) K (K + 1)).ident K le_rfl F _
      ((smoothFourierJet_contDiff N φ _).of_le (by simp))
      (smoothFourierJet_periodic N φ _)]
    rw [L2.inner_def, ← integral_neg]
    unfold cellInner
    apply integral_congr_ae
    filter_upwards [tval_ae F, weakQuiet_projection_gradient φ N] with y hF hφ
    rw [hF, hφ]
    rw [inner_sum]
    calc
      _ = -(∑ k : Fin 2, inner ℝ ((F.val (valueIndex2 (K + 1))) y k)
          (partialOp k (smoothFourierJet (L := 1) N φ (valueIndex2 1)) y)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [real_inner_comm (piSingleCLM ℝ k _) _, inner_piSingleCLM,
          inner_neg_left, real_inner_comm]
      _ = _ := by rw [PiLp.inner_apply]; rfl
  have hl : Continuous (fun z : TorusHk 1 ℝ =>
      inner ℝ (torusHkValueCLM (weakQuietNativeDivergence K F)) (torusHkValueCLM z)) :=
    continuous_const.inner torusHkValueCLM.continuous
  have hr : Continuous (fun z : TorusHk 1 ℝ =>
      -inner ℝ (torusHkValueCLM F) (torusH1GradientL2CLM (E := ℝ) z)) :=
    (continuous_const.inner torusH1GradientL2CLM.continuous).neg
  exact tendsto_nhds_unique
    (hl.continuousAt.tendsto.comp (galerkinProj_tendsto φ))
    ((hr.continuousAt.tendsto.comp (galerkinProj_tendsto φ)).congr (fun N => (hN N).symm))

/-- Lowering the flux reserve leaves its literal value unchanged. -/
theorem weak_quiet_native_flux_value {K J r : ℕ} (hKJ : K ≤ J) {ε a b : ℝ} (hε : 0 < ε)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => ℝ) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => ℝ))
    (hA : coefficientSeminorm ε J a b A ≠ ⊤) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ContDiff ℝ (K : ℕ) (A t)) (hp : AVenhance.IsZ2Periodic (A t))
    (u : TorusHk (K + r) ℝ) :
    truncateTorusHk (Nat.zero_le K) (weakQuietNativeFlux hKJ hε A hA t ht hC hp u) =
      weakQuietNativeFlux (Nat.zero_le J) hε A hA t ht (hC.of_le (by simp)) hp
        (truncateTorusHk (Nat.add_le_add_right (Nat.zero_le K) r) u) := by
  let ulo := truncateTorusHk (Nat.add_le_add_right (Nat.zero_le K) r) u
  let BK := fun l : Fin (K + 1) => (coefficientOrderSup a b A l.val).toReal
  let B0 := fun l : Fin (0 + 1) => (coefficientOrderSup a b A l.val).toReal
  have hbK (l : Fin (K + 1)) (y : Vec 2) : ‖coefficientDerivativeArray (A t) l.val y‖ ≤ BK l :=
    coefficientOrderSup_derivative_bound ε hε K a b A
      (ne_top_of_le_ne_top hA (Construction.Preservation.FullLift.coefficientSeminorm_order_mono
        ε hKJ a b A)) l.val (Nat.le_of_lt_succ l.isLt) t ht y
  have hb0 (l : Fin (0 + 1)) (y : Vec 2) : ‖coefficientDerivativeArray (A t) l.val y‖ ≤ B0 l :=
    coefficientOrderSup_derivative_bound ε hε 0 a b A
      (ne_top_of_le_ne_top hA (Construction.Preservation.FullLift.coefficientSeminorm_order_mono
        ε (Nat.zero_le J) a b A)) l.val (Nat.le_of_lt_succ l.isLt) t ht y
  rw [weak_quiet_native_flux_apply, weak_quiet_native_flux_apply]
  unfold weakQuietSourceFlux torusMultiplyIntervalCoefficient
  apply TorusHk.ext_value
  apply Lp.ext
  filter_upwards [torusMulCoefficient_value_ae (torusDerivativeTensor u) (A t) hC hp hbK,
    torusMulCoefficient_value_ae (torusDerivativeTensor (K := 0) (r := r) ulo)
      (A t) (hC.of_le (by simp)) hp hb0,
    torusDerivativeTensor_value_ae u, torusDerivativeTensor_value_ae (K := 0) (r := r) ulo]
    with y hhigh hlow hten htenlo
  change ((torusDerivativeTensor u).mulCoefficient (A t) hC hp hbK).val (valueIndex2 K) y =
    ((torusDerivativeTensor (K := 0) (r := r) ulo).mulCoefficient
      (A t) (hC.of_le (by simp)) hp hb0).val (valueIndex2 0) y
  rw [hhigh, hlow, hten, htenlo]
  rfl

/-- Both signed realizations are the same actual divergence source, at
arbitrary positive and negative reserves. -/
theorem weak_quiet_native_source_pair {P Q J r R Kc : ℕ} {ε a b C : ℝ}
    (hPJ : P + 1 ≤ J) (hε : 0 < ε)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => ℝ) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => ℝ))
    (hA : coefficientSeminorm ε J a b A ≠ ⊤) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (hC : ContDiff ℝ (P + 1 : ℕ) (A t)) (hp : AVenhance.IsZ2Periodic (A t))
    (Adj : TorusAdj (weakQuietPrimalSource r (A t)) (r + 1) R Kc C)
    (hQ : Q + (r + 1) ≤ Kc) (u : TorusHk ((P + 1) + r) ℝ)
    (φ : TorusHk (Q + (r + 1)) ℝ) :
    inner ℝ (truncateTorusHk (Nat.zero_le P)
      (weakQuietNativeSource hPJ hε A hA t ht hC hp u))
      (truncateTorusHk (Nat.zero_le (Q + (r + 1))) φ) =
    inner ℝ (truncateTorusHk (Nat.zero_le ((P + 1) + r)) u)
      (truncateTorusHk (Nat.zero_le Q) (Adj.adj Q hQ φ)) := by
  have hcp : ContDiff ℝ (1 : ℕ) (A t) := hC.of_le (by exact_mod_cast Nat.le_add_left 1 P)
  have hh := weak_quiet_native_divergence_pair
    (weakQuietNativeFlux hPJ hε A hA t ht hC hp u)
    (truncateTorusHk (by omega : 1 ≤ Q + (r + 1)) φ)
  have ha := weak_quiet_source_native_pair hε A hA t ht hcp hp Adj hQ
    (truncateTorusHk (Nat.add_le_add_right (Nat.zero_le (P + 1)) r) u) φ
  rw [← weak_quiet_native_flux_apply] at ha
  have hv := weak_quiet_native_flux_value hPJ hε A hA t ht hC hp u
  have hve := congrArg (fun z => torusHkValueCLM z) hv
  rw [← hve, weak_scalar_zero_inner] at ha
  rw [weak_scalar_zero_inner, weak_scalar_zero_inner]
  dsimp only [weakQuietNativeSource, ContinuousLinearMap.comp_apply]
  exact hh.trans ha.symm

/-- Fixed positive fluxes are strongly measurable using only measurable
coefficient values, through the native multiplier theorem. -/
theorem weak_quiet_native_flux_measurable {K J r : ℕ} (hKJ : K ≤ J) {ε a b : ℝ} (hε : 0 < ε)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => ℝ) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => ℝ))
    (hA : coefficientSeminorm ε J a b A ≠ ⊤)
    (hm : Measurable (fun z : Set.Icc a b × Vec 2 => A z.1 z.2))
    (hC : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (A t))
    (hp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (A t)) (u : TorusHk (K + r) ℝ) :
    StronglyMeasurable (fun t : Set.Icc a b =>
      weakQuietNativeFlux hKJ hε A hA t t.2 (hC t t.2) (hp t t.2) u) := by
  let BK := fun l : Fin (K + 1) => (coefficientOrderSup a b A l.val).toReal
  have hb (t : Set.Icc a b) (l : Fin (K + 1)) (y : Vec 2) :
      ‖coefficientDerivativeArray (A t) l.val y‖ ≤ BK l :=
    coefficientOrderSup_derivative_bound ε hε K a b A
      (ne_top_of_le_ne_top hA (Construction.Preservation.FullLift.coefficientSeminorm_order_mono
        ε hKJ a b A)) l.val (Nat.le_of_lt_succ l.isLt) t t.2 y
  have h := KernelEnergy.torusMultiplier_fixed_stronglyMeasurable
    (fun t : Set.Icc a b => A t) hm (fun t => hC t t.2) (fun t => hp t t.2) BK hb
    (torusDerivativeTensor u)
  have he : (fun t : Set.Icc a b =>
      weakQuietNativeFlux hKJ hε A hA t t.2 (hC t t.2) (hp t t.2) u) =
      (fun t : Set.Icc a b => (torusDerivativeTensor u).mulCoefficient
        (A t) (hC t t.2) (hp t t.2) (hb t)) := by
    funext t
    rw [weak_quiet_native_flux_apply]
    rfl
  rwa [he]

/-- The divergence of a fixed positive source flux is strongly measurable. -/
theorem weak_quiet_native_source_measurable {K J r : ℕ} (hKJ : K + 1 ≤ J)
    {ε a b : ℝ} (hε : 0 < ε)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => ℝ) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => ℝ))
    (hA : coefficientSeminorm ε J a b A ≠ ⊤)
    (hm : Measurable (fun z : Set.Icc a b × Vec 2 => A z.1 z.2))
    (hC : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K + 1 : ℕ) (A t))
    (hp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (A t))
    (u : TorusHk ((K + 1) + r) ℝ) :
    StronglyMeasurable (fun t : Set.Icc a b =>
      weakQuietNativeSource hKJ hε A hA t t.2 (hC t t.2) (hp t t.2) u) :=
  (weakQuietNativeDivergence (F := ℝ) K).continuous.comp_stronglyMeasurable
    (weak_quiet_native_flux_measurable hKJ hε A hA hm hC hp u)

/-- Native adjoint values are strongly measurable without any measurability
assumption on coefficient derivatives. Positive-source pairing supplies the
countable Hilbert readouts, and the Sobolev value embedding recovers the graph. -/
theorem weak_quiet_native_adjoint_measurable {Q J r R Kc : ℕ} {ε a b : ℝ}
    (hJ : 1 ≤ J) (hε : 0 < ε)
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => ℝ) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => ℝ))
    (hA : coefficientSeminorm ε J a b A ≠ ⊤)
    (hm : Measurable (fun z : Set.Icc a b × Vec 2 => A z.1 z.2))
    (hC : ∀ t ∈ Set.Icc a b, ContDiff ℝ (1 : ℕ) (A t))
    (hp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (A t))
    (C : Set.Icc a b → ℝ)
    (Adj : ∀ t : Set.Icc a b, TorusAdj (weakQuietPrimalSource r (A t)) (r + 1) R Kc (C t))
    (hQ : Q + (r + 1) ≤ Kc) (φ : TorusHk (Q + (r + 1)) ℝ) :
    StronglyMeasurable (fun t : Set.Icc a b => (Adj t).adj Q hQ φ) := by
  let O (t : Set.Icc a b) : TorusHk (1 + r) ℝ →L[ℝ] TorusHk 0 ℝ :=
    weakQuietNativeSource (K := 0) hJ hε A hA t t.2 (hC t t.2) (hp t t.2)
  apply Assembly.weak_quiet_positive_representatives_measurable Q (1 + r)
    (fun t : Set.Icc a b => (Adj t).adj Q hQ φ)
    (truncateTorusHk (Nat.zero_le _) φ) O
  · intro χ
    exact weak_quiet_native_source_measurable (K := 0) hJ hε A hA hm hC hp χ
  · intro t χ
    have he := weak_quiet_native_source_pair (P := 0) hJ hε A hA t t.2
      (hC t t.2) (hp t t.2) (Adj t) hQ χ φ
    calc
      _ = inner ℝ (truncateTorusHk (Nat.zero_le (1 + r)) χ)
          (truncateTorusHk (Nat.zero_le Q) ((Adj t).adj Q hQ φ)) := real_inner_comm _ _
      _ = _ := he.symm
      _ = _ := real_inner_comm _ _

end AVRegularity.WeakEntryProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleComparison.Coarse
namespace AVRegularity.WeakEntryProofs

/-! One actual coefficient produces both signed native source maps at the
common weak order. Its hypotheses are the parent coefficient budget and
regularity; all operator estimates and pairings are proved here. -/

/-- The source premises for one actual coefficient on one closed quiet margin. -/
structure WeakQuietSourceContext where
  ν : ℝ
  ε : ℝ
  c : ℝ
  a : ℝ
  b : ℝ
  β : ℝ
  r : ℕ
  m : ℕ
  cap : ℕ
  J : ℕ
  ν_pos : 0 < ν
  ε_pos : 0 < ε
  c_pos : 0 < c
  c_small : 2 * c ≤ 1
  β_nonneg : 0 ≤ β
  r_pos : 1 ≤ r
  order_le : r + 1 ≤ m
  cap_ge : m ≤ cap
  jets : cap ≤ J
  coeff : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => ℝ) →L[ℝ]
    PiLp 2 (fun _ : Fin 2 => ℝ)
  finite : coefficientSeminorm ε J a b coeff ≠ ⊤
  budget : (coefficientSeminorm ε J a b coeff).toReal ≤ ν * ε ^ (r - 1) * β
  measurable : Measurable (fun z : Set.Icc a b × Vec 2 => coeff z.1 z.2)
  smooth : ∀ t ∈ Set.Icc a b, ContDiff ℝ (J : ℕ) (coeff t)
  periodic : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (coeff t)

namespace WeakQuietSourceContext

def price (p : WeakQuietSourceContext) : ℝ := (2 * (p.cap + 1 : ℕ) / p.c) ^ p.m

def rate (p : WeakQuietSourceContext) : ℝ := p.ν / p.ε ^ 2 * p.price * p.β

theorem rate_nonneg (p : WeakQuietSourceContext) : 0 ≤ p.rate := by
  unfold rate price
  have hν := p.ν_pos
  have hε := p.ε_pos
  have hc := p.c_pos
  have hβ := p.β_nonneg
  positivity

end WeakQuietSourceContext

/-- Native signed maps of this same actual source. No analytic bound is
assumed: this is the output data constructed below. -/
structure WeakQuietSingleSourceData (p : WeakQuietSourceContext) where
  C : Set.Icc p.a p.b → ℝ
  adj : ∀ t : Set.Icc p.a p.b,
    TorusAdj (weakQuietPrimalSource p.r (p.coeff t)) p.m (p.cap - p.m) p.cap (C t)
  adj_bound : ∀ t, (adj t).FBound (p.c * p.ε) p.rate
  primal : ∀ P : ℕ, P + p.m ≤ p.cap → Set.Icc p.a p.b →
    TorusHk (P + p.m) ℝ →L[ℝ] TorusHk P ℝ
  primal_bound : ∀ P hP t f,
    Real.sqrt (factorialNormSq (p.c * p.ε) (primal P hP t f).val) ≤
      p.rate * Real.sqrt (factorialNormSq (p.c * p.ε) f.val)
  paired : ∀ P Q hP hQ t (f : TorusHk (P + p.m) ℝ) (φ : TorusHk (Q + p.m) ℝ),
    inner ℝ (truncateTorusHk (Nat.zero_le P) (primal P hP t f))
      (truncateTorusHk (Nat.zero_le (Q + p.m)) φ) =
    inner ℝ (truncateTorusHk (Nat.zero_le (P + p.m)) f)
      (truncateTorusHk (Nat.zero_le Q) ((adj t).adj Q hQ φ))
  measurable : ∀ Q hQ (φ : TorusHk (Q + p.m) ℝ),
    StronglyMeasurable (fun t : Set.Icc p.a p.b => (adj t).adj Q hQ φ)

/-- A parent-budgeted coefficient produces the full signed source data. -/
theorem weak_quiet_single_source (p : WeakQuietSourceContext) :
    Nonempty (WeakQuietSingleSourceData p) := by
  have hc1 : p.c ≤ 1 := by have h := p.c_small; linarith only [h, p.c_pos]
  have hRJ : p.cap - p.m + 1 ≤ p.J := by
    have := p.order_le; have := p.jets; have := p.cap_ge; omega
  have hJ : 1 ≤ p.J := by have := p.order_le; have := p.jets; have := p.cap_ge; omega
  have hex (t : Set.Icc p.a p.b) : ∃ C : ℝ,
      ∃ Adj : TorusAdj (weakQuietPrimalSource p.r (p.coeff t)) (p.r + 1)
        (p.cap - p.m) p.cap C, Adj.FBound (p.c * p.ε) p.rate := by
    obtain ⟨C, Adj, hAdj⟩ := weak_quiet_source_adjoint_normalized p.ε_pos p.c_pos p.c_small
      p.r (p.cap - p.m) p.cap p.J p.r_pos hRJ p.jets p.coeff p.smooth p.periodic
      p.finite p.budget t t.2
    refine ⟨C, Adj, hAdj.mono_const ?_⟩
    have hh := weak_quiet_adjoint_order_price p.c_pos hc1 p.cap (p.r + 1) p.m p.order_le
    calc
      _ = (p.ν / p.ε ^ 2 *
          (2 ^ (p.r + 1) * ((p.cap : ℝ) / p.c) ^ (p.r + 1))) * p.β := by ring
      _ ≤ p.rate := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hh (by have := p.ν_pos; positivity)) p.β_nonneg
  let C := fun t : Set.Icc p.a p.b => (hex t).choose
  let Adj := fun t : Set.Icc p.a p.b => (hex t).choose_spec.choose
  have hAdj (t) : (Adj t).FBound (p.c * p.ε) p.rate := (hex t).choose_spec.choose_spec
  let Pmap (P : ℕ) (hP : P + p.m ≤ p.cap) (t : Set.Icc p.a p.b) :
      TorusHk (P + p.m) ℝ →L[ℝ] TorusHk P ℝ :=
    (weakQuietNativeSource (show P + 1 ≤ p.J by have := p.order_le; have := p.jets; omega)
      p.ε_pos p.coeff p.finite t t.2
      ((p.smooth t t.2).of_le (by exact_mod_cast
        (show P + 1 ≤ p.J by have := p.order_le; have := p.jets; omega)))
      (p.periodic t t.2)).comp
        (truncateTorusHk (by have := p.order_le; omega : (P + 1) + p.r ≤ P + p.m))
  refine ⟨⟨C, fun t => (Adj t).liftOrder p.order_le,
    fun t => (hAdj t).liftOrder p.rate_nonneg p.order_le, Pmap, ?_, ?_, ?_⟩⟩
  · intro P hP t f
    have hj : P + 1 ≤ p.J := by have := p.order_le; have := p.jets; omega
    have hcap : P + 1 + p.r ≤ p.cap := by have := p.order_le; omega
    have hh := weak_quiet_native_source_normalized hj hcap p.r_pos p.order_le
      p.ν_pos p.ε_pos p.c_pos hc1 p.β_nonneg p.coeff p.finite p.budget t t.2
      ((p.smooth t t.2).of_le (by exact_mod_cast hj)) (p.periodic t t.2)
      (truncateTorusHk (by have := p.order_le; omega : (P + 1) + p.r ≤ P + p.m) f)
    exact hh.trans (mul_le_mul_of_nonneg_left
      (sqrt_fNSq_torus_truncate_le (p.c * p.ε) _ f) p.rate_nonneg)
  · intro P Q hP hQ t f φ
    have hj : P + 1 ≤ p.J := by have := p.order_le; have := p.jets; omega
    have hq : Q + (p.r + 1) ≤ p.cap := by have := p.order_le; omega
    exact weak_quiet_native_source_pair hj p.ε_pos p.coeff p.finite t t.2
      ((p.smooth t t.2).of_le (by exact_mod_cast hj)) (p.periodic t t.2) (Adj t) hq
      (truncateTorusHk (by have := p.order_le; omega : (P + 1) + p.r ≤ P + p.m) f)
      (truncateTorusHk (Nat.add_le_add_left p.order_le Q) φ)
  · intro Q hQ φ
    have hq : Q + (p.r + 1) ≤ p.cap := by have := p.order_le; omega
    exact weak_quiet_native_adjoint_measurable hJ p.ε_pos p.coeff p.finite p.measurable
      (fun t ht => (p.smooth t ht).of_le (by exact_mod_cast hJ)) p.periodic C Adj hq
      (truncateTorusHk (Nat.add_le_add_left p.order_le Q) φ)

end AVRegularity.WeakEntryProofs
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Providers.WeakGen.Comparison AVRegularity.CycleComparison.Coarse
namespace AVRegularity.WeakEntryProofs.Assembly

/-! The actual nonroot weak passage rows on their heat quiet margins. All source
carriers come from the given reduction, and the parent drift equality comes
from the middle half of the pinned renewal quiet margin. -/

private theorem weakQuiet_forcedRow_drift_congr {ν a b : ℝ} {D K : ℕ}
    {v v' : ℝ → Vec 2 → Vec 2} {f : TorusHk K ℝ}
    {F : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => ℝ))} {g u : ℝ → TorusHk K ℝ}
    {w : ℝ → TorusHk (K + 1) ℝ}
    (hs : IsTorusForcedRow ν a b v D K f F g u w)
    (hv : ∀ t ∈ Set.Icc a b, v t = v' t) :
    IsTorusForcedRow ν a b v' D K f F g u w := by
  refine isTorusForcedRow_of (hs.1 0) (hs.2.1 0) (hs.2.2.1 0) (hs.2.2.2.1 0) ?_
  intro t ht ψ
  refine CycleJointProofs.coupledWeakIdentity_integrands_congr
    (volume.restrict unitCube) ν a t v v' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl ?_ (hs.2.2.2.2 0 t ht ψ)
  intro s hs
  apply Filter.Eventually.of_forall
  intro x
  simp only [Weighted.weakIdentityRhs, hv s ⟨hs.1.le, hs.2.trans ht.2⟩,
    zero_apply, Finset.sum_const_zero]

private theorem weakQuiet_forcedRow_value_congr {ν a b : ℝ} {D K : ℕ}
    {v : ℝ → Vec 2 → Vec 2}
    {F : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => ℝ))} {g u u' : ℝ → TorusHk K ℝ}
    {w : ℝ → TorusHk (K + 1) ℝ} (hab : a ≤ b)
    (hs : IsTorusForcedRow ν a b v D K (u a) F g u w)
    (hu : ∀ t ∈ Set.Icc a b, u t = u' t) :
    IsTorusForcedRow ν a b v D K (u' a) F g u' w := by
  refine isTorusForcedRow_of ((hs.1 0).congr fun t ht => (hu t ht).symm)
    (hs.2.1 0) ?_ rfl ?_
  · filter_upwards [hs.2.2.1 0, ae_restrict_mem measurableSet_Icc] with t ht hmem
    exact ht.trans (hu t hmem)
  · intro t ht ψ
    have hh := hs.2.2.2.2 0 t ht ψ
    dsimp only at hh
    rw [hu t ht, hu a ⟨le_rfl, hab⟩] at hh
    simpa only [zero_apply, Finset.sum_const_zero] using hh

/-- The full heat quiet margin lies strictly after the original initial time.
The pinned renewal gap supplies half a positive slow quiet margin before its left end. -/
theorem WeakQuietExpansionCase.after_initial {plan : WeakPassagePlan}
    {prices : WeakQuietPathPrices} (x : WeakQuietExpansionCase plan prices) :
    x.run.a < x.left := by
  have hΛ : 1 ≤ x.c.D.Λ := by
    rw [x.c.base_eq]
    exact (by norm_num : 1 ≤ 128).trans ((plan.base_ge x.B).trans x.c.base_ge)
  have hτ := Velocity.Jets.ocTauP_pos (α := x.c.D.α) (q := x.c.D.q) (m := x.i) hΛ
  have hp := (x.run.reduction.2.2.2 x.i x.level_lt x.level_le).2.1
  have hmid := x.bounds.2.2.2.1
  change x.run.tq x.i - ocTauP x.c.D.α x.c.D.q x.c.D.Λ x.i / 2 ≤ x.left at hmid
  have ha := x.quiet.1
  linarith only [hτ, hp, hmid, ha]

/-- At the edgeless root, every supplied row is the scalar solution's value
on the entire root window. -/
theorem WeakQuietExpansionCase.root_value {plan : WeakPassagePlan}
    {prices : WeakQuietPathPrices} (x : WeakQuietExpansionCase plan prices)
    (htop : x.i = x.c.M + x.A.Jw) (v : x.Vertex) (t : ℝ)
    (ht : t ∈ Set.Icc (x.run.tq (x.i + 1)) (x.run.a + x.A.T₀)) :
    (x.run.Ur x.i v t).toFunction.jet (valueIndex2 x.R.Kw) =ᵐ[volume.restrict unitCube]
      x.run.θ t := by
  rcases x with ⟨B, A, R, c, run, i, hi, hit, quiet, b, bounds⟩
  change i = c.M + A.Jw at htop
  subst i
  rcases v with ⟨v, hv⟩
  change v ∈ (c.stage (c.M + A.Jw)).comps at hv
  have hvroot : v = (⟨0, []⟩ : Comp) :=
    Finset.mem_singleton.mp (c.construction.2.1.2.1 ▸ hv)
  subst v
  exact run.reduction.2.2.1 hv t ht

/-- The actual root row is a native scalar parent row on the heat quiet margin.
This reuses the scalar identification; the unconstrained root Uw
is never asserted to solve an equation. Its genuine gradient lift is returned. -/
theorem weak_quiet_root_native_row {plan : WeakPassagePlan}
    {prices : WeakQuietPathPrices} (x : WeakQuietExpansionCase plan prices)
    (htop : x.i = x.c.M + x.A.Jw) (v : x.Vertex) :
    ∃ w : ℝ → TorusHk 1 ℝ,
      WeakScalarTorusSolution (x.c.D.κ x.c.M) x.left x.right
        (streamVel (x.c.D.Φ (x.i - 1))) 0
        (truncateTorusHk (Nat.zero_le x.R.Kw) (x.run.Ur x.i v x.left))
        (fun t => truncateTorusHk (Nat.zero_le x.R.Kw) (x.run.Ur x.i v t)) w := by
  have hΛ : 128 ≤ x.A.Λ := (plan.base_ge x.B).trans x.c.base_ge
  have hscalar : IsWeakSolutionOn (streamVel (x.c.D.Φ (x.c.M + x.A.Jw)))
      (x.c.D.κ x.c.M) x.run.a (x.run.a + x.A.T₀) x.run.f x.run.θ := x.run.scalar
  obtain ⟨u, w, hs, hvalue⟩ :=
    Providers.WeakGen.Reduction.weak_scalar_torus_identification x.B.α x.B.s x.B.hα₀ x.B.hα₁
      x.B.hs₀ x.B.hs₁ x.B.q x.B.hq x.B.ζ x.B.hζ x.A.Λ hΛ x.c.D.Φ x.c.streams
      (x.c.M + x.A.Jw) (by have hh := x.A.Jw_pos; omega) (x.c.D.κ x.c.M) x.bounds.2.1
      x.run.a (x.run.a + x.A.T₀) x.run.f x.run.θ hscalar x.left x.after_initial
      (x.heat_window.1.le.trans x.quiet.2.1)
  have hv (t : ℝ) (ht : t ∈ Set.Icc x.left x.right) :
      u t = truncateTorusHk (Nat.zero_le x.R.Kw) (x.run.Ur x.i v t) := by
    apply TorusHk.ext_value
    apply Lp.ext
    have hu := hvalue t ⟨ht.1, ht.2.trans x.quiet.2.1⟩
    have hr := x.root_value htop v t (x.heat_window.2 ht)
    have hr' : CycleComparison.Coarse.tval
        (truncateTorusHk (Nat.zero_le x.R.Kw) (x.run.Ur x.i v t)) =ᵐ[volume.restrict unitCube]
        x.run.θ t := by
      rw [CycleComparison.Coarse.tval_truncateTorusHk]
      exact hr
    exact ((CycleComparison.Coarse.tval_ae (u t)).symm.trans hu).trans
      (hr'.symm.trans (CycleComparison.Coarse.tval_ae _))
  have hs' := CycleComparison.Error.isCoupledWeakSolutionTorus_restrict_left x.quiet.2.1 hs
  have hs'' := weakQuiet_forcedRow_value_congr x.heat_window.1.le hs' hv
  rw [← htop] at hs''
  exact ⟨w, weakQuiet_forcedRow_drift_congr hs'' x.heat_velocity_eq⟩

/-- Each genuine physical constituent has a native formal adjoint at the
fixed weak reserve. The ambient cap is used only to select an existing
coefficient; neither this reserve nor its weighted bound charges Dm. -/
theorem weak_quiet_constituent_adjoint {plan : WeakPassagePlan}
    {prices : WeakQuietPathPrices} (hdepth : WeakQuietMarginDepthOK plan prices)
    (x : WeakQuietExpansionCase plan prices)
    (hfloor : weakComparisonCoeffFloor x.R ≤ x.c.M)
    (hhalf : 2 * plan.radius x.R ≤ 1)
    (v u : x.Vertex) (γ : (x.c.stage x.i).fam.Γ v u)
    (d : ℕ) (hd : d ∈ Finset.Icc 2 x.order)
    (t : ℝ) (ht : t ∈ Set.Icc x.left x.right) :
    ∃ C : ℝ, ∃ Adj : TorusAdj
      (weakQuietPrimalSource (d - 1) ((x.c.stage x.i).physCoeff v u γ d t))
      (d - 1 + 1) (x.cap - x.order) x.cap C,
      Adj.FBound x.radius
        ((coefficientSeminorm (x.c.D.eps (x.i - 1)) (plan.jetOrder x.R)
          x.left x.right ((x.c.stage x.i).physCoeff v u γ d)).toReal *
          (2 ^ (d - 1 + 1) * ((x.cap : ℝ) / x.radius) ^ (d - 1 + 1))) := by
  have horder : 1 ≤ x.order := by unfold WeakQuietExpansionCase.order; omega
  have hdepth1 : 1 ≤ prices.depth x.R :=
    (Nat.succ_le_succ (Nat.zero_le _)).trans (hdepth x.R).1
  have hocap : x.order ≤ x.cap := by
    have hh := x.path_reserve (prices.depth x.R) le_rfl
    have hm : x.order ≤ prices.depth x.R * x.order := by
      simpa only [one_mul] using Nat.mul_le_mul_right x.order hdepth1
    exact hm.trans hh
  have hcapJ : x.cap ≤ plan.jetOrder x.R := (hdepth x.R).2
  have hdDm : d ≤ x.c.Dm := (Finset.mem_Icc.mp hd).2.trans x.c.order_ge
  have hε := x.bounds.1
  have hρε : 2 * x.radius ≤ x.c.D.eps (x.i - 1) := by
    exact (by simpa only [WeakQuietExpansionCase.radius, mul_assoc, one_mul] using
      mul_le_mul_of_nonneg_right hhalf hε.le)
  have hc := x.bounds.2.2.2.2.2.2.2.1 v u γ d (Finset.mem_Icc.mp hd).1 hdDm
  have hp := (weakPassage_physCoeff_regular x.c hfloor x.i x.level_lt x.level_le
    x.left x.right v u γ d (Finset.mem_Icc.mp hd).1).2.2.1
  exact weak_quiet_source_adjoint (mul_pos (plan.radius_pos x.R) hε) hρε
    (d - 1) (x.cap - x.order) x.cap (plan.jetOrder x.R)
    (by omega) hcapJ ((x.c.stage x.i).physCoeff v u γ d) hc (fun t _ => hp t)
    (x.coefficient_finite v u γ d (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, hdDm⟩))
    t ht

/-- The aggregate insertion pairs with the actual physical flux of separate
incoming carriers. The latter may differ in their high jets; their native
order-zero values must agree, as the width-zero equation certifies. -/
theorem weak_quiet_actual_incoming_pair {plan : WeakPassagePlan}
    {prices : WeakQuietPathPrices} (hdepth : WeakQuietMarginDepthOK plan prices)
    (x : WeakQuietExpansionCase plan prices)
    (hfloor : weakComparisonCoeffFloor x.R ≤ x.c.M)
    (hhalf : 2 * plan.radius x.R ≤ 1)
    (S : WeakQuietInsertionData x) (v u : x.Vertex)
    (t : ℝ) (ht : t ∈ Set.Icc x.left x.right)
    (Y : (x.c.stage x.i).fam.Γ v u → TorusHk (x.R.Kw + x.c.Dm - 1) ℝ)
    (u0 : TorusHk 0 ℝ)
    (hu : ∀ γ, truncateTorusHk (Nat.zero_le _) (Y γ) = u0) :
    ∃ F : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ℝ)),
      (F.toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube] fun y =>
        ∑ γ : (x.c.stage x.i).fam.Γ v u, ∑ d : ↥(Finset.Icc 2 x.c.Dm),
          (x.c.stage x.i).physCoeff v u γ d.1 t y
            (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
              (Y γ).toFunction.jet ⟨⟨d.1 - 1, by
                have hh := Finset.mem_Icc.mp d.2; omega⟩, word⟩ y)) ∧
      ∀ (hP : 0 + x.order ≤ x.cap) (φ : TorusHk (0 + x.order) ℝ),
        inner ℝ u0 (S.apply v u 0 hP t φ) =
          -Real.sqrt (x.mass u / x.mass v) *
            inner ℝ (CoupledEnergy.Galerkin.torusHkValueCLM F)
              (CoupledEnergy.Variational.torusH1GradientL2CLM (E := ℝ)
                (truncateTorusHk (by unfold WeakQuietExpansionCase.order; omega) φ)) := by
  classical
  let I := (x.c.stage x.i).fam.Γ v u × ↥(Finset.Icc 2 x.order)
  let r (p : I) := p.2.val - 1
  let A (p : I) : ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (r p) => ℝ) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => ℝ) := (x.c.stage x.i).physCoeff v u p.1 p.2.val
  have hDm (p : I) : p.2.val ≤ x.c.Dm :=
    (Finset.mem_Icc.mp p.2.property).2.trans x.c.order_ge
  have hfin (p : I) := x.coefficient_finite v u p.1 p.2.val
    (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp p.2.property).1, hDm p⟩)
  have hc (p : I) : ∀ t ∈ Set.Icc x.left x.right,
      ContDiff ℝ (plan.jetOrder x.R) (A p t) :=
    x.bounds.2.2.2.2.2.2.2.1 v u p.1 p.2.val
      (Finset.mem_Icc.mp p.2.property).1 (hDm p)
  have hp (p : I) := (weakPassage_physCoeff_regular x.c hfloor x.i x.level_lt
    x.level_le x.left x.right v u p.1 p.2.val (Finset.mem_Icc.mp p.2.property).1).2.2.1
  have hJ1 : 1 ≤ plan.jetOrder x.R := by
    have hh := (hdepth x.R).2
    have hh' := (hdepth x.R).1
    have hmul : 0 < prices.depth x.R * (1 + x.A.Jw * x.A.Nw) :=
      Nat.mul_pos (by omega) (by omega)
    omega
  let low (p : I) : 0 + r p ≤ x.R.Kw + x.c.Dm - 1 := by
    have hh := hDm p
    have hh' := (Finset.mem_Icc.mp p.2.property).1
    dsimp only [r]
    omega
  let U (p : I) := truncateTorusHk (low p) (Y p.1)
  let F : TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ℝ)) := ∑ p : I, weakQuietSourceFlux (Nat.zero_le (plan.jetOrder x.R))
    (x.c.D.eps (x.i - 1)) x.bounds.1 x.left x.right (A p) (hfin p) t ht
    ((hc p t ht).of_le (by simp)) (hp p t) (U p)
  refine ⟨F, ?_, ?_⟩
  · have hh : F.toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube]
        fun y => ∑ p : I, A p t y (WithLp.toLp 2 fun word : DerivativeWord2 (r p) =>
          (Y p.1).toFunction.jet ⟨⟨r p, by have := low p; omega⟩, word⟩ y) := by
      apply KernelEnergy.torusJet_sum_ae_of_eq
      intro p
      have hb := weak_quiet_source_flux_curve_value_ae
        (Nat.zero_le (plan.jetOrder x.R)) x.bounds.1 (A p) (hfin p)
        (fun t ht => (hc p t ht).of_le (by simp)) (fun t _ => hp p t)
        (fun _ => U p) t ht
      rw [weak_quiet_source_flux_curve_eq] at hb
      have hj : ∀ᵐ y ∂volume.restrict unitCube, ∀ word : DerivativeWord2 (r p),
          (U p).toFunction.jet ⟨⟨r p, by omega⟩, word⟩ y =
          (Y p.1).toFunction.jet ⟨⟨r p, by have := low p; omega⟩, word⟩ y :=
        ae_all_iff.mpr fun word => KernelEnergy.truncateTorusHk_toFunction_jet_ae
          (low p) (Y p.1) _
      filter_upwards [hb, hj] with y hby hjy
      exact hby.trans (congrArg (A p t y) (PiLp.ext fun word => hjy word))
    have hlow : F.toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube]
        fun y => ∑ γ : (x.c.stage x.i).fam.Γ v u, ∑ d : ↥(Finset.Icc 2 x.order),
          (x.c.stage x.i).physCoeff v u γ d.1 t y
            (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
              (Y γ).toFunction.jet ⟨⟨d.1 - 1, by
                have hh := (Finset.mem_Icc.mp d.2).2.trans x.c.order_ge; omega⟩, word⟩ y) := by
      convert hh using 1
      funext y
      dsimp only [I, A, r]
      rw [Fintype.sum_prod_type]
    filter_upwards [hlow] with y hy
    rw [hy]
    apply Finset.sum_congr rfl
    intro γ _
    exact (x.physical_flux_orders v u γ t (Y γ) y).symm
  · intro hP φ
    have hAd (p : I) := weak_quiet_constituent_adjoint hdepth x hfloor hhalf
      v u p.1 p.2.val p.2.property t ht
    let Ci (p : I) := (hAd p).choose
    let Ai (p : I) := (hAd p).choose_spec.choose
    have hob1 := S.adjoint v u t ht
    obtain ⟨C, Adj, he, _⟩ := hob1
    have hop : x.source v u t = fun ψ y => Real.sqrt (x.mass u / x.mass v) *
        ∑ p : I, weakQuietPrimalSource (r p) (A p t) ψ y := by
      funext ψ y
      rw [x.source_orders]
      dsimp only [I, r, A]
      rw [Fintype.sum_prod_type]
      congr 1
      apply Finset.sum_congr rfl
      intro γ _
      exact (Finset.sum_coe_sort _ _).symm
    rw [he 0 hP]
    have hpair := weak_quiet_source_sum_scaled_native_pair x.bounds.1 ht
      (by unfold WeakQuietExpansionCase.order; omega) r
      (fun p => by have hh := Finset.mem_Icc.mp p.2.property; dsimp only [r]; omega)
      A hfin (fun p => (hc p t ht).of_le (by exact_mod_cast hJ1))
      (fun p => hp p t) Ci Ai (Adj.ofOp hop) hP hP U u0
      (fun p => by dsimp only [U]; rw [← hu p.1]; rfl) φ
    simpa only [F, map_sum, CycleComparison.Reconstruction.adj_ofOp] using hpair

/-- Each incoming flux of a nonroot passage is a genuine native L² curve. -/
theorem weak_quiet_nonroot_incoming_flux {plan : WeakPassagePlan}
    {prices : WeakQuietPathPrices} (x : WeakQuietExpansionCase plan prices)
    (hfloor : weakComparisonCoeffFloor x.R ≤ x.c.M)
    (htop : x.i < x.c.M + x.A.Jw) :
    ∃ Q : x.Vertex → x.Vertex → ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ℝ)),
      (∀ v u, MemLp (Q v u) 2 (volume.restrict
        (Set.Icc (x.run.tq (x.i + 1)) (x.run.a + x.A.T₀)))) ∧
      ∀ v u t, t ∈ Set.Icc (x.run.tq (x.i + 1)) (x.run.a + x.A.T₀) →
        (Q v u t).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube]
          fun y => ∑ γ : (x.c.stage x.i).fam.Γ v u, ∑ d : ↥(Finset.Icc 2 x.c.Dm),
            (x.c.stage x.i).physCoeff v u γ d.1 t y
              (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
                (x.run.Urk x.i v u γ t).toFunction.jet
                  ⟨⟨d.1 - 1, by have := Finset.mem_Icc.mp d.2; omega⟩, word⟩ y) := by
  have hob2 := x.stage_solution htop
  obtain ⟨f, hs⟩ := hob2
  have hΛ : 1 ≤ x.c.D.Λ := by
    rw [x.c.base_eq]
    exact (by norm_num : 1 ≤ 128).trans ((plan.base_ge x.B).trans x.c.base_ge)
  have he : 0 < x.c.D.eps x.i := Construction.Stream.ocEpsilon_pos hΛ
  let reg := fun v u γ (d : ↥(Finset.Icc 2 x.c.Dm)) =>
    weakPassage_physCoeff_regular x.c hfloor x.i x.level_lt x.level_le
      (x.run.tq (x.i + 1)) (x.run.a + x.A.T₀) v u γ d.1
      (Finset.mem_Icc.1 d.2).1
  exact weak_quiet_kernel_incoming_flux_exists (J := 0) he (x.c.stage x.i)
    (x.run.Urk x.i) hs.2.2.2.2.1
    (fun v u γ d => (reg v u γ d).2.2.2 0 (Nat.zero_le _))
    (fun v u γ d => (reg v u γ d).1)
    (fun v u γ d t _ => (reg v u γ d).2.1 0 (Nat.zero_le _) t)
    (fun v u γ d t _ => (reg v u γ d).2.2.1 t)

/-- A nonroot row evolves with the parent drift throughout the heat quiet margin. -/
theorem weak_quiet_nonroot_native_row {plan : WeakPassagePlan}
    {prices : WeakQuietPathPrices} (x : WeakQuietExpansionCase plan prices)
    (htop : x.i < x.c.M + x.A.Jw) (v : x.Vertex)
    (Q : ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ℝ)))
    (hraw : ∀ t ∈ Set.Icc (x.run.tq (x.i + 1)) (x.run.a + x.A.T₀),
      (Q t).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube]
        weakQuietKernelRawFlux (x.c.stage x.i) (x.run.Urk x.i) v t) :
    IsTorusForcedRow (x.c.D.κ x.c.M) x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) 2 0
      (truncateTorusHk (Nat.zero_le x.R.Kw) (x.run.Ur x.i v x.left))
      Q (fun _ => 0)
      (fun t => truncateTorusHk (Nat.zero_le x.R.Kw) (x.run.Ur x.i v t))
      (fun t => truncateTorusHk (Nat.succ_le_succ (Nat.zero_le x.R.Kw))
        (x.run.Urw x.i v t)) := by
  have hob3 := x.stage_solution htop
  obtain ⟨f, hs⟩ := hob3
  have hr := weak_quiet_kernel_native_row (x.c.stage x.i) x.c.P x.R.nW
    x.A.φ₀ x.A.hφ₀ hs v Q hraw
  have hr' := CycleComparison.Error.isCoupledWeakSolutionTorus_restrict_left
    x.quiet.2.1 hr
  have hr'' := CycleComparison.Error.isCoupledWeakSolutionTorus_restrict_right
    x.bounds.2.2.1 x.heat_window.1.le hr'
  exact weakQuiet_forcedRow_drift_congr hr'' x.heat_velocity_eq

/-- The supplied high carriers agree with the actual row values almost
 everywhere on the heat quiet margin. -/
theorem weak_quiet_nonroot_input_value {plan : WeakPassagePlan}
    {prices : WeakQuietPathPrices} (x : WeakQuietExpansionCase plan prices)
    (htop : x.i < x.c.M + x.A.Jw) (v u : x.Vertex)
    (γ : (x.c.stage x.i).fam.Γ v u) :
    ∀ᵐ t ∂volume.restrict (Set.Icc x.left x.right),
      (x.run.Urk x.i v u γ t).val (valueIndex2 (x.R.Kw + x.c.Dm - 1)) =
        (x.run.Ur x.i u t).val (valueIndex2 x.R.Kw) := by
  have hob4 := x.stage_solution htop
  obtain ⟨f, hs⟩ := hob4
  exact ae_restrict_of_ae_restrict_of_subset x.heat_window.2
    (weak_quiet_kernel_input_value (x.c.stage x.i) x.c.P x.R.nW x.A.φ₀ x.A.hφ₀
      x.A.mass hs v u γ)

end AVRegularity.WeakEntryProofs.Assembly
end
end
