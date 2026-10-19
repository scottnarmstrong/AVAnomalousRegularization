-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence
import AVRegularity.CycleComparison.Lift.MixedMultilinearOperatorNormBound
import AVRegularity.CycleComparison.Residual.Jets.Lift
public import AVRegularity.CycleComparison.Lift.ProfileCellInitial
import AVRegularity.CycleComparison.Lift.FirstDiagonalSource
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.CleanupChain
import AVRegularity.CycleComparison.Lift.LiftApplyFiniteVectorSynthesis
public import AVRegularity.Statements.Intermediate.CycleComparison.IsLiftSequence
public import Mathlib.Algebra.Lie.OfAssociative

section
@[expose] public noncomputable section

section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! One summable frequency majorant controls each actual response jet throughout the finite time window. -/

theorem profileModeResponse_uniform_jet_bound (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (a b κ : ℝ) (hab : a ≤ b) (hκ : 0 < κ) (hi : IntegrableOn g (Icc a b))
    (hg : ∀ s ∈ Icc a b, κ ≤ g s) (j : ℕ) (C C₀ : ℝ) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hf : ∀ s ∈ Icc a b, ContDiff ℝ j (f s))
    (hp : ∀ s ∈ Icc a b, Function.Periodic (f s) 1)
    (hj : ∀ s ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1, ‖iteratedDeriv j (f s) x‖ ≤ C)
    (hzero : ∀ s ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1, ‖f s x‖ ≤ C₀)
    (n : ℤ) (t : ℝ) (ht : t ∈ Icc a b) :
    ‖profileFourierFrequency n ^ j * profileModeResponse g f a t n‖ ≤
      profileJetMajorant (C / κ) (C₀ * (b - a)) n := by
  apply profileJetMajorant_bound (Icc a b) (fun t n => profileModeResponse g f a t n)
    j (C / κ) (C₀ * (b - a)) (mul_nonneg hC₀ (sub_nonneg.mpr hab)) ?_ ?_ n t ht
  · intro r hr m hm
    have hs : Icc a r ⊆ Icc a b := Icc_subset_Icc le_rfl hr.2
    exact profileModeResponse_frequency_weight_bound g f a r κ hr.1 hκ (hi.mono_set hs)
      (fun s h => hg s (hs h)) j C hC (fun s h => hf s (hs h))
      (fun s h => hp s (hs h)) (fun s h => hj s (hs h)) m hm
  · intro r hr
    exact profileModeResponse_zero_norm_le g f a b r C₀ hr hC₀ hzero

theorem profileModeResponse_uniform_rhs_bound (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (a b κ M C C₀ : ℝ) (hκ : 0 < κ) (hi : IntegrableOn g (Icc a b))
    (hg : ∀ s ∈ Icc a b, κ ≤ g s) (hgb : ∀ s ∈ Icc a b, |g s| ≤ M)
    (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (hf : ∀ s ∈ Icc a b, ContDiff ℝ 2 (f s))
    (hp : ∀ s ∈ Icc a b, Function.Periodic (f s) 1)
    (hj : ∀ s ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1, ‖iteratedDeriv 2 (f s) x‖ ≤ C)
    (hzero : ∀ s ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1, ‖f s x‖ ≤ C₀)
    (n : ℤ) (t : ℝ) (ht : t ∈ Icc a b) :
    ‖(-(‖profileFourierFrequency n‖ ^ 2) * g t) • profileModeResponse g f a t n +
        unitProfileFourierCoeff (f t) n‖ ≤ profileJetMajorant (M * (C / κ) + C) C₀ n := by
  have h := profileJetMajorant_bound (Icc a b)
    (fun t n => (-(‖profileFourierFrequency n‖ ^ 2) * g t) • profileModeResponse g f a t n +
      unitProfileFourierCoeff (f t) n) 0 (M * (C / κ) + C) C₀ hC₀ ?_ ?_ n t ht
  · simpa only [pow_zero, one_mul] using h
  · intro r hr m hm
    have hs : Icc a r ⊆ Icc a b := Icc_subset_Icc le_rfl hr.2
    exact profileModeResponse_rhs_frequency_bound g f a r κ M C hr.1 hκ (hi.mono_set hs)
      (fun s h => hg s (hs h)) (hgb r hr) hC (fun s h => hf s (hs h))
      (fun s h => hp s (hs h)) (fun s h => hj s (hs h)) m hm
  · intro r hr
    simpa only [profileFourierFrequency, Int.cast_zero, mul_zero, norm_zero,
      zero_pow (by decide : 2 ≠ 0), neg_zero, zero_mul, zero_smul, zero_add] using
      unitProfileFourierCoeff_norm_le (f r) 0 C₀ (hzero r hr)

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! Literal Fourier response synthesis commutes with real constant scalar factors. -/

theorem unitProfileFourierCoeff_real_smul (f : ℝ → ℂ) (c : ℝ) (n : ℤ) :
    unitProfileFourierCoeff (fun x => c • f x) n = c • unitProfileFourierCoeff f n := by
  have hh := fourierCoeffOn.const_smul f (c : ℂ) n (by norm_num : (0 : ℝ) < 1)
  simpa only [unitProfileFourierCoeff, smul_eq_mul, Complex.real_smul] using! hh

theorem profileModeResponse_real_smul (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (c a t : ℝ) (n : ℤ) :
    profileModeResponse g (fun s x => c • f s x) a t n = c • profileModeResponse g f a t n := by
  simp only [profileModeResponse, unitProfileFourierCoeff_real_smul]
  exact transverseModeResponse_const_smul _ c g _ a t

theorem profileCellResponse_real_smul (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (c a t x : ℝ) :
    profileCellResponse g (fun s y => c • f s y) a t x = c • profileCellResponse g f a t x := by
  unfold profileCellResponse profileFourierSeries
  simp only [profileModeResponse_real_smul, mul_smul_comm]
  exact tsum_const_smul'' c

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The classical profile synthesis has the same finite spatial regularity and periodicity on the two-dimensional cell. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem transverse_profile_contDiff (f : ℝ → E) (q : ℕ) (hf : ContDiff ℝ q f) (par : Fin 2) :
    ContDiff ℝ q (fun z : Vec 2 => f (z par.rev)) :=
  hf.comp (ContinuousLinearMap.proj par.rev : Vec 2 →L[ℝ] ℝ).contDiff

omit [NormedSpace ℝ E] [NormedAddCommGroup E] in
theorem transverse_profile_periodic (f : ℝ → E) (hp : Function.Periodic f 1) (par : Fin 2) :
    AVenhance.IsZ2Periodic (fun z : Vec 2 => f (z par.rev)) := by
  intro n z
  simpa only [Pi.add_apply, AVenhance.latticeShift, zsmul_eq_mul, mul_one] using
    hp.zsmul (n par.rev) (z par.rev)

theorem profileResponse_transverse_contDiff (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (a t κ : ℝ) (hat : a ≤ t) (hκ : 0 < κ) (hi : IntegrableOn g (Icc a t))
    (hg : ∀ s ∈ Icc a t, κ ≤ g s) (q : ℕ) (C : ℕ → ℝ)
    (hC : ∀ j ≤ q, 0 ≤ C j) (hf : ∀ s ∈ Icc a t, ContDiff ℝ q (f s))
    (hp : ∀ s ∈ Icc a t, Function.Periodic (f s) 1)
    (hj : ∀ j ≤ q, ∀ s ∈ Icc a t, ∀ x ∈ Icc (0 : ℝ) 1, ‖iteratedDeriv j (f s) x‖ ≤ C j)
    (par : Fin 2) : ContDiff ℝ q (fun z : Vec 2 => profileCellResponse g f a t (z par.rev)) := by
  exact transverse_profile_contDiff _ q
    (profileCellResponse_contDiff g f a t κ hat hκ hi hg q C hC hf hp hj) par

theorem profileResponse_transverse_periodic (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (a t : ℝ) (par : Fin 2) :
    AVenhance.IsZ2Periodic (fun z : Vec 2 => profileCellResponse g f a t (z par.rev)) :=
  transverse_profile_periodic _ (profileCellResponse_periodic g f a t) par

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Physical mean fluxes match the dilated coarse input flux before taking divergence. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem scaledMeanCoefficient_flux (c ρ : ℝ) (hρ : ρ ≠ 0) (τ : ℝ → ℝ)
    (b : MeanCoeff ι h) (d : ℕ) (hd : 1 ≤ d) (α : DerivativeWord2 (d - 1))
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) (x : Vec 2) (k : Fin 2) (v : ι) :
    (∑ u, scaledMeanCoefficient c ρ τ b d α t x k v u (orderedDerivative α f x u)) =
      (c * ρ) • ∑ u, b d α (τ t) (ρ⁻¹ • x) k v u
        (orderedDerivative α (fun X => f (ρ • X)) (ρ⁻¹ • x) u) := by
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro u _
  have he := congrFun (orderedDerivative_dilation α ρ f hf) (ρ⁻¹ • x)
  have harg : ρ • (ρ⁻¹ • x) = x := by rw [smul_smul, mul_inv_cancel₀ hρ, one_smul]
  rw [harg] at he
  rw [he]
  change (c * ρ ^ d) • b d α (τ t) (ρ⁻¹ • x) k v u (orderedDerivative α f x u) = _
  simp only [Pi.smul_apply, map_smul, smul_smul]
  congr 1
  have hd' : d - 1 + 1 = d := by omega
  rw [mul_assoc, ← pow_succ', hd']
end

/-! On coarse inputs, a covariant word has exactly its slow monomial power. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dEps_independent_smul (η ε : ℝ) (i : Fin 2) (c : ℝ) (f : Vec 2 → E) :
    dEps η ε i (fun X _ => c • f X) =
      fun X _ => (c * (Real.sqrt η * ε)) • fderiv ℝ f X (basisVec i) := by
  funext X z
  change fderiv ℝ (fun _ : Vec 2 => c • f X) z (basisVec i) +
    (Real.sqrt η * ε) • fderiv ℝ (c • f) X (basisVec i) = _
  rw [fderiv_fun_const, congrFun (fderiv_const_smul_field c) X]
  simp [smul_smul, mul_comm]

theorem dEpsWord_independent (η ε : ℝ) {m : ℕ} (α : DerivativeWord2 m)
    (f : Vec 2 → E) : dEpsWord η ε α (fun X _ => f X) =
      fun X _ => (Real.sqrt η * ε) ^ m • orderedDerivative α f X := by
  have he : ∀ (l : List (Fin 2)) (g : Vec 2 → E) (c : ℝ),
      l.foldl (fun Ψ i => dEps η ε i Ψ) (fun X _ => c • g X) =
        fun X _ => (c * (Real.sqrt η * ε) ^ l.length) •
          l.foldl (fun g' i => fun X => fderiv ℝ g' X (basisVec i)) g X := by
    intro l
    induction l with
    | nil => intro g c; simp
    | cons i l ih =>
      intro g c
      simp only [List.foldl_cons]
      rw [dEps_independent_smul, ih]
      funext X z
      simp only [List.length_cons, pow_succ]
      congr 1
      ring
  have hh := he (List.ofFn α) f 1
  simpa only [one_smul, one_mul, List.length_ofFn, dEpsWord, orderedDerivative] using hh
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Translation identities preserve periodicity under both literal partial operators. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem slowPartial_periodic_of_periodic (Φ : Vec 2 → Vec 2 → E)
    (hΦ : ∀ X, AVenhance.IsZ2Periodic (Φ X)) (i : Fin 2) :
    ∀ X, AVenhance.IsZ2Periodic (slowPartial i Φ X) := by
  intro X k z
  have he : (fun Y => Φ Y (z + AVenhance.latticeShift k)) = fun Y => Φ Y z :=
    funext fun Y => hΦ Y k z
  unfold slowPartial
  rw [he]

theorem fastPartial_periodic_of_periodic (Φ : Vec 2 → Vec 2 → E)
    (hΦ : ∀ X, AVenhance.IsZ2Periodic (Φ X)) (i : Fin 2) :
    ∀ X, AVenhance.IsZ2Periodic (fastPartial i Φ X) := by
  intro X k z
  have he : (fun y => Φ X (y + AVenhance.latticeShift k)) = Φ X := funext (hΦ X k)
  have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := Φ X) (x := z) (AVenhance.latticeShift k)
  rw [he] at hd
  unfold fastPartial
  rw [← hd]
end

/-! Covariant derivatives act linearly on classical finite flux polynomials. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dEps_smul (η ε : ℝ) (i : Fin 2) (c : ℝ)
    (Φ : Vec 2 → Vec 2 → E) :
    dEps η ε i (fun X z => c • Φ X z) = fun X z => c • dEps η ε i Φ X z := by
  funext X z
  change fderiv ℝ (c • Φ X) z (basisVec i) +
    (Real.sqrt η * ε) • fderiv ℝ (c • (fun X => Φ X z)) X (basisVec i) = _
  rw [congrFun (fderiv_const_smul_field c) z,
    congrFun (fderiv_const_smul_field c) X]
  simp [dEps, fastPartial, slowPartial, smul_add, smul_smul, mul_comm]

theorem dEps_finset_sum {κ : Type*} (s : Finset κ) (η ε : ℝ) (i : Fin 2)
    (Φ : κ → Vec 2 → Vec 2 → E) (X z : Vec 2)
    (hz : ∀ a ∈ s, DifferentiableAt ℝ (Φ a X) z)
    (hX : ∀ a ∈ s, DifferentiableAt ℝ (fun X => Φ a X z) X) :
    dEps η ε i (fun X z => ∑ a ∈ s, Φ a X z) X z =
      ∑ a ∈ s, dEps η ε i (Φ a) X z := by
  have hfast := fderiv_fun_sum hz
  have hslow := fderiv_fun_sum hX
  simp only [dEps, fastPartial, slowPartial, hfast, hslow, sum_apply,
    Finset.smul_sum, Finset.sum_add_distrib]
end

/-! Input evaluations recover operator-valued mixed jet norms with constant one. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem mixed_operator_jet_norm_le_from_apply (p q : ℕ) (f : Vec 2 → Vec 2 → (E →L[ℝ] F))
    (hf : IsBoxSmooth p q f) (X z : Vec 2) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ ξ : E,
      ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (fun y => f Y y ξ) z) X‖ ≤ C * ‖ξ‖) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (f Y) z) X‖ ≤ C := by
  apply mixed_multilinear_operator_norm_le_from_apply _ C hC
  intro ξ
  let l : (E →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F ξ
  let A := ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin q => Vec 2) (E →L[ℝ] F) F l
  have he : (fun Y => iteratedFDeriv ℝ q (fun y => f Y y ξ) z) =
      A ∘ (fun Y => iteratedFDeriv ℝ q (f Y) z) := by
    funext Y
    exact l.iteratedFDeriv_comp_left (hf.1 Y).contDiffAt le_rfl
  have hh := hb ξ
  rw [he, A.iteratedFDeriv_comp_left (hf.2.1 q le_rfl z).contDiffAt le_rfl] at hh
  exact hh
end

/-! A slow directional derivative consumes exactly one slow jet without using the fast reserve. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_mixed_slow_direction_le {r q : ℕ} {f : Vec 2 → Vec 2 → E}
    (hf : IsBoxSmooth (r + 1) q f) (v : Vec 2) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q
      (fun y => fderiv ℝ (fun Z => f Z y) Y v) z) X‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ (r + 1) (fun Y => iteratedFDeriv ℝ q (f Y) z) X‖ := by
  have he : (fun Y => iteratedFDeriv ℝ q
      (fun y => fderiv ℝ (fun Z => f Z y) Y v) z) =
      fun Y => fderiv ℝ (fun Z => iteratedFDeriv ℝ q (f Z) z) Y v := by
    funext Y
    exact (slowDir_aux q E f (hf.mono (by omega) le_rfl) v Y).2 z
  rw [he, iteratedFDeriv_fderiv_apply (hf.2.1 q le_rfl z).contDiffAt v]
  have hb := (jetApply (F := ContinuousMultilinearMap ℝ (fun _ : Fin q => Vec 2) E) r v).le_opNorm
    (iteratedFDeriv ℝ (r + 1) (fun Y => iteratedFDeriv ℝ q (f Y) z) X)
  apply hb.trans
  exact mul_le_mul_of_nonneg_right (jetApply_norm_le
    (E := ContinuousMultilinearMap ℝ (fun _ : Fin q => Vec 2) E) r v) (norm_nonneg _)
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVenhance.Infra.Torus
namespace AVRegularity.CycleComparison.Lift

/-! Both the support and values of all two-dimensional transverse profile coefficients. -/

theorem smoothFourierCoeff_transverse_profile_all (par : Fin 2) (f : ℝ → ℂ)
    (hf : ContDiff ℝ 1 f) (hp : Function.Periodic f 1) (k : Fin 2 → ℤ) :
    smoothFourierCoeff (fun z : Vec 2 => f (z par.rev)) k =
      if k par = 0 then unitProfileFourierCoeff f (k par.rev) else 0 := by
  by_cases hk : k par = 0
  · simpa only [hk, ite_true] using smoothFourierCoeff_transverse_profile par f hf.continuous hp k hk
  · rw [ite_eq_right hk]
    apply smoothFourierCoeff_zero_of_transverse par _
      (hf.comp (ContinuousLinearMap.proj par.rev : Vec 2 →L[ℝ] ℝ).contDiff) _ _ k hk
    · intro n z
      simpa only [Pi.add_apply, intVector, zsmul_eq_mul, mul_one] using!
        hp.zsmul (n par.rev) (z par.rev)
    · intro z
      change fderiv ℝ (fun y : Vec 2 => f (y par.rev)) z (basisVec par) = 0
      rw [fderiv_profile_basis f (hf.differentiable (by norm_num))]
      fin_cases par <;> simp

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! An explicit coefficient synthesis map applies the centered transverse primitive entrywise. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

def centeredFluxLiftCoefficient (par : Fin 2) (c : LiftCoeff ι h) (k : Fin 2) : LiftCoeff ι h :=
  fun m α t X z v u => transverseCenteredFlux par
    (fun r => c m α t X (r • basisVec par.rev) v u) k z

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! Literal finite-coordinate response preserves periodicity and real scalar factors. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem finiteProfileResponse_periodic (g : ℝ → ℝ) (f : ℝ → ℝ → E) (a t : ℝ) :
    Function.Periodic (finiteProfileResponse g f a t) 1 := by
  intro x
  apply (Module.finBasis ℝ E).equivFunL.injective
  funext j
  simp only [finiteProfileResponse_coordinate]
  rw [profileCellResponse_periodic]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Linear operations on full mixed jets preserve their quantitative majorants. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_mixed_jet_add_le {r q : ℕ} {f g : Vec 2 → Vec 2 → E}
    (hf : IsBoxSmooth r q f) (hg : IsBoxSmooth r q g) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q (fun y => f Y y + g Y y) z) X‖ ≤
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q (f Y) z) X‖ +
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q (g Y) z) X‖ := by
  have he : (fun Y => iteratedFDeriv ℝ q (fun y => f Y y + g Y y) z) =
      fun Y => iteratedFDeriv ℝ q (f Y) z + iteratedFDeriv ℝ q (g Y) z := by
    funext Y
    exact iteratedFDeriv_add_apply (hf.1 Y).contDiffAt (hg.1 Y).contDiffAt
  rw [he]
  change ‖iteratedFDeriv ℝ r ((fun Y => iteratedFDeriv ℝ q (f Y) z) +
    (fun Y => iteratedFDeriv ℝ q (g Y) z)) X‖ ≤ _
  rw [iteratedFDeriv_add_apply (hf.2.1 q le_rfl z).contDiffAt
    (hg.2.1 q le_rfl z).contDiffAt]
  exact norm_add_le _ _

theorem norm_mixed_jet_const_smul {r q : ℕ} {f : Vec 2 → Vec 2 → E}
    (hf : IsBoxSmooth r q f) (a : ℝ) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q (fun y => a • f Y y) z) X‖ =
      |a| * ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q (f Y) z) X‖ := by
  have he : (fun Y => iteratedFDeriv ℝ q (fun y => a • f Y y) z) =
      fun Y => a • iteratedFDeriv ℝ q (f Y) z := by
    funext Y
    exact iteratedFDeriv_const_smul_apply (hf.1 Y).contDiffAt
  rw [he, iteratedFDeriv_const_smul_apply' (hf.2.1 q le_rfl z).contDiffAt]
  exact norm_smul a _

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Ordered slow words preserve the independent fast reserve. -/

theorem isBoxSmooth_orderedDerivative_slow (r : ℕ) :
    ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      (p q : ℕ) (f : Vec 2 → Vec 2 → E) (w : DerivativeWord2 r),
      IsBoxSmooth (p + r) q f →
      IsBoxSmooth p q (fun X z => orderedDerivative w (fun Y => f Y z) X) := by
  induction r with
  | zero =>
    intro E _ _ p q f w hf
    simpa only [orderedDerivative_zero, Nat.add_zero] using hf
  | succ r ih =>
    intro E _ _ p q f w hf
    have hh := ih (p + 1) q f (fun i : Fin r => w i.castSucc)
      (by simpa only [Nat.add_assoc, Nat.add_comm 1 r] using hf)
    have hd := isBoxSmooth_slow_direction hh (basisVec (w (Fin.last r)))
    simpa only [orderedDerivative_succ] using! hd

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The actual cross operators preserve fast lattice periodicity without an extra joint reserve. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cellB1_periodic (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (v : ℝ → Vec 2 → Vec 2) (t : ℝ) (Φ : Vec 2 → Vec 2 → E)
    (hΦ : ∀ X, AVenhance.IsZ2Periodic (Φ X)) (hv : AVenhance.IsZ2Periodic (v t)) :
    ∀ X, AVenhance.IsZ2Periodic (cellB1 η G v t Φ X) := by
  have hslow (k : Fin 2) := slowPartial_periodic_of_periodic Φ hΦ k
  have hfast (k : Fin 2) := fastPartial_periodic_of_periodic Φ hΦ k
  have hfastslow (i j : Fin 2) :=
    fastPartial_periodic_of_periodic (slowPartial j Φ) (hslow j) i
  have hgp (i j : Fin 2) : ∀ X, AVenhance.IsZ2Periodic
      (fun z => G t X i j • fastPartial j Φ X z) := by
    intro X n z
    exact congrArg (fun x => G t X i j • x) (hfast j X n z)
  have hgps (i j : Fin 2) := slowPartial_periodic_of_periodic
    (fun X z => G t X i j • fastPartial j Φ X z) (hgp i j) i
  intro X n z
  change (∑ k : Fin 2, (Real.sqrt η * v t (z + AVenhance.latticeShift n) k) •
      slowPartial k Φ X (z + AVenhance.latticeShift n)) -
    Real.sqrt η • ∑ i : Fin 2, ∑ j : Fin 2,
      (G t X i j • fastPartial i (slowPartial j Φ) X (z + AVenhance.latticeShift n) +
        slowPartial i (fun Y y => G t Y i j • fastPartial j Φ Y y) X
          (z + AVenhance.latticeShift n)) = _
  rw [hv n z]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    exact congrArg (fun x => (Real.sqrt η * v t z k) • x) (hslow k X n z)
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg₂ (fun a b => G t X i j • a + b)
      (hfastslow i j X n z) (hgps i j X n z)

theorem cellB2_periodic (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (t : ℝ) (Φ : Vec 2 → Vec 2 → E) (hΦ : ∀ X, AVenhance.IsZ2Periodic (Φ X)) :
    ∀ X, AVenhance.IsZ2Periodic (cellB2 η G t Φ X) := by
  have hslow (j : Fin 2) := slowPartial_periodic_of_periodic Φ hΦ j
  have hprod (i j : Fin 2) : ∀ X, AVenhance.IsZ2Periodic
      (fun z => G t X i j • slowPartial j Φ X z) := by
    intro X n z
    exact congrArg (fun x => G t X i j • x) (hslow j X n z)
  have hp (i j : Fin 2) := slowPartial_periodic_of_periodic
    (fun X z => G t X i j • slowPartial j Φ X z) (hprod i j) i
  intro X n z
  unfold cellB2
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact hp i j X n z

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Entrywise primitive synthesis commutes with the complete finite tested lift action. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] [∀ i, CompleteSpace (h i)]

theorem liftApply_centeredFluxLiftCoefficient (par k : Fin 2) (n : ℕ) (c : LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (X z : Vec 2) (v : ι)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ u,
      Continuous (fun r : ℝ => c m α t X (r • basisVec par.rev) v u)) :
    liftApply n (centeredFluxLiftCoefficient par c k) f t X z v =
      transverseCenteredFlux par
        (fun r => liftApply n c f t X (r • basisVec par.rev) v) k z := by
  have hu (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (u : ι) :
      Continuous (fun r : ℝ => c m α t X (r • basisVec par.rev) v u
        (orderedDerivative α (f t) X u)) :=
    (ContinuousLinearMap.apply ℝ (h v) (orderedDerivative α (f t) X u)).continuous.comp (hc m hm α u)
  have hα (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) :
      Continuous (fun r : ℝ => ∑ u, c m α t X (r • basisVec par.rev) v u
        (orderedDerivative α (f t) X u)) :=
    continuous_finsetSum Finset.univ (fun u _ => hu m hm α u)
  have hm (m : ℕ) (hmem : m ∈ Finset.range (n + 1)) :
      Continuous (fun r : ℝ => ∑ α : DerivativeWord2 m, ∑ u,
        c m α t X (r • basisVec par.rev) v u (orderedDerivative α (f t) X u)) :=
    continuous_finsetSum Finset.univ (fun α _ => hα m (by have := Finset.mem_range.mp hmem; omega) α)
  unfold liftApply
  rw [transverseCenteredFlux_finset_sum par k (Finset.range (n + 1)) _ hm z]
  apply Finset.sum_congr rfl
  intro m hmem
  have hmn : m ≤ n := by have := Finset.mem_range.mp hmem; omega
  rw [transverseCenteredFlux_finset_sum par k Finset.univ _ (fun α _ => hα m hmn α) z]
  apply Finset.sum_congr rfl
  intro α _
  rw [transverseCenteredFlux_finset_sum par k Finset.univ _ (fun u _ => hu m hmn α u) z]
  apply Finset.sum_congr rfl
  intro u _
  exact (transverseCenteredFlux_clm par k
    (ContinuousLinearMap.apply ℝ (h v) (orderedDerivative α (f t) X u))
    (fun r => c m α t X (r • basisVec par.rev) v u) (hc m hmn α u) z).symm

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Scalar duals of linear profiles inherit the full mixed vector bound. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_mixed_dual_linear_profile_le (p q r j : ℕ) (hr : r ≤ p) (hj : j ≤ q)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth p q f)
    (L : ℝ →L[ℝ] Vec 2) (A : E →L[ℝ] F) (X : Vec 2) (x : ℝ) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedDeriv j (fun y => A (f Y (L y))) x) X‖ ≤
      ‖A‖ * ‖L‖ ^ j *
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (f Y) (L x)) X‖ := by
  apply (norm_mixed_linear_profile_le p q r j hr hj
    (fun Y z => A (f Y z)) (hf.clm_comp A) L X x).trans
  have h := norm_mixed_jet_postcomposition_le p q r j hr hj f hf.1
    (fun z => hf.2.1 j hj z) A X (L x)
  have hh := mul_le_mul_of_nonneg_left h (pow_nonneg (norm_nonneg L) j)
  simpa only [← mul_assoc, mul_comm (‖L‖ ^ j) ‖A‖] using hh
end

/-! An intermediate inverse separates metric and forcing differences without changing jet orders. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_mixed_jet_difference_triangle {r j : ℕ}
    {f m g : Vec 2 → Vec 2 → E}
    (hfm : IsBoxSmooth r j (fun X z => f X z - m X z))
    (hmg : IsBoxSmooth r j (fun X z => m X z - g X z)) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (fun y => f Y y - g Y y) z) X‖ ≤
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (fun y => f Y y - m Y y) z) X‖ +
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (fun y => m Y y - g Y y) z) X‖ := by
  have he (Y y : Vec 2) : f Y y - g Y y =
      (f Y y - m Y y) + (m Y y - g Y y) :=
    (sub_add_sub_cancel _ _ _).symm
  simp_rw [he]
  exact norm_mixed_jet_add_le hfm hmg X z
end

/-! Subtraction costs the sum of the two genuine mixed jet majorants. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_mixed_jet_sub_le {p q : ℕ} {f g : Vec 2 → Vec 2 → E}
    (hf : IsBoxSmooth p q f) (hg : IsBoxSmooth p q g) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (fun y => f Y y - g Y y) z) X‖ ≤
      ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (f Y) z) X‖ +
      ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (g Y) z) X‖ := by
  have he (Y y : Vec 2) : f Y y - g Y y = f Y y + (-1 : ℝ) • g Y y := by simp [sub_eq_add_neg]
  simp_rw [he]
  have hh := norm_mixed_jet_add_le hf (hg.const_smul (-1 : ℝ)) X z
  rw [norm_mixed_jet_const_smul hg] at hh
  simpa only [abs_neg, abs_one, one_mul] using hh
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Positive-order truncation makes the tail flux array supported globally in time. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

def positiveLiftCoefficient (R : ℕ) (c : LiftCoeff ι h) : LiftCoeff ι h :=
  fun m α t X z v u => if 1 ≤ m ∧ m ≤ R then c m α t X z v u else 0

def positiveFluxLiftCoefficient (par : Fin 2) (R : ℕ) (c : LiftCoeff ι h)
    (k : Fin 2) : LiftCoeff ι h :=
  centeredFluxLiftCoefficient par (positiveLiftCoefficient R c) k

omit [Fintype ι] in
theorem positiveFluxLiftCoefficient_outside (par k : Fin 2) (R : ℕ) (c : LiftCoeff ι h)
    (m : ℕ) (hm : ¬(1 ≤ m ∧ m ≤ R)) (α : DerivativeWord2 m)
    (t : ℝ) (X z : Vec 2) (v u : ι) :
    positiveFluxLiftCoefficient par R c k m α t X z v u = 0 := by
  simp only [positiveFluxLiftCoefficient, centeredFluxLiftCoefficient, positiveLiftCoefficient,
    ite_eq_right hm, transverseCenteredFlux]
  split_ifs
  · change centeredIntervalPrimitive (0 : ℝ → h u →L[ℝ] h v) (z par.rev) = 0
    exact centeredIntervalPrimitive_zero _
  · rfl

omit [Fintype ι] in
theorem positiveFluxLiftCoefficient_perm (par k : Fin 2) (R : ℕ) (c : LiftCoeff ι h)
    (m : ℕ) (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m))
    (hc : c m (α ∘ σ) = c m α) :
    positiveFluxLiftCoefficient par R c k m (α ∘ σ) =
      positiveFluxLiftCoefficient par R c k m α := by
  funext t X z v u
  simp only [positiveFluxLiftCoefficient, centeredFluxLiftCoefficient, positiveLiftCoefficient, hc]

end AVRegularity.CycleComparison.Lift
end

section
open scoped ComplexConjugate
namespace AVRegularity.CycleComparison.Lift

/-! Real forcing gives conjugate-symmetric inverse Fourier modes. -/

theorem profileModeResponse_neg_of_real (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (hp : ∀ t, Function.Periodic (f t) 1) (hreal : ∀ t x, conj (f t x) = f t x)
    (a b : ℝ) (n : ℤ) :
    profileModeResponse g f a b (-n) = conj (profileModeResponse g f a b n) := by
  unfold profileModeResponse
  have he : (fun t => unitProfileFourierCoeff (f t) (-n)) =
      fun t => conj (unitProfileFourierCoeff (f t) n) := by
    funext t
    exact unitProfileFourierCoeff_neg_of_real (f t) (hp t) (hreal t) n
  rw [he]
  simp only [profileFourierFrequency_norm, Int.cast_neg, abs_neg]
  exact transverseModeResponse_conj _ g _ a b

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Restoring dimensions commutes exactly with the divergence-form mean action. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem scaledMeanCoefficient_meanApply (n : ℕ) (c ρ : ℝ) (hρ : ρ ≠ 0)
    (τ : ℝ → ℝ) (b : MeanCoeff ι h) (f : Vec 2 → ∀ i, h i)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) (x : Vec 2) :
    meanApply n (scaledMeanCoefficient c ρ τ b) (fun _ => f) t x =
      c • meanApply n b (fun _ X => f (ρ • X)) (τ t) (ρ⁻¹ • x) := by
  funext v
  simp only [meanApply, Pi.smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro k _
  have hflux : (fun X (v : ι) => ∑ u,
      scaledMeanCoefficient c ρ τ b d α t X k v u (orderedDerivative α f X u)) =
      fun X => (c * ρ) • (fun Y (v : ι) => ∑ u,
        b d α (τ t) Y k v u (orderedDerivative α (fun X => f (ρ • X)) Y u)) (ρ⁻¹ • X) := by
    funext X v
    exact scaledMeanCoefficient_flux c ρ hρ τ b d (by have := (Finset.mem_Icc.mp hd).1; omega)
      α f hf t X k v
  rw [hflux]
  have he := fderiv_dilation_smul (fun Y (v : ι) => ∑ u,
    b d α (τ t) Y k v u (orderedDerivative α (fun X => f (ρ • X)) Y u))
    ρ⁻¹ (c * ρ) x (basisVec k)
  have hscalar : c * ρ * ρ⁻¹ = c := by rw [mul_assoc, mul_inv_cancel₀ hρ, mul_one]
  rw [hscalar] at he
  exact congrFun he v
end

/-! Rectangular Schwarz interchange for a slow word and the full fast jet. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem orderedDerivative_slow_fast_jet (r : ℕ) (q : ℕ) :
    ∀ (f : Vec 2 → Vec 2 → E) (w : DerivativeWord2 r), IsBoxSmooth r q f →
      ∀ X z, iteratedFDeriv ℝ q
        (fun y => orderedDerivative w (fun Y => f Y y) X) z =
        orderedDerivative w (fun Y => iteratedFDeriv ℝ q (f Y) z) X := by
  induction r with
  | zero =>
    intro f w hf X z
    simp only [orderedDerivative_zero]
  | succ r ih =>
    intro f w hf X z
    let wp : DerivativeWord2 r := fun i => w i.castSucc
    let g : Vec 2 → Vec 2 → E := fun Y y => orderedDerivative wp (fun Z => f Z y) Y
    have hg : IsBoxSmooth 1 q g :=
      isBoxSmooth_orderedDerivative_slow r 1 q f wp
        (by simpa only [Nat.add_comm 1 r] using hf)
    have he : (fun Y => iteratedFDeriv ℝ q (g Y) z) =
        fun Y => orderedDerivative wp (fun Z => iteratedFDeriv ℝ q (f Z) z) Y := by
      funext Y
      exact ih f wp (hf.mono (Nat.le_succ r) le_rfl) Y z
    simp only [orderedDerivative_succ]
    change iteratedFDeriv ℝ q
      (fun y => fderiv ℝ (fun Y => g Y y) X (basisVec (w (Fin.last r)))) z = _
    rw [(slowDir_aux q E g hg (basisVec (w (Fin.last r))) X).2 z, he]
end

/-! Zero source entries have zero primitive flux entries. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem transverseCenteredFlux_zero (par k : Fin 2) (z : Vec 2) :
    transverseCenteredFlux par (0 : ℝ → E) k z = 0 := by
  unfold transverseCenteredFlux
  split_ifs
  · exact centeredIntervalPrimitive_zero _
  · rfl

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem centeredFluxLiftCoefficient_entry_eq_zero
    (par k : Fin 2) (c : LiftCoeff ι h) (m : ℕ) (α : DerivativeWord2 m)
    (t : ℝ) (v u : ι) (hz : ∀ X z, c m α t X z v u = 0) (X z : Vec 2) :
    centeredFluxLiftCoefficient par c k m α t X z v u = 0 := by
  change transverseCenteredFlux par (fun r => c m α t X (r • basisVec par.rev) v u) k z = 0
  have he : (fun r : ℝ => c m α t X (r • basisVec par.rev) v u) = 0 :=
    funext fun r => hz X (r • basisVec par.rev)
  rw [he]
  exact transverseCenteredFlux_zero par k z
end

/-! The classical lift operators annihilate constant input fields. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem orderedDerivative_const {m : ℕ} (α : DerivativeWord2 m) (c : E)
    (hm : 1 ≤ m) : orderedDerivative α (fun _ => c) = 0 := by
  have hne : List.ofFn α ≠ [] := by
    intro he
    have hl := congrArg List.length he
    simp only [List.length_ofFn, List.length_nil] at hl
    omega
  have hz : ∀ l : List (Fin 2),
      l.foldl (fun g i => fun x => fderiv ℝ g x (basisVec i)) (0 : Vec 2 → E) = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih =>
      simp only [List.foldl_cons]
      have hzero : (fun x => fderiv ℝ (0 : Vec 2 → E) x (basisVec i)) = 0 := by
        funext x
        simp
      rw [hzero]
      exact ih
  cases he : List.ofFn α with
  | nil => exact (hne he).elim
  | cons i l =>
    unfold orderedDerivative
    rw [he, List.foldl_cons]
    have hc : (fun x => fderiv ℝ (fun _ : Vec 2 => c) x (basisVec i)) = 0 := by
      funext x
      simp
    rw [hc]
    exact hz l

 theorem orderedDerivative_zero {m : ℕ} (α : DerivativeWord2 m) :
    orderedDerivative α (0 : Vec 2 → E) = 0 := by
  cases m with
  | zero => simp [orderedDerivative]
  | succ m => exact orderedDerivative_const α 0 (by omega)

theorem cellB1_const (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (v : ℝ → Vec 2 → Vec 2) (t : ℝ) (c : E) :
    cellB1 η G v t (fun _ _ => c) = 0 := by
  funext X z
  simp [cellB1, slowPartial, fastPartial]

theorem cellB2_const (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (t : ℝ) (c : E) : cellB2 η G t (fun _ _ => c) = 0 := by
  funext X z
  simp [cellB2, slowPartial]

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem sourceOp_const {D : ℕ} (edge : ConstituentEdges D h) (η ε t : ℝ)
    (c : ∀ i, h i) : sourceOp edge η ε t (fun _ _ => c) = 0 := by
  funext X z
  simp [sourceOp, sourceFlux_const_eq_zero, dEps, fastPartial, slowPartial]

theorem sourceCoeff_const {D : ℕ} (edge : ConstituentEdges D h) (η : ℝ)
    (j : ℕ) (t : ℝ) (c : ∀ i, h i) :
    sourceCoeff edge η j t (fun _ _ => c) = 0 := by
  funext X z
  simp [sourceCoeff, sourceOp_const]

theorem cellB1_zero_input {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (η : ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2) (t : ℝ) :
    cellB1 η G v t (0 : Vec 2 → Vec 2 → F) = 0 := by
  simpa using! cellB1_const η G v t (0 : F)

theorem sourceCoeff_zero_input {D : ℕ} (edge : ConstituentEdges D h) (η : ℝ)
    (j : ℕ) (t : ℝ) : sourceCoeff edge η j t (0 : Vec 2 → Vec 2 → ∀ i, h i) = 0 := by
  simpa using! sourceCoeff_const edge η j t (0 : ∀ i, h i)
end

/-! Normalization distributes through the literal uncentered recurrence, including the zero source order. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftA_normalized_component_expansion (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i)
    (hh n : ℕ) (t : ℝ) (X z : Vec 2) (v : ι) (A : Vec 2 →L[ℝ] ℝ) (lam : ℝ) :
    (Real.exp ((lam • A) X))⁻¹ • liftA Q Cc f hh n t X z v =
      (Real.exp ((lam • A) X))⁻¹ • cellB1 Q.η Q.G Q.v t
        (liftApply (n - 1) (Cc hh (n - 1)) f t) X z v +
      (if 2 ≤ n then (Real.exp ((lam • A) X))⁻¹ • cellB2 Q.η Q.G t
        (liftApply (n - 2) (Cc hh (n - 2)) f t) X z v else 0) -
      (if hh = 0 then 0 else ∑ j ∈ Finset.range (min D n + 1),
        (Real.exp ((lam • A) X))⁻¹ • sourceCoeff Q.edge Q.η j t
          (liftApply (n - j) (Cc (hh - 1) (n - j)) f t) X z v) := by
  split_ifs <;> simp only [liftA, *, Pi.add_apply, Pi.sub_apply, Pi.zero_apply,
    Finset.sum_apply, smul_add, smul_sub, smul_zero, Finset.smul_sum, ite_true, ite_false]
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Complex Fourier estimates on real duals recover vector mixed norms without a dimension factor. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mixed_jet_norm_le_from_complexified_real_duals (p q : ℕ)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth p q f)
    (X z : Vec 2) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ l : E →L[ℝ] ℝ,
      ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
        (fun y => ((l (f Y y) : ℝ) : ℂ)) z) X‖ ≤ C * ‖l‖) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (f Y) z) X‖ ≤ C := by
  apply mixed_jet_norm_le_from_real_duals p q f hf X z C hC
  intro l
  have hfl := (hf.clm_comp l).clm_comp Complex.ofRealCLM
  have hh := norm_mixed_jet_realPart_le p q p q le_rfl le_rfl _ hfl X z
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_re] using hh.trans (hb l)

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Fourier coefficients of the literal inverse are its finite-past ODE responses. -/

theorem unitProfileFourierCoeff_profileCellResponse (g : ℝ → ℝ)
    (f : ℝ → ℝ → ℂ) (a t κ C : ℝ) (hat : a ≤ t) (hκ : 0 < κ)
    (hi : IntegrableOn g (Icc a t)) (hg : ∀ s ∈ Icc a t, κ ≤ g s)
    (hC : 0 ≤ C) (hf : ∀ s ∈ Icc a t, Continuous (f s))
    (hp : ∀ s ∈ Icc a t, Function.Periodic (f s) 1)
    (hb : ∀ s ∈ Icc a t, ∀ x ∈ Icc (0 : ℝ) 1, ‖f s x‖ ≤ C) (n : ℤ) :
    unitProfileFourierCoeff (profileCellResponse g f a t) n = profileModeResponse g f a t n := by
  unfold profileCellResponse
  apply unitProfileFourierCoeff_profileFourierSeries
  have hs := profileFourier_jet_summable (profileModeResponse g f a t) 0 (C / κ)
    (fun m hm => profileModeResponse_frequency_weight_bound g f a t κ hat hκ hi hg
      0 C hC (fun s hs => by simpa using (contDiff_zero.mpr (hf s hs) : ContDiff ℝ (0 : WithTop ℕ∞) (f s))) hp
      (by simpa only [iteratedDeriv_zero] using hb) m hm)
  simpa only [pow_zero, one_mul] using hs

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Finite fast reserves make the zero-parameter source flux a classical C¹ field. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem sourceFlux_zero_component_contDiff (edge : ConstituentEdges D h) (η t : ℝ)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) (X : Vec 2)
    (hf : ContDiff ℝ (D : ℕ∞) (Φ X))
    (hc : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      ContDiff ℝ (D : ℕ∞) (γ.coeff α t X)) (q : Fin 2) (v : ι) :
    ContDiff ℝ 1 (fun z => sourceFlux edge η 0 t Φ q X z v) := by
  simp only [sourceFlux, dEpsWord_zero_parameter]
  apply ContDiff.sum
  intro u _
  apply ContDiff.sum
  intro d _
  have ht : ∀ γ ∈ edge v u d,
      ContDiff ℝ 1 (fun z => ∑ α : DerivativeWord2 (d.1 - 1),
        γ.coeff α t X z q • γ.map (orderedDerivative α (Φ X) z u)) := by
    intro γ hγ
    apply ContDiff.sum
    intro α _
    have hd : 2 ≤ d.1 ∧ d.1 ≤ D := Finset.mem_Icc.mp d.2
    have hw : ContDiff ℝ 1 (orderedDerivative α (Φ X)) :=
      orderedDerivative_contDiff α 1 (Φ X) (hf.of_le (by exact_mod_cast (show 1 + (d.1 - 1) ≤ D by omega)))
    have hcoeff : ContDiff ℝ 1 (fun z => γ.coeff α t X z q) :=
      (ContinuousLinearMap.proj q).contDiff.comp ((hc v u d γ hγ α).of_le (by exact_mod_cast (show 1 ≤ D by omega)))
    have hu : ContDiff ℝ 1 (fun z => orderedDerivative α (Φ X) z u) := by
      simpa only [Function.comp_def] using!
        (ContinuousLinearMap.proj u : (∀ i, h i) →L[ℝ] h u).contDiff.comp hw
    exact hcoeff.smul (γ.map.contDiff.comp hu)
  have hl : ∀ l : List (Constituent d.1 (h u) (h v)),
      (∀ γ ∈ l, ContDiff ℝ 1 (fun z => ∑ α : DerivativeWord2 (d.1 - 1),
        γ.coeff α t X z q • γ.map (orderedDerivative α (Φ X) z u))) →
      ContDiff ℝ 1 (fun z => (l.map fun γ => ∑ α : DerivativeWord2 (d.1 - 1),
        γ.coeff α t X z q • γ.map (orderedDerivative α (Φ X) z u)).sum) := by
    intro l
    induction l with
    | nil => intro _; simpa using (contDiff_const : ContDiff ℝ 1 (fun _ : Vec 2 => (0 : h v)))
    | cons γ l ih =>
      intro hh
      simpa only [List.map_cons, List.sum_cons] using
        (hh γ (List.mem_cons_self)).add (ih (fun γ' hγ' => hh γ' (List.mem_cons_of_mem _ hγ')))
  exact hl _ ht

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! The first literal cross operator is time measurable by separate slow and fast difference quotients. -/

section
variable {T E : Type*} [MeasurableSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem cellB1_parameter_measurable (η : ℝ) (τ : T → ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (Φ : T → Vec 2 → Vec 2 → E)
    (hm : ∀ X z, Measurable (fun t => Φ t X z))
    (hf : ∀ t, IsBoxSmooth 1 1 (Φ t))
    (hGm : ∀ X i j, Measurable (fun t => G (τ t) X i j))
    (hGs : ∀ t i j, ContDiff ℝ (1 : ℕ∞) (fun X => G (τ t) X i j))
    (hvm : ∀ z k, Measurable (fun t => v (τ t) z k)) (X z : Vec 2) :
    Measurable (fun t => cellB1 η G v (τ t) (Φ t) X z) := by
  have hs (j : Fin 2) (Y y : Vec 2) : Measurable (fun t => slowPartial j (Φ t) Y y) :=
    slowPartial_parameter_measurable Φ hm
      (fun t y => (boxSmooth_slow_contDiff (hf t) y).differentiable one_ne_zero) j Y y
  have hsb (j : Fin 2) (t : T) : IsBoxSmooth 0 1 (slowPartial j (Φ t)) :=
    isBoxSmooth_slow_direction (hf t) (basisVec j)
  have hfm (j : Fin 2) (Y y : Vec 2) : Measurable (fun t => fastPartial j (Φ t) Y y) :=
    fastPartial_parameter_measurable Φ hm
      (fun t Y => ((hf t).1 Y).differentiable one_ne_zero) j Y y
  have hfb (j : Fin 2) (t : T) : IsBoxSmooth 1 0 (fastPartial j (Φ t)) := (hf t).fastPartial j
  unfold cellB1
  apply Measurable.sub
  · apply Finset.measurable_sum
    intro k _
    exact (measurable_const.mul (hvm z k)).smul (hs k X z)
  · apply Measurable.const_smul
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    apply Measurable.add
    · exact (hGm X i j).smul (fastPartial_parameter_measurable _ (hs j)
        (fun t Y => ((hsb j t).1 Y).differentiable one_ne_zero) i X z)
    · exact slowPartial_parameter_measurable
        (fun t Y y => G (τ t) Y i j • fastPartial j (Φ t) Y y)
        (fun Y y => (hGm Y i j).smul (hfm j Y y))
        (fun t y => ((hGs t i j).differentiable one_ne_zero).smul
          ((boxSmooth_slow_contDiff (hfb j t) y).differentiable one_ne_zero)) i X z
end

/-! The second literal cross operator is time measurable by slow difference quotients. -/

section
variable {T E : Type*} [MeasurableSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem cellB2_parameter_measurable (η : ℝ) (τ : T → ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (Φ : T → Vec 2 → Vec 2 → E)
    (hm : ∀ X z, Measurable (fun t => Φ t X z))
    (hf : ∀ t, IsBoxSmooth 2 0 (Φ t))
    (hGm : ∀ X i j, Measurable (fun t => G (τ t) X i j))
    (hGs : ∀ t i j, ContDiff ℝ (1 : ℕ∞) (fun X => G (τ t) X i j)) (X z : Vec 2) :
    Measurable (fun t => cellB2 η G (τ t) (Φ t) X z) := by
  have hs (j : Fin 2) (Y y : Vec 2) : Measurable (fun t => slowPartial j (Φ t) Y y) :=
    slowPartial_parameter_measurable Φ hm
      (fun t y => (boxSmooth_slow_contDiff (hf t) y).differentiable (by norm_num)) j Y y
  have hb (j : Fin 2) (t : T) : IsBoxSmooth 1 0 (slowPartial j (Φ t)) :=
    isBoxSmooth_slow_direction (hf t) (basisVec j)
  unfold cellB2
  apply Measurable.neg
  apply Measurable.const_smul
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  exact slowPartial_parameter_measurable
    (fun t Y y => G (τ t) Y i j • slowPartial j (Φ t) Y y)
    (fun Y y => (hGm Y i j).smul (hs j Y y))
    (fun t y => ((hGs t i j).differentiable one_ne_zero).smul
      ((boxSmooth_slow_contDiff (hb j t) y).differentiable one_ne_zero)) i X z
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The literal uncentered source preserves scalar-dual measurability on the clamped window. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftA_normalized_clamped_dual_measurable_of_terms
    (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (a b : ℝ) (hab : a ≤ b)
    (v : ι) (l : h v →L[ℝ] ℝ) (A : Vec 2 →L[ℝ] ℝ) (lam : ℝ) (X z : Vec 2)
    (h₁ : Measurable (fun t => l ((Real.exp ((lam • A) X))⁻¹ • cellB1 Q.η Q.G Q.v
      (Set.projIcc a b hab t) (liftApply (n - 1) (Cc hh (n - 1)) f
        (Set.projIcc a b hab t)) X z v)))
    (h₂ : 2 ≤ n → Measurable (fun t => l ((Real.exp ((lam • A) X))⁻¹ • cellB2 Q.η Q.G
      (Set.projIcc a b hab t) (liftApply (n - 2) (Cc hh (n - 2)) f
        (Set.projIcc a b hab t)) X z v)))
    (hS : hh ≠ 0 → ∀ j ≤ min D n, Measurable (fun t => l ((Real.exp ((lam • A) X))⁻¹ •
      sourceCoeff Q.edge Q.η j (Set.projIcc a b hab t)
        (liftApply (n - j) (Cc (hh - 1) (n - j)) f (Set.projIcc a b hab t)) X z v))) :
    Measurable (fun t => l ((Real.exp ((lam • A) X))⁻¹ •
      liftA Q Cc f hh n (Set.projIcc a b hab t) X z v)) := by
  simp_rw [liftA_normalized_component_expansion]
  by_cases hn : 2 ≤ n <;> by_cases hh0 : hh = 0
  · simp only [ite_eq_left hn, ite_eq_left hh0, map_add, sub_zero]
    exact h₁.add (h₂ hn)
  · simp only [ite_eq_left hn, ite_eq_right hh0, map_add, map_sub, map_sum]
    exact (h₁.add (h₂ hn)).sub (Finset.measurable_sum _ fun j hj =>
      hS hh0 j (by have he := Finset.mem_range.mp hj; omega))
  · simpa only [ite_eq_right hn, ite_eq_left hh0, map_add, map_sub, map_zero,
      add_zero, sub_zero] using h₁
  · simp only [ite_eq_right hn, ite_eq_right hh0, map_sub,
      add_zero, map_sum]
    exact h₁.sub (Finset.measurable_sum _ fun j hj =>
      hS hh0 j (by have he := Finset.mem_range.mp hj; omega))

end AVRegularity.CycleComparison.Lift
end
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Basic support identities for the finite lift coefficient arrays. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

 theorem liftApply_of_coeff_zero (n : ℕ) (c : LiftCoeff ι h)
    (hc : ∀ m α t X z v u, c m α t X z v u = 0)
    (a : ℝ → Vec 2 → ∀ i, h i) : liftApply n c a = 0 := by
  funext t X z v
  simp [liftApply, hc]

 theorem liftApply_zero (n : ℕ) (c : LiftCoeff ι h) :
    liftApply n c (0 : ℝ → Vec 2 → ∀ i, h i) = 0 := by
  funext t X z v
  simp [liftApply, AVRegularity.CycleComparison.Lift.orderedDerivative_zero]

 theorem liftApply_const (n : ℕ) (c : LiftCoeff ι h) (c0 : ∀ i, h i)
    (t : ℝ) (X z : Vec 2) (v : ι) :
    liftApply n c (fun _ _ => c0) t X z v =
      ∑ α : DerivativeWord2 0, ∑ u, c 0 α t X z v u (c0 u) := by
  unfold liftApply
  rw [Finset.sum_eq_single 0]
  · simp [orderedDerivative]
  · intro m hm hm0
    have hpos : 1 ≤ m := by omega
    have hd (α : DerivativeWord2 m) : orderedDerivative α (fun _ : Vec 2 => c0) = 0 :=
      orderedDerivative_const α c0 hpos
    simp [hd]
  · simp

variable [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}
  (Q : LiftOperatorData ι h D) (sX sZ : ℕ) (t₀ t₁ : ℝ) (N H : ℕ)
  (Cc : ℕ → ℕ → LiftCoeff ι h)
  (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc)

include hseq in
theorem liftApply_above_cutoff (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : N < n)
    (a : ℝ → Vec 2 → ∀ i, h i) : liftApply n (Cc hh n) a = 0 :=
  liftApply_of_coeff_zero n (Cc hh n) (hseq.2.2.1 hh hhh n hn) a

include hseq in
theorem liftApply_positive_grade_zero_degree (hh : ℕ) (hhpos : 1 ≤ hh) (hhh : hh ≤ H)
    (a : ℝ → Vec 2 → ∀ i, h i) : liftApply 0 (Cc hh 0) a = 0 :=
  liftApply_of_coeff_zero 0 (Cc hh 0) (hseq.2.1 hh hhpos hhh) a

include hseq in
theorem liftApply_const_degree_zero (c0 : ∀ i, h i) (hh : ℕ) (hhh : hh ≤ H)
    (t : ℝ) (ht : t ∈ Set.Icc t₀ t₁) :
    liftApply 0 (Cc hh 0) (fun _ _ => c0) t = fun _ _ => if hh = 0 then c0 else 0 := by
  by_cases hh0 : hh = 0
  · subst hh
    funext X z
    simpa only [eq_self, ite_true] using hseq.1 (fun _ => c0) contDiff_const t ht X z
  · have he := liftApply_positive_grade_zero_degree Q sX sZ t₀ t₁ N H Cc hseq hh (by omega) hhh
      (fun _ _ => c0)
    simpa only [ite_eq_right hh0] using! congrFun he t
end

/-! Positive truncation preserves tested actions when the omitted entries vanish. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

omit [Fintype ι] in
theorem positiveLiftCoefficient_eq_at_time (R : ℕ) (c : LiftCoeff ι h) (t : ℝ)
    (hz : ∀ m, ¬(1 ≤ m ∧ m ≤ R) → ∀ (α : DerivativeWord2 m) X z v u,
      c m α t X z v u = 0)
    (m : ℕ) (α : DerivativeWord2 m) (X z : Vec 2) (v u : ι) :
    positiveLiftCoefficient R c m α t X z v u = c m α t X z v u := by
  by_cases hm : 1 ≤ m ∧ m ≤ R
  · exact ite_eq_left hm
  · exact (ite_eq_right hm).trans (hz m hm α X z v u).symm
end

end AVRegularity.CycleComparison.Lift
end
end
