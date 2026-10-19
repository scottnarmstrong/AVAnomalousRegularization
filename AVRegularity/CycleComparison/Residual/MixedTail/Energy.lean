-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Residual.TailJets.Main
public import AVRegularity.CycleComparison.Residual.FastJets.Sampling
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep
public import Mathlib.Order.CompletePartialOrder
import AVRegularity.CycleComparison.Residual.Antidivergence.Main

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.MixedTail

/-! Fast derivatives of a lift action: since the coarse field is fast independent, the fast word
derivative of `liftApply M c a τ X y v` in `y` falls on the coefficients, so it is the lift action of
the fast-differentiated coefficient array `fastCoeff δ c`. The tail jet bounds of `TailJets` then
apply to `fastCoeff δ c`, with the mixed cell jets `mixedCellJet` in place of `cellL2Jet`. -/

section
/-- The fast word derivative `∂_z^δ` of the entries of a coefficient array. -/
def fastCoeff {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {b : ℕ} (δ : DerivativeWord2 b) (c : LiftCoeff ι h) :
    LiftCoeff ι h :=
  fun m α t X z v u => orderedDerivative δ (fun z' => c m α t X z' v u) z

/-- Uniform-time cell `L²` norm of the slow `i`-jet of the fast word `δ` of `f`. -/
def mixedCellJet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (I : Set ℝ) (i : ℕ)
    {b : ℕ} (δ : DerivativeWord2 b) (f : ℝ → Vec 2 → Vec 2 → E) : ℝ≥0∞ :=
  ⨆ t ∈ I, ⨆ X : Vec 2,
    eLpNorm (fun z => iteratedFDeriv ℝ i (fun X' => orderedDerivative δ (f t X') z) X) 2
      (volume.restrict AVenhance.unitCube)

/-- The weighted block norm of the mixed cell jets of a coefficient array. -/
def schurMixedJet {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {κ : Type*} [Fintype κ] (π : ι → ℝ) (I : Set ℝ) (i : ℕ)
    {b : ℕ} (δ : DerivativeWord2 b)
    (c : κ → ℝ → Vec 2 → Vec 2 → ∀ v u : ι, h u →L[ℝ] h v) : ℝ≥0∞ :=
  schurSums π fun v u => ∑ a : κ, mixedCellJet I i δ (fun t X z => c a t X z v u)

theorem mixedCellJet_eq_cellL2Jet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Set ℝ) (i : ℕ) {b : ℕ} (δ : DerivativeWord2 b) (f : ℝ → Vec 2 → Vec 2 → E) :
    mixedCellJet I i δ f = cellL2Jet I i (fun t X z => orderedDerivative δ (f t X) z) := rfl

theorem orderedDerivative_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {κ : Type*}
    (s : Finset κ) {j : ℕ} (β : DerivativeWord2 j) {g : κ → Vec 2 → F}
    (hg : ∀ k ∈ s, ContDiff ℝ (j : ℕ∞) (g k)) :
    orderedDerivative β (fun x => ∑ k ∈ s, g k x) = fun x => ∑ k ∈ s, orderedDerivative β (g k) x := by
  have hsum : ContDiff ℝ (j : ℕ∞) (fun x => ∑ k ∈ s, g k x) := ContDiff.sum hg
  rw [orderedDerivative_eq_iteratedFDeriv β hsum]
  funext x
  have h1 := iteratedFDeriv_sum (𝕜 := ℝ) (u := s) (f := g) (i := j) hg
  have h2 := congrFun h1 x
  simp only [Finset.sum_apply] at h2
  rw [h2]
  simp only [sum_apply]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [orderedDerivative_eq_iteratedFDeriv β (hg k hk)]

section Lift

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- The fast word derivative of a lift action falls on the coefficients. -/
theorem liftApply_fastCoeff {b : ℕ} (δ : DerivativeWord2 b) (M : ℕ) (c : LiftCoeff ι h)
    (a : ℝ → Vec 2 → ∀ i, h i) (τ : ℝ) (X' : Vec 2)
    (hc : ∀ m α v u, ContDiff ℝ (b : ℕ∞) (fun y => c m α τ X' y v u)) (y : Vec 2) (v : ι) :
    liftApply M (fastCoeff δ c) a τ X' y v =
      orderedDerivative δ (fun y' => liftApply M c a τ X' y' v) y := by
  have hterm : ∀ m (α : DerivativeWord2 m) (u : ι),
      ContDiff ℝ (b : ℕ∞) (fun y' => c m α τ X' y' v u (orderedDerivative α (a τ) X' u)) :=
    fun m α u => (ContinuousLinearMap.apply ℝ (h v) (orderedDerivative α (a τ) X' u)).contDiff.comp
      (hc m α v u)
  have hu : ∀ m (α : DerivativeWord2 m), ContDiff ℝ (b : ℕ∞)
      (fun y' => ∑ u, c m α τ X' y' v u (orderedDerivative α (a τ) X' u)) := fun m α =>
    ContDiff.sum fun u _ => hterm m α u
  have hα : ∀ m, ContDiff ℝ (b : ℕ∞) (fun y' => ∑ α : DerivativeWord2 m, ∑ u,
      c m α τ X' y' v u (orderedDerivative α (a τ) X' u)) := fun m =>
    ContDiff.sum fun α _ => hu m α
  have e1 : ∀ m (α : DerivativeWord2 m) (u : ι),
      orderedDerivative δ (fun y' => c m α τ X' y' v u (orderedDerivative α (a τ) X' u)) y =
        orderedDerivative δ (fun y' => c m α τ X' y' v u) y (orderedDerivative α (a τ) X' u) := by
    intro m α u
    exact congrFun (orderedDerivative_clm_comp
      (ContinuousLinearMap.apply ℝ (h v) (orderedDerivative α (a τ) X' u)) δ (hc m α v u)) y
  have e2 : ∀ m (α : DerivativeWord2 m),
      orderedDerivative δ (fun y' => ∑ u, c m α τ X' y' v u (orderedDerivative α (a τ) X' u)) y =
        ∑ u, orderedDerivative δ (fun y' => c m α τ X' y' v u) y (orderedDerivative α (a τ) X' u) := by
    intro m α
    rw [congrFun (orderedDerivative_sum Finset.univ δ fun u _ => hterm m α u) y]
    exact Finset.sum_congr rfl fun u _ => e1 m α u
  have e3 : ∀ m, orderedDerivative δ (fun y' => ∑ α : DerivativeWord2 m, ∑ u,
      c m α τ X' y' v u (orderedDerivative α (a τ) X' u)) y =
      ∑ α : DerivativeWord2 m, ∑ u, orderedDerivative δ (fun y' => c m α τ X' y' v u) y
        (orderedDerivative α (a τ) X' u) := by
    intro m
    rw [congrFun (orderedDerivative_sum Finset.univ δ fun α _ => hu m α) y]
    exact Finset.sum_congr rfl fun α _ => e2 m α
  have hfun : (fun y' => liftApply M c a τ X' y' v) = fun y' => ∑ m ∈ Finset.range (M + 1),
      ∑ α : DerivativeWord2 m, ∑ u, c m α τ X' y' v u (orderedDerivative α (a τ) X' u) := rfl
  rw [hfun, congrFun (orderedDerivative_sum (Finset.range (M + 1)) δ fun m _ => hα m) y]
  change ∑ m ∈ Finset.range (M + 1), ∑ α : DerivativeWord2 m, ∑ u,
    orderedDerivative δ (fun y' => c m α τ X' y' v u) y (orderedDerivative α (a τ) X' u) = _
  exact Finset.sum_congr rfl fun m _ => (e3 m).symm

end Lift

section Inner

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]

/-- **Mixed analogue of T2**: the fast word `δ` of the coefficients enters through
`mixedCellJet`. -/
theorem sum_mass_lintegral_iteratedFDeriv_fast_le
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (I : Set ℝ) (M p : ℕ) {b : ℕ} (δ : DerivativeWord2 b)
    (c : LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) {τ : ℝ} (hτ : τ ∈ I)
    (hc : ∀ m α v u, IsBoxSmooth p b (fun X y => c m α τ X y v u))
    (ha : ContDiff ℝ ((p + M : ℕ) : ℕ∞) (a τ)) (X : Vec 2) :
    ∑ v, ENNReal.ofReal (π v)⁻¹ * ∫⁻ y in AVenhance.unitCube,
        ‖iteratedFDeriv ℝ p (fun X' =>
          orderedDerivative δ (fun y' => liftApply M c a τ X' y' v) y) X‖ₑ ^ 2
      ≤ ENNReal.ofReal (tailJetConst M p) * ∑ m ∈ Finset.range (M + 1),
          ∑ i ∈ Finset.range (p + 1),
          schurMixedJet π I i δ (c m) ^ 2 *
            ∑ u, ENNReal.ofReal (π u)⁻¹ *
              ‖iteratedFDeriv ℝ (p - i + m) (fun X' => a τ X' u) X‖ₑ ^ 2 := by
  have hc' : ∀ m α v u, IsBoxSmooth p 0 (fun X y => fastCoeff δ c m α τ X y v u) := fun m α v u =>
    FastJets.isBoxSmooth_fastL (sX := p) (sZ := 0) (List.ofFn δ) (F := fun X y => c m α τ X y v u)
      (by simpa using hc m α v u)
  have key := sum_mass_lintegral_iteratedFDeriv_liftApply_le π hπ I M p (fastCoeff δ c) a
    hτ hc' ha X
  have hrew : ∀ X' y v, liftApply M (fastCoeff δ c) a τ X' y v =
      orderedDerivative δ (fun y' => liftApply M c a τ X' y' v) y := fun X' y v =>
    liftApply_fastCoeff δ M c a τ X' (fun m α v u => ((hc m α v u).1 X')) y v
  simp only [hrew] at key
  exact key

end Inner
end

/-! Bridge from the mixed cell jets to the energy jets of `fieldEnergyNorm`: the slow `i`-jet of
a fast word `δ` of length `b` is bounded in the cell `L²` norm, by Schwarz interchange of `∂_z^δ`
and the slow derivatives, by `2^i` times the `b`-th fast jet of the slow `i`-jet, which is part of
the sup-in-time `L²` norm in `fieldEnergyNorm`. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A fast word commutes with a slow word. -/
theorem fastL_slowL_comm (γ : List (Fin 2)) :
    ∀ (δ : List (Fin 2)) {F : Vec 2 → Vec 2 → E}, IsBoxSmooth γ.length δ.length F →
      FastJets.fastL δ (FastJets.slowL γ F) = FastJets.slowL γ (FastJets.fastL δ F) := by
  intro δ
  induction δ with
  | nil => intro F _; rfl
  | cons i δ ih =>
    intro F hF
    have hF1 : IsBoxSmooth γ.length 1 F := hF.mono le_rfl (by simp)
    have hF' : IsBoxSmooth γ.length δ.length (fastPartial i F) := by
      have := hF.fastPartial (sX := γ.length) (sZ := δ.length) i
      exact this
    rw [FastJets.fastL_cons, FastJets.fastPartial_slowL i γ hF1, ih hF', FastJets.fastL_cons]

/-- The slow `i`-jet is `C^b` in the fast variable. -/
theorem contDiff_slowJet {i b : ℕ} {F : Vec 2 → Vec 2 → E} (hF : IsBoxSmooth (i + b) (i + b) F)
    (X : Vec 2) :
    ContDiff ℝ (b : ℕ∞) (fun z' => iteratedFDeriv ℝ i (fun X' => F X' z') X) := by
  have hU : ContDiff ℝ ((i + b : ℕ) : ℕ∞) (Function.uncurry F) :=
    hF.contDiff_uncurry (m := i + b) le_rfl le_rfl
  let L := ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ)
    (E := fun _ : Fin i => Vec 2) (E₁ := fun _ : Fin i => Vec 2 × Vec 2) (F := E)
    (fun _ => ContinuousLinearMap.inl ℝ (Vec 2) (Vec 2))
  have hrel : ∀ z', iteratedFDeriv ℝ i (fun X' => F X' z') X =
      L (iteratedFDeriv ℝ i (Function.uncurry F) (X, z')) := by
    intro z'
    have e : (fun X' => F X' z') = (fun p => Function.uncurry F (p + ((0 : Vec 2), z'))) ∘
        ⇑(ContinuousLinearMap.inl ℝ (Vec 2) (Vec 2)) := by
      funext X'; simp [Function.uncurry]
    have hc : ContDiff ℝ ((i + b : ℕ) : ℕ∞) (fun p : Vec 2 × Vec 2 =>
        Function.uncurry F (p + ((0 : Vec 2), z'))) :=
      hU.comp (contDiff_id.add contDiff_const)
    rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hc X (by exact_mod_cast Nat.le_add_right i b),
      iteratedFDeriv_comp_add_right]
    simp [L]
  simp_rw [hrel]
  exact L.contDiff.comp ((hU.iteratedFDeriv_right (m := (b : ℕ∞)) (by norm_cast; omega)).comp
    (contDiff_const.prodMk contDiff_id))

theorem schurSums_const_mul_le {ι : Type*} [Fintype ι] (π : ι → ℝ) (C : ℝ≥0∞)
    (K : ι → ι → ℝ≥0∞) : schurSums π (fun v u => C * K v u) ≤ C * schurSums π K := by
  unfold schurSums
  refine max_le ?_ ?_
  · refine iSup_le fun v => ?_
    have : ∑ u, ENNReal.ofReal (Real.sqrt (π u / π v)) * (C * K v u) =
        C * ∑ u, ENNReal.ofReal (Real.sqrt (π u / π v)) * K v u := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by ring
    rw [this]
    exact mul_le_mul_right (le_max_of_le_left (le_iSup (fun v => ∑ u,
      ENNReal.ofReal (Real.sqrt (π u / π v)) * K v u) v)) C
  · refine iSup_le fun u => ?_
    have : ∑ v, ENNReal.ofReal (Real.sqrt (π u / π v)) * (C * K v u) =
        C * ∑ v, ENNReal.ofReal (Real.sqrt (π u / π v)) * K v u := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
    rw [this]
    exact mul_le_mul_right (le_max_of_le_right (le_iSup (fun u => ∑ v,
      ENNReal.ofReal (Real.sqrt (π u / π v)) * K v u) u)) C
end

end AVRegularity.MixedTail
end
