-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.IndependentFreshCoarseAppendReferenceGeometry
import AVRegularity.Construction.EntryScales.TerminalCore
import Mathlib.Algebra.Order.Star.Real

section
section
/-! Ordered forcing production preserves each matrix grade over all independent parameters. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem independentLiftA_uniform_production (H : ℕ)
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (d : Finset.Icc 2 D), Constituent d.val ℝ ℝ →
      DerivativeWord2 (d.val - 1) → ℝ → Vec 2 → P → Vec 2)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → P → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (F : ℕ → ℕ → ℝ → Vec 2 → P → ι → ℝ) (hh n : ℕ) (out inp : ι)
    (QG : ∀ i j, IndependentParameterSourceReserve (H + 1) (fun t _ Y => G t Y i j))
    (Qv : ∀ i, IndependentParameterSourceReserve H (fun t z (_ : P) => v t z i))
    (Q1 : IndependentParameterSourceReserve (H + 2) (fun t z Y => F hh (n - 1) t z Y out))
    (Q2 : 2 ≤ n → IndependentParameterSourceReserve (H + 2) (fun t z Y => F hh (n - 2) t z Y out))
    (Qprev : hh ≠ 0 → ∀ j ∈ Finset.range (min D n + 1), ∀ u,
      IndependentParameterSourceReserve (H + 1 + D) (fun t z Y => F (hh - 1) (n - j) t z Y u))
    (Qa : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      IndependentParameterSourceReserve (H + 1) (a v u d γ α))
    (M : ι → ι → ℝ) (hM : ∀ v u, 0 ≤ M v u) (count : ℕ)
    (BG BV BE BF : ℝ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hBF : 0 ≤ BF)
    (hG : ∀ i j r, r ≤ H + 1 → (QG i j).budget r ≤ BG)
    (hv : ∀ i r, r ≤ H → (Qv i).budget r ≤ BV)
    (h1 : ∀ r ≤ H + 2, Q1.budget r ≤ finiteMatrixPower M hh out inp * BF)
    (h2 : ∀ hn r, r ≤ H + 2 → (Q2 hn).budget r ≤ finiteMatrixPower M hh out inp * BF)
    (hp : ∀ hhh j hj u r, r ≤ H + 1 + D →
      (Qprev hhh j hj u).budget r ≤ finiteMatrixPower M (hh - 1) u inp * BF)
    (he : ∀ u d γ hγ α r, r ≤ H + 1 → (Qa out u d γ hγ α).budget r ≤ M out u * BE)
    (hmap : ∀ u d γ, γ ∈ edge out u d → ‖γ.map‖ ≤ 1)
    (hlen : ∀ u d, (edge out u d).length ≤ count) :
    ∃ Q : IndependentParameterSourceReserve H (independentLiftASource edge a L A η G v F hh n out),
      ∀ r ≤ H, Q.budget r ≤ finiteMatrixPower M hh out inp *
        (normalizedCellB1UniformBudget H A η BG BV BF + normalizedCellB2UniformBudget H A η BG BF +
          (min D n + 1) * normalizedSourceArrayMatrixBudget H D count A η BE BF) := by
  let θ := finiteMatrixPower M hh out inp
  have hθ : 0 ≤ θ := finiteMatrixPower_nonneg M hM hh out inp
  let BS := normalizedSourceArrayMatrixBudget H D count A η BE BF
  have hBS : 0 ≤ BS := normalizedSourceArrayMatrixBudget_nonneg _ _ _ _ _ _ _ hBE hBF
  have hs (hhh : hh ≠ 0) j (hj : j ∈ Finset.range (min D n + 1)) :
      ∃ Q : IndependentParameterSourceReserve H
        (independentSourceComponentArray edge a L A η (F (hh - 1) (n - j)) j out),
        ∀ r ≤ H, Q.budget r ≤ θ * BS := by
    obtain ⟨Q, hQ⟩ := independentSourceArray_matrix_reserve H edge a L hL η A _ M hM
      (hh - 1) count out inp (Qprev hhh j hj) (Qa out) BE BF hBE hBF
      (hp hhh j hj) he hmap hlen j
    refine ⟨Q, ?_⟩
    intro r hr
    simpa only [show 1 + (hh - 1) = hh by omega] using hQ r hr
  choose QS hQS using hs
  let B2 := fun t z Y => if 2 ≤ n then independentNormalizedCellB2Source L A η G
    (fun t z Y => F hh (n - 2) t z Y out) t z Y else 0
  have hb2 : ∃ Q : IndependentParameterSourceReserve H B2, ∀ r ≤ H,
      Q.budget r ≤ θ * normalizedCellB2UniformBudget H A η BG BF := by
    by_cases hn : 2 ≤ n
    · refine ⟨(independentNormalizedCellB2SourceReserve H L hL A η G _ QG (Q2 hn)).congrSource
        (by funext t z Y; exact (ite_eq_left hn).symm), ?_⟩
      intro r hr
      rw [IndependentParameterSourceReserve.congrSource_budget]
      exact independentNormalizedCellB2SourceReserve_uniform_budget H L hL A η G _ QG (Q2 hn)
        θ BG BF hθ hBG hBF hG (h2 hn) r hr
    · refine ⟨(IndependentParameterSourceReserve.zero H).congrSource
        (by funext t z Y; exact (ite_eq_right hn).symm), ?_⟩
      intro r _
      rw [IndependentParameterSourceReserve.congrSource_budget]
      exact mul_nonneg hθ (normalizedCellB2UniformBudget_nonneg H A η BG BF hBG hBF)
  obtain ⟨QB2, hQB2⟩ := hb2
  let S := fun t z Y => if hh = 0 then 0 else ∑ j ∈ Finset.range (min D n + 1),
    independentSourceComponentArray edge a L A η (F (hh - 1) (n - j)) j out t z Y
  have hs' : ∃ Q : IndependentParameterSourceReserve H S, ∀ r ≤ H,
      Q.budget r ≤ θ * ((min D n + 1) * BS) := by
    by_cases hhh : hh = 0
    · refine ⟨(IndependentParameterSourceReserve.zero H).congrSource
        (by funext t z Y; exact (ite_eq_left hhh).symm), ?_⟩
      intro r _
      rw [IndependentParameterSourceReserve.congrSource_budget]
      exact mul_nonneg hθ (mul_nonneg (by positivity) hBS)
    · refine ⟨(IndependentParameterSourceReserve.finsetSum _ H _ (QS hhh)).congrSource
        (by funext t z Y; exact (ite_eq_right hhh).symm), ?_⟩
      intro r hr
      rw [IndependentParameterSourceReserve.congrSource_budget, IndependentParameterSourceReserve.finsetSum_budget]
      apply (Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hQS hhh j.val j.property r hr)).trans_eq
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring
  obtain ⟨QR, hQR⟩ := hs'
  let QB1 := independentNormalizedCellB1SourceReserve H L hL A η G v _ QG Qv Q1
  let T : ℝ →L[ℝ] ℝ := -ContinuousLinearMap.id ℝ ℝ
  refine ⟨((QB1.add QB2).add (QR.map T)).congrSource
    (by funext t z Y; simp only [independentLiftASource, T, neg_apply,
      ContinuousLinearMap.id_apply, sub_eq_add_neg]; rfl), ?_⟩
  intro r hr
  rw [IndependentParameterSourceReserve.congrSource_budget]
  change QB1.budget r + QB2.budget r + ‖T‖ * QR.budget r ≤ _
  have ht : ‖T‖ = 1 := by simp only [T, norm_neg, ContinuousLinearMap.norm_id]
  rw [ht, one_mul]
  have hb1 := independentNormalizedCellB1SourceReserve_uniform_budget H L hL A η G v _ QG Qv Q1
    θ BG BV BF hθ hBG hBV hBF hG hv h1 r hr
  exact (add_le_add (add_le_add hb1 (hQB2 r hr)) (hQR r hr)).trans_eq (by ring)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Full independent coarse append jets have the primitive shear price at every finite order. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem independentFreshCoarseAppendPacking_positive_jets (r : ℕ) (D : OCData)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (m : ℕ) (parentSlot slot : ℤ)
    (hp : Odd parentSlot) (θ t : ℝ) (hθ : |θ| ≤ 1)
    (hsmall : |D.slotAnchor (m + 1) slot - t| * ocA D.α D.q D.Λ m ≤ 1)
    (K n : ℕ) (hn : 1 ≤ n) (hnK : n ≤ K) (X : Vec 2 × Vec (2 + 4 * r)) :
    ‖iteratedFDeriv ℝ n (independentFreshCoarseAppendPacking r D m parentSlot slot θ t) X‖ ≤
      1 + (2 * Real.pi) ^ (K + 1) := by
  let F : (Vec 2 × Vec (2 + 4 * r)) →L[ℝ] Vec 2 := ContinuousLinearMap.fst ℝ _ _
  let P := (independentStoredParameterProjection (4 * r)).comp
    (ContinuousLinearMap.snd ℝ (Vec 2) (Vec (2 + 4 * r)))
  let S := (independentIntrinsicSlowProjection (4 * r)).comp
    (ContinuousLinearMap.snd ℝ (Vec 2) (Vec (2 + 4 * r)))
  have hF : ‖F‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro Y
    change ‖Y.1‖ ≤ 1 * ‖Y‖
    simpa only [one_mul] using norm_fst_le Y
  have hP : ‖P‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro Y
    rw [one_mul]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg Y)).2
    intro i
    exact (norm_le_pi_norm Y.2 (i.natAdd 2)).trans (norm_snd_le Y)
  have hS : ‖S‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro Y
    rw [one_mul]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg Y)).2
    intro i
    exact (norm_le_pi_norm Y.2 (i.castAdd (4 * r))).trans (norm_snd_le Y)
  let δ := D.relDisp m parentSlot (D.slotAnchor (m + 1) slot) t
  have hδ : ContDiff ℝ (⊤ : ℕ∞) δ := relDisp_spatial_smooth D m parentSlot _ t
  have hb : ‖iteratedFDeriv ℝ n (δ ∘ F) X‖ ≤ (2 * Real.pi) ^ (K + 1) := by
    have hh := finite_affine_derivative_norm_le δ n (hδ.of_le (by simp)) F hF 0 X
    simp only [add_zero] at hh
    apply hh.trans
    apply (weak_relative_displacement_menu_jet_bound D hΛ hζ m parentSlot hp
      (D.slotAnchor (m + 1) slot) t K n hnK (F X)).trans
    calc
      _ = (2 * Real.pi) ^ (K + 1) *
        (|D.slotAnchor (m + 1) slot - t| * ocA D.α D.q D.Λ m) := by ring
      _ ≤ (2 * Real.pi) ^ (K + 1) * 1 :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = _ := mul_one _
  exact coarse_append_positive_jet_bound r n hn P S F hP hS hF (δ ∘ F)
    ((hδ.comp F.contDiff).of_le (by simp)) θ _ hθ X hb

end AVRegularity.EntryWeakProofs
end
end

section
/-! Full incoming reserves normalize to genuine edge reserves with their recorded weight unchanged. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def actualWeakIncomingSourceReserve (H : ℕ)
    (D : OCData) (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (m birth : ℕ) (hm : D.term ≤ m) (hb : m ≤ birth)
    (nγ d : ℕ) (hnγ : 2 ≤ nγ) (hd : 2 ≤ d)
    (f : ℝ → Vec 2 → P → E) (Q : IndependentParameterSourceReserve H f)
    (θ B : ℝ) (hθ : 0 ≤ θ) (hB : 0 ≤ B)
    (hQ : ∀ k ≤ H, Q.budget k ≤
      θ * (D.κ D.term * D.eps birth ^ (nγ - 2) * D.eps m ^ ((d : ℝ) - (nγ : ℝ))) * B) :
    IndependentParameterSourceReserve H
      (fun t z Y => (D.kap m * D.eps m ^ (d - 2))⁻¹ • f t z Y) where
  regular t := (Q.regular t).const_smul _
  periodic t Y k z := congrArg (fun v : E => (D.kap m * D.eps m ^ (d - 2))⁻¹ • v)
    (Q.periodic t Y k z)
  measurable Y := measurable_const.smul (Q.measurable Y)
  budget _ := θ * B
  budget_nonneg _ := mul_nonneg hθ hB
  derivative_bound k hk t X := by
    have hf : ContDiff ℝ (k : ℕ∞) (fun Z : Vec 2 × P => f t Z.1 Z.2) :=
      (Q.regular t).of_le (by exact_mod_cast hk)
    have hj (Z : Vec 2 × P) :
        (1 : ℝ) ^ k * ‖iteratedFDeriv ℝ k (fun U : Vec 2 × P => f t U.1 U.2) Z‖ ≤
          θ * (D.κ D.term * D.eps birth ^ (nγ - 2) * D.eps m ^ ((d : ℝ) - (nγ : ℝ))) * B := by
      simpa only [one_pow, one_mul] using (Q.derivative_bound k hk t Z).trans (hQ k hk)
    simpa only [one_pow, one_mul] using actual_weak_incoming_normalized_jet_bound
      D hq hΛ hζ hband m birth hm hb nγ d k hnγ hd (fun Z : Vec 2 × P => f t Z.1 Z.2)
      hf 1 θ B hθ hB hj X

end AVRegularity.EntryWeakProofs
end
end

section
/-! The literal centered shear displacement used inside the parent difference. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def independentCenteredChildDisplacement (D : OCData) (m : ℕ) (slot : ℤ) (u r : ℝ)
    (Fi Fa : P × Vec 2 → Vec 2) (θ : ℝ) (Y : P × (Vec 2 × (Vec 2 × Vec 2))) : Vec 2 :=
  weakCenteredShearTransition D m slot u r
    (Y.2.2.1, independentCenteredChildReturn Fi Fa θ Y)

theorem independentCenteredChildDisplacement_contDiff (D : OCData) (m : ℕ) (slot : ℤ) (u r : ℝ)
    (Fi Fa : P × Vec 2 → Vec 2) (hFi : ContDiff ℝ (⊤ : ℕ∞) Fi)
    (hFa : ContDiff ℝ (⊤ : ℕ∞) Fa) (θ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (independentCenteredChildDisplacement D m slot u r Fi Fa θ) :=
  (weakCenteredShearTransition_contDiff D m slot u r).comp
    ((centeredChildPhaseProjection (P := P) (V := Vec 2)).contDiff.prodMk
      (independentCenteredChildReturn_contDiff Fi Fa hFi hFa θ))

end AVRegularity.EntryWeakProofs
end
end

section
/-! The parent-chart base uses the independent center and the small relative shear. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def independentCenteredChildBase (D : OCData) (m : ℕ) (slot : ℤ) (u r θ : ℝ)
    (Y : P × (Vec 2 × (Vec 2 × Vec 2))) : Vec 2 :=
  Y.2.1 + θ • D.relDisp m slot u r Y.2.2.1

theorem independentCenteredChildBase_contDiff (D : OCData) (m : ℕ) (slot : ℤ) (u r θ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (independentCenteredChildBase (P := P) D m slot u r θ) :=
  (centeredChildCenterProjection (P := P) (V := Vec 2)).contDiff.add
    (((relDisp_spatial_smooth D m slot u r).comp
      (centeredChildPhaseProjection (P := P) (V := Vec 2)).contDiff).const_smul θ)

theorem independentCenteredChildBase_positive_jet_bound (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (m : ℕ) (slot : ℤ) (hp : Odd slot) (u r θ : ℝ)
    (hsmall : |u - r| * ocA D.α D.q D.Λ m ≤ 1) (hθ : |θ| ≤ 1)
    (K n : ℕ) (hn : 1 ≤ n) (hnK : n ≤ K) (Y : P × (Vec 2 × (Vec 2 × Vec 2))) :
    ‖iteratedFDeriv ℝ n (independentCenteredChildBase D m slot u r θ) Y‖ ≤
      1 + (2 * Real.pi) ^ (K + 1) := by
  let Q := centeredChildPhaseProjection (P := P) (V := Vec 2)
  let A := centeredChildCenterProjection (P := P) (V := Vec 2)
  let f := D.relDisp m slot u r
  have hf : ContDiff ℝ (n : ℕ∞) f := (relDisp_spatial_smooth D m slot u r).of_le (by simp)
  have hg : ContDiff ℝ (n : ℕ∞) (f ∘ Q) := hf.comp Q.contDiff
  have hA : ContDiff ℝ (n : ℕ∞) A := A.contDiff
  have hbδ : ‖iteratedFDeriv ℝ n (f ∘ Q) Y‖ ≤ (2 * Real.pi) ^ (K + 1) := by
    have hh := finite_affine_derivative_norm_le f n hf Q centeredChildPhaseProjection_norm_le 0 Y
    simp only [add_zero] at hh
    have hd := weak_relative_displacement_menu_jet_bound D hΛ hζ m slot hp u r K n hnK (Q Y)
    have he : |u - r| * (2 * Real.pi) ^ (K + 1) * ocA D.α D.q D.Λ m =
        (|u - r| * ocA D.α D.q D.Λ m) * (2 * Real.pi) ^ (K + 1) := by ring
    rw [he] at hd
    exact hh.trans (hd.trans ((mul_le_mul_of_nonneg_right hsmall (by positivity)).trans_eq (one_mul _)))
  have he : independentCenteredChildBase (P := P) D m slot u r θ = A + θ • (f ∘ Q) := rfl
  have hscaledReg : ContDiff ℝ (n : ℕ∞) (θ • (f ∘ Q)) := hg.const_smul θ
  rw [he, iteratedFDeriv_add_apply hA.contDiffAt hscaledReg.contDiffAt,
    iteratedFDeriv_const_smul_apply (f := f ∘ Q) (x := Y) (a := θ) hg.contDiffAt]
  have hscaled : ‖θ • iteratedFDeriv ℝ n (f ∘ Q) Y‖ ≤ (2 * Real.pi) ^ (K + 1) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hbδ (abs_nonneg θ)).trans
      ((mul_le_mul_of_nonneg_right hθ (by positivity)).trans_eq (one_mul _))
  exact (norm_add_le _ _).trans (add_le_add
    ((linear_positive_derivative_norm_le A n hn Y).trans centeredChildCenterProjection_norm_le) hscaled)

end AVRegularity.EntryWeakProofs
end
end

section
/-! The centered displacement remains inside an explicit native spatial radius. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def independentCenteredChildDisplacementRadius (C S : ℝ) : ℝ :=
  (1 + (2 * Real.pi) ^ 2) * C * S

end AVRegularity.EntryWeakProofs
end
end

section
/-! The fresh child chart is a normalized parent difference at its literal centered base/displacement. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def independentCenteredChildChartInnerMap (D : OCData) (m : ℕ) (slot : ℤ) (u r : ℝ)
    (Fi Fa : P × Vec 2 → Vec 2) (θ : ℝ) (Y : P × (Vec 2 × (Vec 2 × Vec 2))) :
    P × (Vec 2 × Vec 2) :=
  (Y.1, independentCenteredChildBase D m slot u r θ Y,
    independentCenteredChildDisplacement D m slot u r Fi Fa θ Y)

def independentCenteredChildChart (D : OCData) (m : ℕ) (slot : ℤ) (u r : ℝ)
    (Fu Fi Fa : P × Vec 2 → Vec 2) (θ : ℝ) (Y : P × (Vec 2 × (Vec 2 × Vec 2))) : Vec 2 :=
  let B := independentCenteredChildBase D m slot u r θ Y
  let V := independentCenteredChildDisplacement D m slot u r Fi Fa θ Y
  θ⁻¹ • (Fu (Y.1, B + θ • V) - Fu (Y.1, B))

theorem independentCenteredChildChartInnerMap_contDiff (D : OCData) (m : ℕ) (slot : ℤ) (u r : ℝ)
    (Fi Fa : P × Vec 2 → Vec 2) (hFi : ContDiff ℝ (⊤ : ℕ∞) Fi)
    (hFa : ContDiff ℝ (⊤ : ℕ∞) Fa) (θ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (independentCenteredChildChartInnerMap D m slot u r Fi Fa θ) :=
  contDiff_fst.prodMk ((independentCenteredChildBase_contDiff D m slot u r θ).prodMk
    (independentCenteredChildDisplacement_contDiff D m slot u r Fi Fa hFi hFa θ))

theorem independentCenteredChildChart_contDiff (D : OCData) (m : ℕ) (slot : ℤ) (u r : ℝ)
    (Fu Fi Fa : P × Vec 2 → Vec 2) (hFu : ContDiff ℝ (⊤ : ℕ∞) Fu)
    (hFi : ContDiff ℝ (⊤ : ℕ∞) Fi) (hFa : ContDiff ℝ (⊤ : ℕ∞) Fa) (θ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (independentCenteredChildChart D m slot u r Fu Fi Fa θ) :=
  (independentCenteredReturn_contDiff Fu (fun Z => Z.2) hFu contDiff_snd θ).comp
    (independentCenteredChildChartInnerMap_contDiff D m slot u r Fi Fa hFi hFa θ)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine small renewal shear bounds every phase displacement and the centered parent base. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem weak_relative_displacement_value_le_of_small (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (m : ℕ) (slot : ℤ) (hp : Odd slot) (u r : ℝ)
    (hsmall : |u - r| * ocA D.α D.q D.Λ m ≤ 1) (phase : Vec 2) :
    ‖D.relDisp m slot u r phase‖ ≤ 2 * Real.pi := by
  have hh := weak_relative_displacement_value_bound D hΛ hζ m slot hp u r phase
  have he : |u - r| * (2 * Real.pi) * ocA D.α D.q D.Λ m =
      (|u - r| * ocA D.α D.q D.Λ m) * (2 * Real.pi) := by ring
  rw [he] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_right hsmall (by positivity)).trans_eq (one_mul _))

variable {P : Type*}

theorem independentCenteredChildBase_value_le (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (m : ℕ) (slot : ℤ) (hp : Odd slot) (u r θ : ℝ)
    (hsmall : |u - r| * ocA D.α D.q D.Λ m ≤ 1) (hθ : |θ| ≤ 1)
    (Y : P × (Vec 2 × (Vec 2 × Vec 2))) (B : ℝ) (hY : ‖Y.2.1‖ ≤ B) :
    ‖independentCenteredChildBase D m slot u r θ Y‖ ≤ B + 2 * Real.pi := by
  have hδ := weak_relative_displacement_value_le_of_small D hΛ hζ m slot hp u r hsmall Y.2.2.1
  have hδθ : ‖θ • D.relDisp m slot u r Y.2.2.1‖ ≤ 2 * Real.pi := by
    rw [norm_smul, Real.norm_eq_abs]
    exact ((mul_le_mul_of_nonneg_right hθ (norm_nonneg _)).trans_eq (one_mul _)).trans hδ
  exact (norm_add_le _ _).trans (add_le_add hY hδθ)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Full stored, slow and fast sampling jets keep the produced finer source's weight. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

theorem independentFreshCoarseAppendedNativeSource_jet_bound
    (r : ℕ) (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (m : ℕ) (parentSlot slot : ℤ) (hp : Odd parentSlot) (ell t : ℝ) (hell : |ell| ≤ 1)
    (hsmall : |D.slotAnchor (m + 1) slot - t| * ocA D.α D.q D.Λ m ≤ 1)
    (K n : ℕ) (hn : n ≤ K)
    (f : ℝ → Vec 2 → Vec (2 + 4 * (r + 1)) → E)
    (Q : IndependentParameterSourceReserve K f) (θ B : ℝ) (hθ : 0 ≤ θ) (hB : 0 ≤ B)
    (hQ : ∀ j ≤ K, Q.budget j ≤ θ * B) (Y : Vec 2 × Vec (2 + 4 * r)) :
    ‖iteratedFDeriv ℝ n (fun X : Vec 2 × Vec (2 + 4 * r) => f t 0
      (independentIntrinsicParameterPacking (4 * (r + 1)) 0
        (independentFreshCoarseAppendPacking r D m parentSlot slot ell t X))) Y‖ ≤
      θ * (K.factorial * B * (1 + (2 * Real.pi) ^ (K + 1)) ^ K) := by
  exact finite_weighted_jet_composition_bound
    (fun P => f t 0 (independentIntrinsicParameterPacking (4 * (r + 1)) 0 P))
    (independentFreshCoarseAppendPacking r D m parentSlot slot ell t) K n hn
    (Q.zeroSlow_contDiff t)
    ((independentFreshCoarseAppendPacking_contDiff r D m parentSlot slot ell t).of_le (by simp))
    Y θ B _ hθ hB (le_add_of_nonneg_right (by positivity))
    (fun j hj => (Q.zeroSlow_jet_bound t j hj _).trans (hQ j hj))
    (fun j hj hjK => independentFreshCoarseAppendPacking_positive_jets r D hΛ hζ m parentSlot slot hp
      ell t hell hsmall K j hj hjK Y)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Admissible birth-scale centers remain in the inner strip at parent normalization. -/
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

theorem independentFreshCoarseChainPacking_center_bound (D : OCData)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (A : RealChain) (bw : ℝ)
    (hbw : bw ≤ 1 / 10000) (j₀ level : ℕ) (slot : ℤ)
    (hA : IsAdmissibleChain D bw j₀ level slot A) (j : Fin A.children.length) :
    ‖independentFreshChildProjection j false (independentFreshCoarseChainPacking D A)‖ ≤ 1 / 8 := by
  have hΛ₁ : 1 ≤ D.Λ := by omega
  have hc := independentFreshActualChainPacking_center_bound D hΛ₁ A bw hbw j₀ level slot hA j
  rw [independentFreshActualChainPacking, independentFreshChildPacking_center] at hc
  rw [independentFreshCoarseChainPacking, independentFreshChildPacking_center]
  apply normalized_center_norm_le_of_length_le
    (independentFreshActualBirthLength D A j) (independentFreshCoarseBirthLength D A j)
    (1 / 8) (Construction.Stream.ocEpsilon_pos hΛ₁)
    (Construction.Stream.ocEpsilon_pos hΛ₁) ?_ A.children[j].center hc
  exact EntryScales.epsilon_antitone hq hΛ (by
    change A.baseLevel + j.val ≤ A.baseLevel + 1 + j.val
    omega)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine independent earlier fields identify the literal native forcing on an affine slow slice. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {d D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independent_lift_a_source_affine (H : ℕ) (hH : 1 ≤ H)
    (edge : ConstituentEdges D (fun _ : ι => ℝ)) (hD : 1 ≤ D)
    (a : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec d → Vec 2)
    (L : Vec 2 →L[ℝ] Vec d) (hL : ‖L‖ ≤ 1) (offset : Vec d)
    (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → Vec d → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (f : ℝ → Vec 2 → ι → ℝ)
    (F : ℕ → ℕ → ℝ → Vec 2 → Vec d → ι → ℝ)
    (hh n : ℕ) (out : ι)
    (QG : ∀ i j, IndependentParameterSourceReserve (H + 1) (fun t _ Y => G t Y i j))
    (Q1 : ∀ u, IndependentParameterSourceReserve (H + 2) (fun t z Y => F hh (n - 1) t z Y u))
    (Q2 : 2 ≤ n → ∀ u,
      IndependentParameterSourceReserve (H + 2) (fun t z Y => F hh (n - 2) t z Y u))
    (Qprev : hh ≠ 0 → ∀ j ∈ Finset.range (min D n + 1), ∀ u,
      IndependentParameterSourceReserve (H + 1 + D) (fun t z Y => F (hh - 1) (n - j) t z Y u))
    (Qa : ∀ v u e, ∀ γ ∈ edge v u e, ∀ α,
      IndependentParameterSourceReserve (H + 1) (a v u e γ α))
    (hcopy : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ t X z,
      liftApply q (Cc p q) f t X z = Real.exp (A X) • F p q t z (L X + offset))
    (hn : 1 ≤ n) (t : ℝ) (z X : Vec 2) :
    normalizedLiftASource
      ⟨η, fun t X => G t (L X + offset), v,
        independentConstituentEdgeSlice edge a Qa L offset⟩ Cc f hh n A t z X out =
      independentLiftASource edge a L A η G v F hh n out t z (L X + offset) := by
  let Q : LiftOperatorData ι (fun _ => ℝ) D :=
    ⟨η, fun t X => G t (L X + offset), v, independentConstituentEdgeSlice edge a Qa L offset⟩
  have hnorm p q (hpq : p < hh ∨ (p = hh ∧ q < n)) :
      (fun t z X => (Real.exp (A X))⁻¹ • liftApply q (Cc p q) f t X z) =
      fun t z X => F p q t z (L X + offset) := by
    funext t z X
    rw [hcopy p q hpq t X z, smul_smul, inv_mul_cancel₀ (Real.exp_ne_zero _), one_smul]
  have hnormScalar p q (hpq : p < hh ∨ (p = hh ∧ q < n)) (u : ι) :
      (fun t z X => (Real.exp (A X))⁻¹ • liftApply q (Cc p q) f t X z u) =
      fun t z X => F p q t z (L X + offset) u := by
    exact congrArg (fun B => fun t z X => B t z X u) (hnorm p q hpq)
  have hpre1 : hh < hh ∨ (hh = hh ∧ n - 1 < n) := Or.inr ⟨rfl, by omega⟩
  have hpre2 (hn2 : 2 ≤ n) : hh < hh ∨ (hh = hh ∧ n - 2 < n) := Or.inr ⟨rfl, by omega⟩
  let Q1s := fun u => ((Q1 u).affineSlice L hL offset).congrSource
    ((hnormScalar hh (n - 1) hpre1 u).symm)
  have Q2s (hn2 : 2 ≤ n) (u : ι) : JointSourceReserve (H + 2)
      (fun t z X => (Real.exp (A X))⁻¹ • liftApply (n - 2) (Cc hh (n - 2)) f t X z u) :=
    ((Q2 hn2 u).affineSlice L hL offset).congrSource
      ((hnormScalar hh (n - 2) (hpre2 hn2) u).symm)
  rw [normalized_lift_a_component_decomposition H Q Cc f hh n A out
    (fun i j => (QG i j).affineSlice L hL offset) Q1s Q2s t z X]
  rw [hnormScalar hh (n - 1) hpre1 out]
  rw [independent_normalized_cellB1_affine_slice H L hL A η G v _ QG (Q1 out) offset t z X]
  unfold independentLiftASource
  congr 1
  · congr 1
    by_cases hn2 : 2 ≤ n
    · simp only [ite_eq_left hn2]
      rw [hnormScalar hh (n - 2) (hpre2 hn2) out]
      exact independent_normalized_cellB2_affine_slice H L hL A η G _ QG (Q2 hn2 out) offset t z X
    · simp only [ite_eq_right hn2]
  · by_cases hhh : hh = 0
    · simp only [ite_eq_left hhh]
    · simp only [ite_eq_right hhh]
      apply Finset.sum_congr rfl
      intro j hj
      have hpre : hh - 1 < hh ∨ (hh - 1 = hh ∧ n - j < n) := Or.inl (by omega)
      rw [show liftApply (n - j) (Cc (hh - 1) (n - j)) f t =
        (fun X z => Real.exp (A X) • F (hh - 1) (n - j) t z (L X + offset)) from
        funext (fun X => funext (fun z => hcopy _ _ hpre t X z))]
      exact independent_source_coeff_affine_slice H hH edge hD a L hL offset A η _
        (Qprev hhh j hj) Qa j (by have := Finset.mem_range.mp hj; omega) out t z X

end AVRegularity.EntryWeakProofs
end
end
end

section
section
/-! Native spatial sizes depend on spatial Lipschitz constants, independently of mixed family jet budgets. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*}

theorem independentCenteredChildReturn_spatial_value_bound (Fi Fa : P × Vec 2 → Vec 2)
    (Y : P × (Vec 2 × (Vec 2 × Vec 2)))
    (hFi : ContDiff ℝ 1 (fun X => Fi (Y.1, X))) (V θ : ℝ) (hθ : θ ≠ 0)
    (hb : ∀ X ∈ segment ℝ (Fa (Y.1, Y.2.1)) (Fa (Y.1, Y.2.1) + θ • Y.2.2.2),
      ‖fderiv ℝ (fun Z => Fi (Y.1, Z)) X‖ ≤ V) :
    ‖independentCenteredChildReturn Fi Fa θ Y‖ ≤ V * ‖Y.2.2.2‖ :=
  independent_spatial_difference_value_bound Fi Y.1 hFi V θ hθ
    (Fa (Y.1, Y.2.1)) Y.2.2.2 hb

theorem independentCenteredChildDisplacement_spatial_value_bound
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (m : ℕ) (slot : ℤ) (hp : Odd slot) (u r : ℝ)
    (hsmall : |u - r| * ocA D.α D.q D.Λ m ≤ 1) (Fi Fa : P × Vec 2 → Vec 2)
    (Y : P × (Vec 2 × (Vec 2 × Vec 2)))
    (hFi : ContDiff ℝ 1 (fun X => Fi (Y.1, X))) (V θ : ℝ) (hV : 0 ≤ V) (hθ : θ ≠ 0)
    (S : ℝ) (hY : ‖Y.2.2.2‖ ≤ S)
    (hbFi : ∀ X ∈ segment ℝ (Fa (Y.1, Y.2.1)) (Fa (Y.1, Y.2.1) + θ • Y.2.2.2),
      ‖fderiv ℝ (fun Z => Fi (Y.1, Z)) X‖ ≤ V) :
    ‖independentCenteredChildDisplacement D m slot u r Fi Fa θ Y‖ ≤
      independentCenteredChildDisplacementRadius V S := by
  have hR := (independentCenteredChildReturn_spatial_value_bound Fi Fa Y hFi V θ hθ hbFi).trans
    (mul_le_mul_of_nonneg_left hY hV)
  have hT := weak_centered_shear_transition_value_bound D hΛ hζ m slot hp u r hsmall
    Y.2.2.1 (independentCenteredChildReturn Fi Fa θ Y)
  exact hT.trans ((mul_le_mul_of_nonneg_left hR (by positivity)).trans_eq (by
    unfold independentCenteredChildDisplacementRadius
    ring))

end AVRegularity.EntryWeakProofs
end
end

section
/-! Produced earlier independent coefficients give the full physical flux with its exact matrix grade. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {d D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def independentLiftFluxSource
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec d → Vec 2)
    (J : Vec 2 →L[ℝ] Vec d) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → Vec d → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (c : ℕ → ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (hh n : ℕ) (out inp : ι) (k : Fin 2) (t : ℝ) (z : Vec 2) (Y : Vec d) : ℝ :=
  let F := fun p q t z Y w => independentScalarLiftTestSource q (c p q) A w inp t z Y
  independentLiftFluxCrossSource J A η G v (fun t z Y => F hh (n - 1) t z Y out)
    (fun t z Y => F hh (n - 2) t z Y out) k t z Y -
    Real.sqrt η • ∑ j ∈ Finset.Icc 1 (min D n),
      independentSourceFluxComponentCoefficient edge a J A η (F (hh - 1) (n - j)) k (j - 1) out t z Y

def independentLiftFluxProductionCost (H D n count : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (η BG BV BE B : ℝ) : ℝ :=
  let BF := finiteLiftSymbolBudget n A * B
  normalizedLiftFluxCrossBudget H A η BG BV BF BF +
    ‖(-Real.sqrt η) • ContinuousLinearMap.id ℝ ℝ‖ *
      ((Finset.Icc 1 (min D n)).card : ℝ) * normalizedSourceFluxMatrixBudget H D count A η BE BF

theorem independentLiftFlux_uniform_production (H : ℕ)
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec d → Vec 2)
    (J : Vec 2 →L[ℝ] Vec d) (hJ : ‖J‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → Vec d → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (c : ℕ → ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (hh n : ℕ) (hn : 2 ≤ n) (hhpos : hh ≠ 0) (out inp : ι) (k : Fin 2)
    (QG : ∀ i j, IndependentParameterSourceReserve H (fun t _ Y => G t Y i j))
    (Qv : ∀ i, IndependentParameterSourceReserve H (fun t z (_ : Vec d) => v t z i))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      IndependentParameterSourceReserve (H + D + 2) (fun t z Y => c p q m.val α t z Y v u))
    (Qa : ∀ v u e, ∀ γ ∈ edge v u e, ∀ α, IndependentParameterSourceReserve H (a v u e γ α))
    (M : ι → ι → ℝ) (hM : ∀ v u, 0 ≤ M v u) (count : ℕ)
    (BG BV BE B : ℝ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 0 ≤ B)
    (hG : ∀ i j r, r ≤ H → (QG i j).budget r ≤ BG)
    (hv : ∀ i r, r ≤ H → (Qv i).budget r ≤ BV)
    (hc : ∀ p q hpq m α v u r, r ≤ H + D + 2 → (Qc p q hpq m α v u).budget r ≤ finiteMatrixPower M p v u * B)
    (he : ∀ v u e γ hγ α r, r ≤ H → (Qa v u e γ hγ α).budget r ≤ M v u * BE)
    (hm : ∀ v u e γ, γ ∈ edge v u e → ‖γ.map‖ ≤ 1)
    (hlen : ∀ v u e, (edge v u e).length ≤ count) :
    ∃ Q : IndependentParameterSourceReserve H (independentLiftFluxSource edge a J A η G v c hh n out inp k),
      ∀ r ≤ H, Q.budget r ≤ finiteMatrixPower M hh out inp *
        independentLiftFluxProductionCost H D n count A η BG BV BE B := by
  let BF := finiteLiftSymbolBudget n A * B
  let BT := normalizedSourceFluxMatrixBudget H D count A η BE BF
  have hBF : 0 ≤ BF := mul_nonneg (finiteLiftSymbolBudget_nonneg n A) hB
  let F := fun p q t z Y w => independentScalarLiftTestSource q (c p q) A w inp t z Y
  let Qt := fun p q (hpq : p < hh ∨ (p = hh ∧ q < n)) K (hK : K ≤ H + D + 2) w =>
    independentScalarLiftTestSourceReserve K q (c p q) A w inp
      (fun m α => (Qc p q hpq m α w inp).restrictOrder K hK)
  have ht p q hpq K hK w (hq : q ≤ n) r (hr : r ≤ K) :
      (Qt p q hpq K hK w).budget r ≤ finiteMatrixPower M p w inp * BF := by
    exact independentScalarLiftTestSourceReserve_menu_budget K q n hq (c p q) A w inp _
      (finiteMatrixPower M p w inp) B (finiteMatrixPower_nonneg M hM p w inp) hB
      (fun m α r hr => hc p q hpq m α w inp r (hr.trans hK)) r hr
  have hpre1 : hh < hh ∨ (hh = hh ∧ n - 1 < n) := Or.inr ⟨rfl, by omega⟩
  have hpre2 : hh < hh ∨ (hh = hh ∧ n - 2 < n) := Or.inr ⟨rfl, by omega⟩
  let Q₁ := Qt hh (n - 1) hpre1 (H + 1) (by omega) out
  let Q₂ := Qt hh (n - 2) hpre2 (H + 1) (by omega) out
  let QC := independentLiftFluxCrossSourceReserve H J hJ A η G v _ _ QG Qv Q₁ Q₂ k
  have hQC r (hr : r ≤ H) : QC.budget r ≤ finiteMatrixPower M hh out inp *
      normalizedLiftFluxCrossBudget H A η BG BV BF BF :=
    independentLiftFluxCrossSourceReserve_uniform_budget H J hJ A η G v _ _ QG Qv Q₁ Q₂ k
      (finiteMatrixPower M hh out inp) BG BV BF BF (finiteMatrixPower_nonneg M hM hh out inp)
      hBG hBV hBF hBF hG hv (ht _ _ _ _ _ out (Nat.sub_le _ _))
      (ht _ _ _ _ _ out (Nat.sub_le _ _)) r hr
  have hT j (_hj : j ∈ Finset.Icc 1 (min D n)) :
      ∃ Q : IndependentParameterSourceReserve H
        (independentSourceFluxComponentCoefficient edge a J A η (F (hh - 1) (n - j)) k (j - 1) out),
        ∀ r ≤ H, Q.budget r ≤ finiteMatrixPower M hh out inp * BT := by
    obtain ⟨Q, hQ⟩ := independentSourceFlux_matrix_reserve H edge a J hJ η A (F (hh - 1) (n - j)) M hM
      (hh - 1) count out inp (fun w => Qt (hh - 1) (n - j) (Or.inl (by omega)) (H + D) (by omega) w)
      (Qa out) BE BF hBE hBF (fun w r hr => ht _ _ _ _ _ w (Nat.sub_le _ _) r hr)
      (he out) (hm out) (hlen out) k (j - 1)
    refine ⟨Q, ?_⟩
    have hgrade : 1 + (hh - 1) = hh := by omega
    simpa only [hgrade] using hQ
  choose QT hQT using hT
  let T := IndependentParameterSourceReserve.finsetSum (Finset.Icc 1 (min D n)) H _ QT
  let L : ℝ →L[ℝ] ℝ := (-Real.sqrt η) • ContinuousLinearMap.id ℝ ℝ
  refine ⟨(QC.add (T.map L)).congrSource (by
    funext t z Y
    simp only [independentLiftFluxSource, L, smul_apply, ContinuousLinearMap.id_apply,
      neg_smul, sub_eq_add_neg]
    rfl), ?_⟩
  intro r hr
  rw [IndependentParameterSourceReserve.congrSource_budget]
  have hTs := IndependentParameterSourceReserve.finsetSum_uniform_budget _ H _ QT
    (finiteMatrixPower M hh out inp) BT hQT
  have hLM := T.map_uniform_budget L (finiteMatrixPower M hh out inp) (((Finset.Icc 1 (min D n)).card : ℝ) * BT)
    (fun r hr => (hTs r hr).trans_eq (by ring))
  exact (QC.add_uniform_budget (T.map L) _ _ _ hQC hLM r hr).trans_eq (by
    dsimp only [independentLiftFluxProductionCost, BF, BT, L]
    ring)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Mixed derivative prices and spatial value radii stay separate in the fresh centered displacement. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def independentCenteredChildDisplacementMixedCost (K : ℕ) (C V S : ℝ) : ℝ :=
  K.factorial * (max (independentCenteredReturnCost K C S)
    (1 + weakCenteredRelativeShearCost K (V * S))) ^ (K + 1)

theorem independentCenteredChildDisplacementMixedCost_ge_one (K : ℕ) (C V S : ℝ) (hC : 1 ≤ C) :
    1 ≤ independentCenteredChildDisplacementMixedCost K C V S :=
  positiveJetCompositionBudget_ge_one K _
    ((independentCenteredReturnCost_ge_one K C S hC).trans (le_max_left _ _))

theorem independentCenteredChildDisplacement_mixed_jet_bound
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (m : ℕ) (slot : ℤ) (hp : Odd slot) (u r : ℝ)
    (hsmall : |u - r| * ocA D.α D.q D.Λ m ≤ 1)
    (Fi Fa : P × Vec 2 → Vec 2) (hFi : ContDiff ℝ (⊤ : ℕ∞) Fi)
    (hFa : ContDiff ℝ (⊤ : ℕ∞) Fa) (K n : ℕ) (hn : 1 ≤ n) (hnK : n ≤ K)
    (C : ℝ) (hC : 1 ≤ C) (V : ℝ) (hV : 0 ≤ V) (θ : ℝ) (hθ : θ ≠ 0) (hθ₁ : |θ| ≤ 1)
    (Y : P × (Vec 2 × (Vec 2 × Vec 2))) (S : ℝ) (hY : ‖Y.2.2.2‖ ≤ S)
    (hbFa : ∀ i, 1 ≤ i → i ≤ K → ‖iteratedFDeriv ℝ i Fa (Y.1, Y.2.1)‖ ≤ C)
    (hbFi : ∀ i, 1 ≤ i → i ≤ K + 1 →
      ∀ Z ∈ segment ℝ (Y.1, Fa (Y.1, Y.2.1))
        (Y.1, Fa (Y.1, Y.2.1) + θ • Y.2.2.2), ‖iteratedFDeriv ℝ i Fi Z‖ ≤ C)
    (hbFiSpatial : ∀ Z ∈ segment ℝ (Fa (Y.1, Y.2.1))
      (Fa (Y.1, Y.2.1) + θ • Y.2.2.2), ‖fderiv ℝ (fun X => Fi (Y.1, X)) Z‖ ≤ V) :
    ‖iteratedFDeriv ℝ n (independentCenteredChildDisplacement D m slot u r Fi Fa θ) Y‖ ≤
      independentCenteredChildDisplacementMixedCost K C V S := by
  let R := independentCenteredChildReturn Fi Fa θ
  let Q := centeredChildPhaseProjection (P := P) (V := Vec 2)
  let G := fun Z => (Q Z, R Z)
  let T := weakCenteredShearTransition D m slot u r
  let B := max (independentCenteredReturnCost K C S)
    (1 + weakCenteredRelativeShearCost K (V * S))
  have hRC := independentCenteredReturnCost_ge_one K C S hC
  have hB : 1 ≤ B := hRC.trans (le_max_left _ _)
  have hR : ContDiff ℝ (⊤ : ℕ∞) R := independentCenteredChildReturn_contDiff Fi Fa hFi hFa θ
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := Q.contDiff.prodMk hR
  have hFiSpatial : ContDiff ℝ 1 (fun X => Fi (Y.1, X)) :=
    (hFi.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hRV : ‖R Y‖ ≤ V * S :=
    (independentCenteredChildReturn_spatial_value_bound Fi Fa Y hFiSpatial V θ hθ hbFiSpatial).trans
      (mul_le_mul_of_nonneg_left hY hV)
  have he : independentCenteredChildDisplacement D m slot u r Fi Fa θ = T ∘ G := rfl
  rw [he]
  apply finite_positive_jet_composition_bound T G
    (weakCenteredShearTransition_contDiff D m slot u r) hG K n hn hnK Y B hB
  · intro i hi hiK
    exact (weak_centered_shear_transition_positive_jet_bound D hΛ hζ m slot hp u r hsmall
      K i hi hiK (V * S) (Q Y) (R Y) hRV).trans (le_max_right _ _)
  · intro i hi hiK
    have hRN : ContDiff ℝ (i : ℕ∞) R := hR.of_le (by simp)
    have hQN : ContDiff ℝ (i : ℕ∞) Q := Q.contDiff
    have hbR : ‖iteratedFDeriv ℝ i R Y‖ ≤ independentCenteredReturnCost K C S :=
      independentCenteredChildReturn_positive_jet_bound Fi Fa hFi hFa K i hi hiK
        C hC θ hθ hθ₁ Y S hY hbFa hbFi
    have hbQ : ‖iteratedFDeriv ℝ i Q Y‖ ≤ independentCenteredReturnCost K C S :=
      (linear_positive_derivative_norm_le Q i hi Y).trans
        (centeredChildPhaseProjection_norm_le.trans hRC)
    exact ((independent_joint_pair_jet_bound Q R i hQN hRN Y).trans (max_le hbQ hbR)).trans
      (le_max_left _ _)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Separate spatial and mixed budgets control the fresh input to the parent difference. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def independentCenteredChildChartInnerMixedCost (K : ℕ) (C V S : ℝ) : ℝ :=
  max (1 + (2 * Real.pi) ^ (K + 1)) (independentCenteredChildDisplacementMixedCost K C V S)

theorem independentCenteredChildChartInnerMixedCost_ge_one (K : ℕ) (C V S : ℝ) (hC : 1 ≤ C) :
    1 ≤ independentCenteredChildChartInnerMixedCost K C V S :=
  (independentCenteredChildDisplacementMixedCost_ge_one K C V S hC).trans (le_max_right _ _)

theorem independentCenteredChildChartInnerMap_mixed_jet_bound
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (m : ℕ) (slot : ℤ) (hp : Odd slot) (u r : ℝ)
    (hsmall : |u - r| * ocA D.α D.q D.Λ m ≤ 1)
    (Fi Fa : P × Vec 2 → Vec 2) (hFi : ContDiff ℝ (⊤ : ℕ∞) Fi)
    (hFa : ContDiff ℝ (⊤ : ℕ∞) Fa) (K n : ℕ) (hn : 1 ≤ n) (hnK : n ≤ K)
    (C : ℝ) (hC : 1 ≤ C) (V₀ : ℝ) (hV₀ : 0 ≤ V₀) (θ : ℝ) (hθ : θ ≠ 0) (hθ₁ : |θ| ≤ 1)
    (Y : P × (Vec 2 × (Vec 2 × Vec 2))) (S : ℝ) (hY : ‖Y.2.2.2‖ ≤ S)
    (hbFa : ∀ i, 1 ≤ i → i ≤ K → ‖iteratedFDeriv ℝ i Fa (Y.1, Y.2.1)‖ ≤ C)
    (hbFi : ∀ i, 1 ≤ i → i ≤ K + 1 →
      ∀ Z ∈ segment ℝ (Y.1, Fa (Y.1, Y.2.1))
        (Y.1, Fa (Y.1, Y.2.1) + θ • Y.2.2.2), ‖iteratedFDeriv ℝ i Fi Z‖ ≤ C)
    (hbFiSpatial : ∀ Z ∈ segment ℝ (Fa (Y.1, Y.2.1))
      (Fa (Y.1, Y.2.1) + θ • Y.2.2.2), ‖fderiv ℝ (fun X => Fi (Y.1, X)) Z‖ ≤ V₀) :
    ‖iteratedFDeriv ℝ n (independentCenteredChildChartInnerMap D m slot u r Fi Fa θ) Y‖ ≤
      independentCenteredChildChartInnerMixedCost K C V₀ S := by
  let A := independentCenteredChildBase (P := P) D m slot u r θ
  let V := independentCenteredChildDisplacement D m slot u r Fi Fa θ
  let Q : (P × (Vec 2 × (Vec 2 × Vec 2))) →L[ℝ] P :=
    ContinuousLinearMap.fst ℝ P (Vec 2 × (Vec 2 × Vec 2))
  have hA : ContDiff ℝ (n : ℕ∞) A :=
    (independentCenteredChildBase_contDiff D m slot u r θ).of_le (by simp)
  have hV : ContDiff ℝ (n : ℕ∞) V :=
    (independentCenteredChildDisplacement_contDiff D m slot u r Fi Fa hFi hFa θ).of_le (by simp)
  have hQ : ContDiff ℝ (n : ℕ∞) Q := Q.contDiff
  have hbA : ‖iteratedFDeriv ℝ n A Y‖ ≤ 1 + (2 * Real.pi) ^ (K + 1) :=
    independentCenteredChildBase_positive_jet_bound D hΛ hζ m slot hp u r θ hsmall hθ₁
      K n hn hnK Y
  have hbV : ‖iteratedFDeriv ℝ n V Y‖ ≤ independentCenteredChildDisplacementMixedCost K C V₀ S :=
    independentCenteredChildDisplacement_mixed_jet_bound D hΛ hζ m slot hp u r hsmall
      Fi Fa hFi hFa K n hn hnK C hC V₀ hV₀ θ hθ hθ₁ Y S hY hbFa hbFi hbFiSpatial
  have hbAV : ‖iteratedFDeriv ℝ n (fun Z => (A Z, V Z)) Y‖ ≤
      independentCenteredChildChartInnerMixedCost K C V₀ S :=
    (independent_joint_pair_jet_bound A V n hA hV Y).trans (max_le_max hbA hbV)
  have hQnorm : ‖Q‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun Z => by
    rw [one_mul]; exact norm_fst_le Z)
  have hbQ : ‖iteratedFDeriv ℝ n Q Y‖ ≤ independentCenteredChildChartInnerMixedCost K C V₀ S :=
    (linear_positive_derivative_norm_le Q n hn Y).trans
      (hQnorm.trans (independentCenteredChildChartInnerMixedCost_ge_one K C V₀ S hC))
  exact (independent_joint_pair_jet_bound Q (fun Z => (A Z, V Z)) n hQ (hA.prodMk hV) Y).trans
    (max_le hbQ hbAV)

end AVRegularity.EntryWeakProofs
end
end

section
/-! The actual pulse supplies full independent source reserves with its true Peclet price. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def independentPulseSourceReserve (H : ℕ) {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {ν : ℝ} (hΛ : 1 ≤ Λ) (hν : 0 < ν) (hζ : IsFastProfile ζ) {slot : ℤ} (hp : Odd slot) :
    IndependentParameterSourceReserve H (fun t z (_ : P) => ocPulseCellDrift α q Λ ζ m ν slot t z) :=
  independentFastOnlySourceReserve H _
    (fun t => (normalizedPulseDrift_contDiff hΛ hν hp t).of_le (by simp))
    (fun t => normalizedPulseDrift_periodic hΛ hν hp t)
    (normalizedPulseDrift_joint_continuous hΛ hν hζ hp).measurable
    (fun _ => (ocEpsilon q Λ m ^ (1 + α) / ν) * pulseFastDerivativeConstant H)
    (fun _ => mul_nonneg (div_nonneg (Real.rpow_nonneg
      (Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ).le _) hν.le)
      (pulseFastDerivativeConstant_nonneg H))
    (fun n hn t z => normalizedPulseDrift_vector_fast_bound hΛ hν hζ hp H n hn t z)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Earlier mixed chart menus produce fresh mixed jets while spatial radii use only spatial Lipschitz constants. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def independentCenteredChildChartMixedCost (K : ℕ) (C V S : ℝ) : ℝ :=
  K.factorial * (max (independentCenteredChildChartInnerMixedCost K C V S)
    ((2 : ℝ) ^ K * C * (independentCenteredChildDisplacementRadius V S + K))) ^ (K + 1)

theorem independentCenteredChildChart_mixed_jet_bound
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (m : ℕ) (slot : ℤ) (hp : Odd slot) (u r : ℝ)
    (hsmall : |u - r| * ocA D.α D.q D.Λ m ≤ 1)
    (Fu Fi Fa : P × Vec 2 → Vec 2) (hFu : ContDiff ℝ (⊤ : ℕ∞) Fu) (hFi : ContDiff ℝ (⊤ : ℕ∞) Fi)
    (hFa : ContDiff ℝ (⊤ : ℕ∞) Fa) (K n : ℕ) (hn : 1 ≤ n) (hnK : n ≤ K)
    (C : ℝ) (hC : 1 ≤ C) (V : ℝ) (hV₀ : 0 ≤ V) (θ : ℝ) (hθ : θ ≠ 0) (hθ₁ : |θ| ≤ 1)
    (Y : P × (Vec 2 × (Vec 2 × Vec 2))) (S : ℝ) (hY : ‖Y.2.2.2‖ ≤ S)
    (hbFa : ∀ i, 1 ≤ i → i ≤ K → ‖iteratedFDeriv ℝ i Fa (Y.1, Y.2.1)‖ ≤ C)
    (hbFi : ∀ i, 1 ≤ i → i ≤ K + 1 →
      ∀ Z ∈ segment ℝ (Y.1, Fa (Y.1, Y.2.1))
        (Y.1, Fa (Y.1, Y.2.1) + θ • Y.2.2.2), ‖iteratedFDeriv ℝ i Fi Z‖ ≤ C)
    (hbFiSpatial : ∀ Z ∈ segment ℝ (Fa (Y.1, Y.2.1))
      (Fa (Y.1, Y.2.1) + θ • Y.2.2.2), ‖fderiv ℝ (fun X => Fi (Y.1, X)) Z‖ ≤ V)
    (hbFu : ∀ i, 1 ≤ i → i ≤ K + 1 →
      ∀ Z ∈ segment ℝ (Y.1, independentCenteredChildBase D m slot u r θ Y)
        (Y.1, independentCenteredChildBase D m slot u r θ Y +
          θ • independentCenteredChildDisplacement D m slot u r Fi Fa θ Y),
        ‖iteratedFDeriv ℝ i Fu Z‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (independentCenteredChildChart D m slot u r Fu Fi Fa θ) Y‖ ≤
      independentCenteredChildChartMixedCost K C V S := by
  let F : P × (Vec 2 × Vec 2) → Vec 2 := fun Z =>
    θ⁻¹ • (Fu (Z.1, Z.2.1 + θ • Z.2.2) - Fu (Z.1, Z.2.1))
  let G := independentCenteredChildChartInnerMap D m slot u r Fi Fa θ
  let B := max (independentCenteredChildChartInnerMixedCost K C V S)
    ((2 : ℝ) ^ K * C * (independentCenteredChildDisplacementRadius V S + K))
  have hB : 1 ≤ B :=
    (independentCenteredChildChartInnerMixedCost_ge_one K C V S hC).trans (le_max_left _ _)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    independentCenteredReturn_contDiff Fu (fun Z => Z.2) hFu contDiff_snd θ
  have hG : ContDiff ℝ (⊤ : ℕ∞) G :=
    independentCenteredChildChartInnerMap_contDiff D m slot u r Fi Fa hFi hFa θ
  have hFiSpatial : ContDiff ℝ 1 (fun X => Fi (Y.1, X)) :=
    (hFi.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have hV := independentCenteredChildDisplacement_spatial_value_bound D hΛ hζ m slot hp u r hsmall
    Fi Fa Y hFiSpatial V θ hV₀ hθ S hY hbFiSpatial
  have he : independentCenteredChildChart D m slot u r Fu Fi Fa θ = F ∘ G := rfl
  rw [he]
  apply finite_positive_jet_composition_bound F G hF hG K n hn hnK Y B hB
  · intro i _ hiK
    exact (independent_spatial_difference_joint_menu_bound Fu K i (hFu.of_le (by simp))
      hiK C (zero_le_one.trans hC) θ hθ hθ₁ Y.1
      (independentCenteredChildBase D m slot u r θ Y)
      (independentCenteredChildDisplacement D m slot u r Fi Fa θ Y)
      (independentCenteredChildDisplacementRadius V S) hV hbFu).trans (le_max_right _ _)
  · intro i hi hiK
    exact (independentCenteredChildChartInnerMap_mixed_jet_bound D hΛ hζ m slot hp u r hsmall
      Fi Fa hFi hFa K i hi hiK C hC V hV₀ θ hθ hθ₁ Y S hY hbFa hbFi hbFiSpatial).trans (le_max_left _ _)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Finite lift tests and their ordered mean actions preserve equivalent open slow slices. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {U : Set (Vec 2)}

theorem independentScalarLiftTestSource_slow_slice_congr
    (L : Vec 2 →L[ℝ] P) (Y Z : P) (n : ℕ)
    (c e : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → P → ι → ι → ℝ)
    (hc : ∀ m α v u, IndependentSourceSlowSliceEqOn L U Y Z
      (fun t z W => c m α t z W v u) (fun t z W => e m α t z W v u))
    (A : Vec 2 →L[ℝ] ℝ) (v u : ι) :
    IndependentSourceSlowSliceEqOn L U Y Z
      (independentScalarLiftTestSource n c A v u) (independentScalarLiftTestSource n e A v u) := by
  intro t X hX z
  have he : independentScalarCoefficientLift c (L X + Y) =
      independentScalarCoefficientLift e (L X + Z) := by
    funext m α τ W w v' u'
    dsimp only [independentScalarCoefficientLift]
    exact congrArg (fun a : ℝ => a • ContinuousLinearMap.id ℝ ℝ) (hc m α v' u' τ X hX w)
  dsimp only [independentScalarLiftTestSource]
  rw [he]

omit [DecidableEq ι] in
theorem independentLiftApplySource_slow_slice_congr (n : ℕ)
    (c e : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → P → ι → ι → ℝ)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (Y Z : P) (A : Vec 2 →L[ℝ] ℝ)
    (f g : ℝ → P → ι → ℝ) (v : ι)
    (Qf : ∀ u, IndependentParameterSourceReserve n (fun t (_ : Vec 2) W => f t W u))
    (Qg : ∀ u, IndependentParameterSourceReserve n (fun t (_ : Vec 2) W => g t W u))
    (hU : IsOpen U)
    (hc : ∀ m α u, IndependentSourceSlowSliceEqOn L U Y Z
      (fun t z W => c m α t z W v u) (fun t z W => e m α t z W v u))
    (hf : ∀ u, IndependentSourceSlowSliceEqOn L U Y Z
      (fun t (_ : Vec 2) W => f t W u) (fun t _ W => g t W u)) :
    IndependentSourceSlowSliceEqOn L U Y Z
      (independentLiftApplySource n c L A f v) (independentLiftApplySource n e L A g v) := by
  intro t X hX z
  dsimp only [independentLiftApplySource]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro u _
  have hcoeff := hc m.val α u t X hX z
  have hword := independentSourceCovariantWord_slow_slice_congr L hL Y Z (Qf u) (Qg u) hU
    (hf u) A m.val (by have := m.isLt; omega) α t X hX z
  dsimp only at hcoeff
  rw [hcoeff, hword]

omit [DecidableEq ι] in
theorem independentLiftMeanCompositionSource_slow_slice_congr {d : ℕ} (j : ℕ)
    (c e : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (L : Vec 2 →L[ℝ] Vec d) (hL : ‖L‖ ≤ 1) (Y Z : Vec d) (A : Vec 2 →L[ℝ] ℝ)
    (F G : ℝ → Vec 2 → Vec d → ι → ℝ) (v : ι)
    (QF : ∀ u, IndependentParameterSourceReserve j (fun t z W => F t z W u))
    (QG : ∀ u, IndependentParameterSourceReserve j (fun t z W => G t z W u))
    (hU : IsOpen U)
    (hc : ∀ m α u, IndependentSourceSlowSliceEqOn L U Y Z
      (fun t z W => c m α t z W v u) (fun t z W => e m α t z W v u))
    (hF : ∀ u, IndependentSourceSlowSliceEqOn L U Y Z
      (fun t z W => F t z W u) (fun t z W => G t z W u)) :
    IndependentSourceSlowSliceEqOn L U Y Z
      (independentLiftMeanCompositionSource j c L A F v)
      (independentLiftMeanCompositionSource j e L A G v) := by
  apply independentLiftApplySource_slow_slice_congr j c e L hL Y Z A _ _ v
    (fun u => (QF u).mean) (fun u => (QG u).mean) hU hc
  intro u t X hX _
  change fieldCellMean (fun z => F t z (L X + Y) u) =
    fieldCellMean (fun z => G t z (L X + Z) u)
  congr 1
  funext z
  exact hF u t X hX z

end AVRegularity.EntryWeakProofs
end
end

section
/-! Spatial carrier radii are fixed before any mixed derivative budgets are evaluated. -/
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

def centeredParentRadius (β S : ℝ) : ℝ :=
  4 * (1 + β) + 4 * (1 + β ^ 2) * (S + 1)

theorem centeredParentRadius_inverse_input (β S : ℝ) (hβ : 0 ≤ β) (hS : 0 ≤ S) :
    2 * (1 + β) + S ≤ centeredParentRadius β S := by
  unfold centeredParentRadius
  nlinarith only [hβ, hS, sq_nonneg β, mul_nonneg (sq_nonneg β) hS]

theorem centeredParentRadius_forward_input (β S : ℝ) (hβ : 0 ≤ β) (hS : 0 ≤ S) :
    1 + 2 * β + 2 * (1 + β ^ 2) * S ≤ centeredParentRadius β S := by
  unfold centeredParentRadius
  nlinarith only [hβ, hS, sq_nonneg β, mul_nonneg (sq_nonneg β) hS]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Every actual pulse entry keeps the vector derivative price, uniformly over family parameters. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def independentPulseEntrySourceReserve (H : ℕ) {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {ν : ℝ} (hΛ : 1 ≤ Λ) (hν : 0 < ν) (hζ : IsFastProfile ζ) {slot : ℤ} (hp : Odd slot) (i : Fin 2) :
    IndependentParameterSourceReserve H (fun t z (_ : P) => ocPulseCellDrift α q Λ ζ m ν slot t z i) :=
  (independentPulseSourceReserve H hΛ hν hζ hp).map (ContinuousLinearMap.proj i)

theorem independentPulseEntrySourceReserve_response_budget (H : ℕ) {α q : ℝ} {Λ m : ℕ}
    {ζ : ℝ → ℝ} {ν : ℝ} (hΛ : 1 ≤ Λ) (hν : 0 < ν) (hζ : IsFastProfile ζ)
    {slot : ℤ} (hp : Odd slot) (i : Fin 2) (n : ℕ) :
    (independentPulseEntrySourceReserve (P := P) (α := α) (q := q) (m := m)
      H hΛ hν hζ hp i).budget n ≤
      (ocEpsilon q Λ m ^ (1 + α) / ν) * pulseFastDerivativeConstant H := by
  let L : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (fun z => by
    simpa only [L, ContinuousLinearMap.proj_apply, one_mul] using norm_le_pi_norm z i)
  have hB : 0 ≤ (ocEpsilon q Λ m ^ (1 + α) / ν) * pulseFastDerivativeConstant H :=
    mul_nonneg (div_nonneg (Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le _) hν.le)
      (pulseFastDerivativeConstant_nonneg H)
  change ‖L‖ * ((ocEpsilon q Λ m ^ (1 + α) / ν) * pulseFastDerivativeConstant H) ≤ _
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hL hB

theorem independentPulseEntrySourceReserve_budget_bound (H : ℕ) {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {ν : ℝ} (hΛ : 1 ≤ Λ) (hν : 0 < ν) (hζ : IsFastProfile ζ) {slot : ℤ} (hp : Odd slot)
    (hPe : ocEpsilon q Λ m ^ (1 + α) / ν ≤ 1) (i : Fin 2) (n : ℕ) :
    (independentPulseEntrySourceReserve (P := P) (α := α) (q := q) (m := m) H hΛ hν hζ hp i).budget n ≤
      pulseFastDerivativeConstant H := by
  let L : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (fun z => by
    simpa only [L, ContinuousLinearMap.proj_apply, one_mul] using norm_le_pi_norm z i)
  have hB : 0 ≤ (ocEpsilon q Λ m ^ (1 + α) / ν) * pulseFastDerivativeConstant H :=
    mul_nonneg (div_nonneg (Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le _) hν.le)
      (pulseFastDerivativeConstant_nonneg H)
  change ‖L‖ * ((ocEpsilon q Λ m ^ (1 + α) / ν) * pulseFastDerivativeConstant H) ≤ _
  exact (mul_le_mul_of_nonneg_right hL hB).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hPe (pulseFastDerivativeConstant_nonneg H))

end AVRegularity.EntryWeakProofs
end
end

section
/-! The independent child-chart model equals the actual child geometry, with parent-scale center coordinates. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*}

theorem childGeom_chart_eq_independentCenteredChildChart (D : OCData) (k : ℕ) (slot : ℤ)
    (g : P → ChainGeom) (p : P) (hg : ChainGeometry.InvLaw (g p)) (anchor u ρ θ : ℝ)
    (hρ : ρ ≠ 0) (hθ : θ ≠ 0) (he : D.eps k ≠ 0) (hscale : D.eps k = ρ * θ)
    (c : ChainChild) (C H : Vec 2) (hc : c.center = ρ • C) :
    centeredGeometryChart (D.childGeom k slot anchor c (g p)) (D.eps k) u H =
      independentCenteredChildChart D k slot u anchor
        (fun Y : P × Vec 2 => centeredGeometryChart (g Y.1) ρ u Y.2)
        (fun Y : P × Vec 2 => centeredGeometryChartInv (g Y.1) ρ anchor Y.2)
        (fun Y : P × Vec 2 => centeredGeometryChart (g Y.1) ρ anchor Y.2)
        θ (p, C, c.phase, H) := by
  have hcc : c.center = D.eps k • (θ⁻¹ • C) := by
    rw [hc, hscale, smul_smul, mul_assoc, mul_inv_cancel₀ hθ, mul_one]
  have hR := childCenterReturn_eq_independentCenteredReturn g p hg anchor ρ θ hρ c C H hc
  rw [← hscale] at hR
  have hB : θ • (θ⁻¹ • C + D.relDisp k slot u anchor c.phase) =
      C + θ • D.relDisp k slot u anchor c.phase := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hθ, one_smul]
  have hh := childGeom_centered_chart_factorization D k slot anchor (g p) hg c
    ρ θ he hscale (θ⁻¹ • C) H hcc u
  dsimp only at hh
  rw [hR, hB] at hh
  exact hh

end AVRegularity.EntryWeakProofs
end
end

section
/-! Full mixed chart menus spend one earlier derivative per child; spatial radii use the fixed Lipschitz constant two. -/
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

def nativeMixedChartInverseCost (K : ℕ) (C S : ℝ) : ℝ :=
  K.factorial * (max (independentCenteredChildChartMixedCost K C 2 S)
    (1 + (2 * Real.pi) ^ (K + 1))) ^ (K + 1)

def nativeMixedChartStepCost (K : ℕ) (C S : ℝ) : ℝ :=
  max 1 (max (independentCenteredChildChartMixedCost K C 2 S) (nativeMixedChartInverseCost K C S))

def nativeMixedChartBudget : ℕ → ℕ → ℝ → ℝ
  | K, 0, _ => weakBaseChartJetBudget K
  | K, n + 1, S => nativeMixedChartStepCost K
      (nativeMixedChartBudget (K + 1) n (centeredParentRadius (2 * Real.pi) S)) S
termination_by _ n _ => n

theorem nativeMixedChartStepCost_ge_one (K : ℕ) (C S : ℝ) :
    1 ≤ nativeMixedChartStepCost K C S := le_max_left _ _

theorem nativeMixedChartBudget_ge_one (K n : ℕ) (S : ℝ) :
    1 ≤ nativeMixedChartBudget K n S := by
  cases n with
  | zero =>
    rw [nativeMixedChartBudget]
    exact weakBaseChartJetBudget_ge_one K
  | succ n =>
    rw [nativeMixedChartBudget]
    exact nativeMixedChartStepCost_ge_one K _ S

theorem nativeMixedChartStepCost_forward (K : ℕ) (C S : ℝ) :
    independentCenteredChildChartMixedCost K C 2 S ≤ nativeMixedChartStepCost K C S :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem nativeMixedChartStepCost_inverse (K : ℕ) (C S : ℝ) :
    nativeMixedChartInverseCost K C S ≤ nativeMixedChartStepCost K C S :=
  (le_max_right _ _).trans (le_max_right _ _)

end AVRegularity.EntryWeakProofs
end
end
end
