-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import AVRegularity.Proofs.GenSem.ChainMetric
public import AVRegularity.EntryWeak.FluxProductionArithmetic
public import AVRegularity.EntryWeak.NormalizedLiftAComponentDecomposition
import AVRegularity.CycleEvolution.CellInverseJetFactorialBound
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs

/-! Extending literal native coefficients preserves every algebraic initial, degree, order and symmetry clause. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d D N R sX sZ : ℕ} {a b : ℝ}

theorem independentCarrierCoefficientExtension_above_degree_on (V : Set (Vec d))
    (c : Vec d → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (Q : Vec d → LiftOperatorData ι (fun _ => ℝ) D)
    (Ω : Vec d → Set (Vec 2))
    (hc : ∀ P ∈ V, IsLiftSequenceOn (Ω P) (Q P) sX sZ a b N R (c P)) (P : Vec d)
    (hh n m : ℕ) (hhh : hh ≤ R) (hn : N < n) (α : DerivativeWord2 m)
    (t : ℝ) (X z : Vec 2) (v u : ι) :
    independentCarrierCoefficientExtension V c P hh n m α t X z v u = 0 := by
  have hn0 : n ≠ 0 := by omega
  by_cases hP : P ∈ V
  · simp only [independentCarrierCoefficientExtension, ite_eq_right hn0, ite_eq_left hP]
    exact (hc P hP).2.2.1 hh hhh n hn m α t X z v u
  · simp only [independentCarrierCoefficientExtension, ite_eq_right hn0, ite_eq_right hP, Pi.zero_apply]

theorem independentCarrierCoefficientExtension_above_order_on (V : Set (Vec d))
    (c : Vec d → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (Q : Vec d → LiftOperatorData ι (fun _ => ℝ) D)
    (Ω : Vec d → Set (Vec 2))
    (hc : ∀ P ∈ V, IsLiftSequenceOn (Ω P) (Q P) sX sZ a b N R (c P)) (P : Vec d)
    (hh n m : ℕ) (hhh : hh ≤ R) (hm : n < m) (α : DerivativeWord2 m)
    (t : ℝ) (X z : Vec 2) (v u : ι) :
    independentCarrierCoefficientExtension V c P hh n m α t X z v u = 0 := by
  by_cases hn0 : n = 0
  · subst n
    by_cases hh0 : hh = 0
    · simp only [independentCarrierCoefficientExtension, ite_true, ite_eq_left hh0]
      exact independentIdentityLiftCoeff_above_order m hm α t X z v u
    · simp only [independentCarrierCoefficientExtension, ite_true, ite_eq_right hh0, Pi.zero_apply]
  · by_cases hP : P ∈ V
    · simp only [independentCarrierCoefficientExtension, ite_eq_right hn0, ite_eq_left hP]
      exact (hc P hP).2.2.2.1 hh hhh n m hm α t X z v u
    · simp only [independentCarrierCoefficientExtension, ite_eq_right hn0, ite_eq_right hP, Pi.zero_apply]

theorem independentCarrierCoefficientExtension_perm_on (V : Set (Vec d))
    (c : Vec d → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (Q : Vec d → LiftOperatorData ι (fun _ => ℝ) D)
    (Ω : Vec d → Set (Vec 2))
    (hc : ∀ P ∈ V, IsLiftSequenceOn (Ω P) (Q P) sX sZ a b N R (c P)) (P : Vec d)
    (hh n m : ℕ) (hhh : hh ≤ R) (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)) :
    independentCarrierCoefficientExtension V c P hh n m (α ∘ σ) =
      independentCarrierCoefficientExtension V c P hh n m α := by
  by_cases hn0 : n = 0
  · subst n
    by_cases hh0 : hh = 0
    · simp only [independentCarrierCoefficientExtension, ite_true, ite_eq_left hh0]
      exact independentIdentityLiftCoeff_perm m α σ
    · simp only [independentCarrierCoefficientExtension, ite_true, ite_eq_right hh0, Pi.zero_apply]
  · by_cases hP : P ∈ V
    · simp only [independentCarrierCoefficientExtension, ite_eq_right hn0, ite_eq_left hP]
      exact (hc P hP).2.2.2.2.1 hh hhh n m α σ
    · simp only [independentCarrierCoefficientExtension, ite_eq_right hn0, ite_eq_right hP, Pi.zero_apply]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! A continuous periodic real field is fixed pointwise by its produced energy trace. -/

theorem realCellRawReadout_eq_periodic_field (K : ℕ) (hK : 2 ≤ K)
    (D : ℝ → RawJet2 1 ℂ) (t : ℝ) (w : TorusHk K ℂ)
    (hm : MemLp (cellValue D t) 2 (volume.restrict AVenhance.unitCube))
    (hw : torusHkValueCLM w =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t)
    (c : Vec 2 → ℝ) (hc : Continuous c) (hp : AVenhance.IsZ2Periodic c)
    (he : cellValue D t =ᵐ[volume.restrict AVenhance.unitCube] fun x => (c x : ℂ)) :
    realCellClassicalReadout (AVRegularity.CycleEvolution.cellRawTrace D t) = c := by
  rw [realCellRawReadout_high_eq K w D t hm hw]
  apply periodicCell_ae_eq_pointwise _ c
    (realClassicalLift_contDiff K 0 (by omega) _).continuous hc
    (realClassicalLift_periodic K _) hp
  filter_upwards [realClassicalLift_value_ae K hK (mapTorusHk Complex.reCLM w),
    mapTorusHk_jet_ae Complex.reCLM w (valueIndex2 K), hw, he] with x hx hy hz ht
  exact hx.trans (hy.trans (by
    change (torusHkValueCLM w x).re = c x
    rw [hz, ht, Complex.ofReal_re]))

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational AVenhance.Infra.ODE
namespace AVRegularity.EntryWeakProofs

/-! High spatial energy for the actual Galerkin sequence, with scalar source data. -/

theorem scalarRawSource_pairing (src : ℝ → Vec 2 → ℂ) (t : ℝ) (z : TorusHk 1 ℂ) :
    cellRawSourceFunctional 0 src (fun _ _ => 0) t z =
      inner ℝ (cellSourceSlice src t) (torusHkValueCLM z) := by
  simp only [cellRawSourceFunctional, cellSourceSlice_zero, PiLp.zero_apply,
    cellSourceFunctional, ContinuousLinearMap.coe_coe, sub_apply, sum_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, inner_zero_left,
    Finset.sum_const_zero, sub_zero]

theorem MolecularGalerkinLimitData.high_energy_bound {a b : ℝ} {hab : a ≤ b}
    {P : MolecularData} {src : ℝ → Vec 2 → ℂ} {initial : ComplexCellL2}
    (D : MolecularGalerkinLimitData a b hab P src (fun _ _ => 0) initial)
    (K : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ∀ t, ContDiff ℝ (K : ℕ∞) (P.v t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ t j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (S : ℝ → TorusHk K ℂ) (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hs : ∀ t, (S t).val (valueIndex2 K) = cellSourceSlice src t)
    (u₀ : TorusHk K ℂ) (hinit : initial = torusHkValueCLM u₀) :
    ∀ N t, t ∈ Icc a b →
      factorialNormSq ρ (dataFourierHighCLM N K
        (cellGalerkinValue N (extendCurve hab (D.curve N) t))).val ≤
      (factorialNormSq ρ u₀.val + ∫ s in a..b, factorialNormSq ρ (S s).val) *
        Real.exp ((1 + 4 * (∑ j : Fin (K + 1), factorialRootWeight ρ j.val *
          finiteTransportBudget (E := ℂ) K Cv j) ^ 2) * (t - a)) := by
  intro N t ht
  let y := extendCurve hab (D.curve N)
  let dy := linearRhs (fun r => cellGalerkinOperator N (dataGeneratorB P r))
    (fun r => cellGalerkinForcing N (cellRawSourceFunctional 0 src (fun _ _ => 0) r)) y
  have he : ∀ᵐ r ∂volume.restrict (Icc a b), ∀ z : CellGalerkinSpace (E := ℂ) N,
      inner ℝ (cellGalerkinValue N (dy r)) (cellGalerkinValue N z) =
        dataGeneratorForm P r (y r).val z.val +
          inner ℝ ((S r).val (valueIndex2 K)) (cellGalerkinValue N z) := by
    have h := (D.variational N).equation
    rw [uIcc_of_le hab] at h
    filter_upwards [h] with r hr
    intro z
    have hh := hr z
    change inner ℝ (cellGalerkinValue N (dy r)) (cellGalerkinValue N z) =
      dataGeneratorForm P r (y r).val z.val + cellRawSourceFunctional 0 src (fun _ _ => 0) r z.val at hh
    rw [scalarRawSource_pairing, ← hs r] at hh
    exact hh
  have hh := dataFinite_high_energy_bound hab N K ρ hρ P Cv hCv hv hp hb y dy S hS
    (D.variational N).time he t ht
  have hi : factorialNormSq ρ (dataFourierHighCLM N K (cellGalerkinValue N (y a))).val ≤
      factorialNormSq ρ u₀.val := by
    dsimp only [y]
    rw [D.initial_value N, hinit]
    exact dataFourierHigh_initial_factorial_le N K ρ u₀
  exact hh.trans (mul_le_mul_of_nonneg_right (add_le_add hi le_rfl) (Real.exp_nonneg _))

/-! Cutoff-independent high Hilbert bounds for the actual scalar-forced sequence. -/

theorem MolecularGalerkinLimitData.uniform_high_norm {a b : ℝ} {hab : a ≤ b}
    {P : MolecularData} {src : ℝ → Vec 2 → ℂ} {initial : ComplexCellL2}
    (D : MolecularGalerkinLimitData a b hab P src (fun _ _ => 0) initial)
    (K : ℕ) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ∀ t, ContDiff ℝ (K : ℕ∞) (P.v t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ t j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (S : ℝ → TorusHk K ℂ) (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hs : ∀ t, (S t).val (valueIndex2 K) = cellSourceSlice src t)
    (u₀ : TorusHk K ℂ) (hinit : initial = torusHkValueCLM u₀) :
    ∃ R : ℝ, ∀ N t, t ∈ Icc a b →
      ‖dataFourierHighCLM N K (cellGalerkinValue N (extendCurve hab (D.curve N) t))‖ ≤ R := by
  let B := factorialNormSq 1 u₀.val + ∫ s in a..b, factorialNormSq 1 (S s).val
  let C := 1 + 4 * (∑ j : Fin (K + 1), factorialRootWeight 1 j.val *
    finiteTransportBudget (E := ℂ) K Cv j) ^ 2
  have hB : 0 ≤ B := add_nonneg (factorialNormSq_nonneg _ _)
    (intervalIntegral.integral_nonneg_of_forall hab (fun _ => factorialNormSq_nonneg _ _))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let E := B * Real.exp (C * (b - a))
  have hE : 0 ≤ E := mul_nonneg hB (Real.exp_nonneg _)
  have hm : 0 < factorialWeightMin 1 K := factorialWeightMin_pos 1 (by norm_num)
  refine ⟨Real.sqrt (E / factorialWeightMin 1 K), ?_⟩
  intro N t ht
  let w := dataFourierHighCLM N K (cellGalerkinValue N (extendCurve hab (D.curve N) t))
  have he := D.high_energy_bound K 1 (by norm_num) Cv hCv hv hp hb S hS hs u₀ hinit N t ht
  have hwe : factorialNormSq 1 w.val ≤ E := he.trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hC)) hB)
  have hn : ‖w‖ ^ 2 ≤ E / factorialWeightMin 1 K := by
    apply (le_div_iff₀ hm).2
    have hl := factorialNormSq_lower 1 w.val
    change factorialWeightMin 1 K * ‖w‖ ^ 2 ≤ factorialNormSq 1 w.val at hl
    simpa only [mul_comm] using hl.trans hwe
  exact (Real.le_sqrt (norm_nonneg w) (div_nonneg hE hm.le)).2 hn

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
open scoped Matrix Matrix.Norms.Elementwise
namespace AVRegularity.EntryWeakProofs

/-! Molecular metric production uses a scale threshold fixed before the actual data. -/

theorem uniform_finite_weak_metric_eventually_elliptic (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (J : ℕ) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      ∀ base ≥ M, ∀ (Y : Vec 2) (p : ℕ → ℤ) (c : ℕ → ChainChild),
      (∀ n ≤ J, Odd (p n)) →
      (∀ n < J, IsScheduledIn D (base + 1 + n) (p (n + 1)) (p n)) →
      ∀ n ≤ J, ∀ t ∈ ocPulseWindow D.α D.q D.Λ (base + 1 + n) (p n), ∀ h ξ : Vec 2,
        let A : RealChain := ⟨base, List.ofFn (fun j : Fin (n + 1) => p j), Y,
          List.ofFn (fun j : Fin n => c j)⟩
        (3 / 4) * ∑ i, ξ i ^ 2 ≤
          ∑ i, ∑ j, (A.recenter D h).famMetric D t i j * ξ i * ξ j ∧
        ∑ i, ∑ j, (A.recenter D h).famMetric D t i j * ξ i * ξ j ≤
          (5 / 4) * ∑ i, ξ i ^ 2 := by
  obtain ⟨M, hM, hb⟩ := uniform_finite_weak_chart_eventually_close α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ J
  refine ⟨M, hM, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq
  have hΛ' : 128 ≤ D.Λ := by rw [hDΛ]; exact hΛ
  have hbD := hb D hDα hDq hDΛ hDζ hseq
  intro base hbase Y p c hp hs n hn t ht h ξ
  let A : RealChain := ⟨base, List.ofFn (fun j : Fin (n + 1) => p j), Y,
    List.ofFn (fun j : Fin n => c j)⟩
  have hgeom : A.geom D = finiteWeakChainGeom D base Y p c n :=
    (finiteWeakChainGeom_eq_chain D base Y p c n).symm
  have hl : A.slots.length = A.children.length + 1 := by simp [A]
  apply recentered_metric_ellipticity_of_backward_jacobian D A hl t h _ ξ
  intro i j
  have hτ : 0 ≤ ocTauPP D.α D.q D.Λ (base + 1 + n) :=
    (Construction.Stream.ocTauPP_pos (by omega : 1 ≤ D.Λ)).le
  have hR : 1 ≤ finiteChainWindowRadius J n := by
    unfold finiteChainWindowRadius
    have h : (0 : ℝ) ≤ ((J - n : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have ht' := weak_lift_anchor_distance D.α D.q (by omega : 1 ≤ D.Λ)
    (base + 1 + n) (p n) t ht
  have htR : |t - D.slotAnchor (base + 1 + n) (p n)| ≤
      finiteChainWindowRadius J n * ocTauPP D.α D.q D.Λ (base + 1 + n) := by
    exact ht'.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hR hτ)
  have haR : |D.slotAnchor (base + 1 + n) (p n) - D.slotAnchor (base + 1 + n) (p n)| ≤
      finiteChainWindowRadius J n * ocTauPP D.α D.q D.Λ (base + 1 + n) := by
    rw [sub_self, abs_zero]
    exact mul_nonneg (finiteChainWindowRadius_nonneg _ _) hτ
  let x := (A.geom D).1 t ((A.geom D).2.1 + h) (A.geom D).2.2
  have hbound := hbD base hbase Y p c hp hs n hn
    (D.slotAnchor (base + 1 + n) (p n)) t haR htR x
  have he := jacobian_entry_close_of_operator_norm _ x (1 / 32) hbound i j
  simpa only [x, hgeom, finiteWeakChainGeom_anchor] using he

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Literal weak eddy flux coefficient extraction keeps its quadratic response mean. -/

theorem weakEddyFlux_fluxCoeff {Dm : ℕ} (D : OCData) (m n d : ℕ) (ρ : ℝ) (hρ : ρ ≠ 0)
    (Q : LiftOperatorData (Fin 1) (fun _ => ℝ) Dm)
    (Cc : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (hd : d - 1 ≤ n - 1)
    (hs : ∀ (β : DerivativeWord2 (d - 1)) (σ : Equiv.Perm (Fin (d - 1))),
      Cc 0 (n - 1) (d - 1) (β ∘ σ) = Cc 0 (n - 1) (d - 1) β)
    (α : DerivativeWord2 (d - 1)) (t : ℝ) (y : Vec 2)
    (hv : ∀ k, Continuous (fun z => Real.sqrt Q.η * Q.v ((D.cellScaleSq m)⁻¹ * t) z k))
    (hc : Continuous (fun z => fun v : Fin 1 =>
      Cc 0 (n - 1) (d - 1) α ((D.cellScaleSq m)⁻¹ * t) (ρ⁻¹ • y) z v 0 1)) :
    fluxCoeff (weakEddyFlux D m ρ Q Cc n t) d α y = fun k =>
      (-((D.cellScaleSq m)⁻¹ *
        (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ n * ρ) * ρ ^ (d - 1)) *
      fieldCellMean (fun z => (Real.sqrt Q.η * Q.v ((D.cellScaleSq m)⁻¹ * t) z k) •
        Cc 0 (n - 1) (d - 1) α ((D.cellScaleSq m)⁻¹ * t) (ρ⁻¹ • y) z 0 0 1) := by
  let τ := (D.cellScaleSq m)⁻¹ * t
  let Y := ρ⁻¹ • y
  let f : Vec 2 → Fin 1 → ℝ := fun X => Pi.single 0 (∏ j : Fin (d - 1), (ρ • X - y) (α j))
  have he : f = fun X => ρ ^ (d - 1) • Providers.GenSem.monoField (0 : Fin 1) Y α X := by
    funext X
    dsimp only [f, Y]
    rw [scaled_word_monomial (d - 1) α ρ hρ y X]
    simp only [Providers.GenSem.monoField, ← Pi.single_smul, smul_eq_mul]
  have hlift z v : liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) τ Y z v =
      (ρ ^ (d - 1) * ((d - 1).factorial : ℝ)) *
        Cc 0 (n - 1) (d - 1) α τ Y z v 0 1 := by
    rw [he, scalarLiftApply_coarse_smul (n - 1) (Cc 0 (n - 1)) _
      (Providers.GenSem.contDiff_monoField (0 : Fin 1) Y α)]
    change ρ ^ (d - 1) * liftApply (n - 1) (Cc 0 (n - 1))
      (fun _ => Providers.GenSem.monoField (0 : Fin 1) Y α) τ Y z v = _
    rw [Providers.GenSem.liftApply_monoField hd (fun σ β => hs β σ) 0 Y α τ z v]
    ring
  funext k
  let g := fun z => (Real.sqrt Q.η * Q.v τ z k) •
    (fun v : Fin 1 => Cc 0 (n - 1) (d - 1) α τ Y z v 0 1)
  have hmean : fieldCellMean (fun z => (Real.sqrt Q.η * Q.v τ z k) •
      liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) τ Y z) =
      (ρ ^ (d - 1) * ((d - 1).factorial : ℝ)) • fieldCellMean g := by
    rw [← fieldCellMean_smul]
    apply congrArg fieldCellMean
    funext z v
    simp only [Pi.smul_apply, smul_eq_mul, g, hlift]
    ring
  have hg : Continuous g := (hv k).smul hc
  have hproj : fieldCellMean g 0 = fieldCellMean (fun z => g z 0) := by
    let L : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
    exact (L.integral_comp_comm (integrableOn_unitCube hg)).symm
  unfold fluxCoeff weakEddyFlux
  simp only [Pi.smul_apply, smul_eq_mul]
  change ((d - 1).factorial : ℝ)⁻¹ *
    (-((D.cellScaleSq m)⁻¹ *
      (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ n * ρ) *
      fieldCellMean (fun z => (Real.sqrt Q.η * Q.v τ z k) •
        liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) τ Y z) 0) = _
  rw [hmean]
  change ((d - 1).factorial : ℝ)⁻¹ *
    (-((D.cellScaleSq m)⁻¹ *
      (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ n * ρ) *
        ((ρ ^ (d - 1) * ((d - 1).factorial : ℝ)) * fieldCellMean g 0)) = _
  rw [hproj]
  have hfact : (((d - 1).factorial : ℝ)) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (d - 1)
  dsimp only [g, τ, Y]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVRegularity.EntryWeakProofs

/-! One data-independent threshold gives ellipticity uniformly over arbitrary real parameters of every scheduled chain. -/

theorem uniform_scheduled_weak_metric_eventually_elliptic (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (J : ℕ) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      ∀ (A : RealChain) (i : ℕ) (p : ℤ),
      M ≤ A.baseLevel → A.children.length ≤ J → A.ctxLevel = i →
      A.slots.length = A.children.length + 1 → A.slot = p →
      (∀ q ∈ A.slots, Odd q) →
      (∀ k : ℕ, ∀ hk : k + 1 < A.slots.length,
        IsScheduledIn D (A.baseLevel + 1 + k) (A.slots[k + 1]) (A.slots[k])) →
      ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ h ξ : Vec 2,
        (3 / 4) * ∑ k, ξ k ^ 2 ≤
          ∑ k, ∑ l, (A.recenter D h).famMetric D t k l * ξ k * ξ l ∧
        ∑ k, ∑ l, (A.recenter D h).famMetric D t k l * ξ k * ξ l ≤
          (5 / 4) * ∑ k, ξ k ^ 2 := by
  choose M hM hb using fun n => uniform_finite_weak_metric_eventually_elliptic α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ n
  let M₀ := ∑ k ∈ Finset.range (J + 1), M k
  have hle (n : ℕ) (hn : n ≤ J) : M n ≤ M₀ :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
  refine ⟨M₀, (hM 0).trans (hle 0 (Nat.zero_le _)), ?_⟩
  intro D hDα hDq hDΛ hDζ hseq A i p hbase hlength hctx hl hslot hodd hscheduled t ht h ξ
  have hi : i = A.baseLevel + 1 + A.children.length := by
    unfold RealChain.ctxLevel RealChain.lastLevel at hctx
    omega
  have ht' : t ∈ ocPulseWindow D.α D.q D.Λ (A.baseLevel + 1 + A.children.length)
      (realChainSlotSeq A A.children.length) := by
    rw [realChainSlotSeq_last A hl, hslot, ← hi]
    exact ht
  have he := hb A.children.length D hDα hDq hDΛ hDζ hseq A.baseLevel ((hle _ hlength).trans hbase) A.base
    (realChainSlotSeq A) (realChainChildSeq A)
    (fun n hn => by
      have hn' : n < A.slots.length := by omega
      unfold realChainSlotSeq
      rw [List.getD_eq_getElem _ _ hn']
      exact hodd _ (List.getElem_mem hn'))
    (fun n hn => by
      have hn' : n + 1 < A.slots.length := by omega
      unfold realChainSlotSeq
      rw [List.getD_eq_getElem _ _ hn', List.getD_eq_getElem _ _ (by omega : n < A.slots.length)]
      exact hscheduled n hn')
    A.children.length le_rfl t ht' h ξ
  simpa only [realChain_ofFn_eq A hl] using he

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Actual finite ordered-word inverses are constructed from strictly lower forcing. -/

variable {I : Type*}

theorem independent_word_inverse_family_exists (K : ℕ)
    (G : List I → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (f : List I → ℝ → Vec 2 → ℂ)
    (F : List I → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hG0 : IsCellMetric (G [])) {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hdata : ∀ w : List I, w.length ≤ K →
      cellMetricSupNorm (G w) < ⊤ ∧ Measurable (Function.uncurry (G w)) ∧
      cellUlNorm univ (f w) < ⊤ ∧ cellUlNorm univ (F w) < ⊤ ∧
      AEStronglyMeasurable (Function.uncurry (f w))
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) ∧
      AEStronglyMeasurable (Function.uncurry (F w))
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube))) :
    ∃ c : List I → ℝ → RawJet2 1 ℂ, ∀ w, w.length ≤ K →
      IsCellInverseValue ⟨G [], v, 0, 0⟩ (fun t => cellQ0 (f w t))
        (F w + independentWordMetricFlux G c w) (c w) := by
  classical
  revert hdata
  induction K with
  | zero =>
    intro hdata
    have hh := hdata [] (by simp)
    obtain ⟨D, hD, _⟩ := cellAllTimeInverse_exists_bound_ae hG0 hv (f []) (F [])
      hh.2.2.2.2.1 hh.2.2.2.2.2 hh.2.2.1 hh.2.2.2.1
    refine ⟨fun _ => D, ?_⟩
    intro w hw
    have he : w = [] := List.length_eq_zero_iff.mp (by omega)
    subst w
    simpa only [independentWordMetricFlux_nil, add_zero] using hD
  | succ n ih =>
    intro hdata
    obtain ⟨old, hold⟩ := ih (fun w hw => hdata w (hw.trans (Nat.le_succ n)))
    have hex (w : List I) (hw : w.length = n + 1) :
        ∃ D : ℝ → RawJet2 1 ℂ,
          IsCellInverseValue ⟨G [], v, 0, 0⟩ (fun t => cellQ0 (f w t))
            (F w + independentWordMetricFlux G old w) D := by
      have hh := hdata w (by omega)
      have hp := independentWordMetricFlux_finite G old w
        (fun p hp => (hdata p.1 (by
          have hl := (independentWordForcing_lengths w p hp).2.1
          omega)).1)
        (fun p hp => (hdata p.1 (by
          have hl := (independentWordForcing_lengths w p hp).2.1
          omega)).2.1)
        (fun p hp => (hold p.2 (by
          have hl := (independentWordForcing_lengths w p hp).2.2
          omega)).2.2)
        (fun p hp => (hold p.2 (by
          have hl := (independentWordForcing_lengths w p hp).2.2
          omega)).1.2.2.2.1)
      obtain ⟨D, hD, _⟩ := cellAllTimeInverse_exists_bound_ae hG0 hv (f w)
        (F w + independentWordMetricFlux G old w) hh.2.2.2.2.1
        (hh.2.2.2.2.2.add hp.1) hh.2.2.1
        ((cellUlNorm_add univ _ _ hh.2.2.2.2.2 hp.1).trans_lt
          (ENNReal.add_lt_top.mpr ⟨hh.2.2.2.1, hp.2⟩))
      exact ⟨D, hD⟩
    let c := fun w : List I => if hw : w.length = n + 1 then (hex w hw).choose else old w
    refine ⟨c, ?_⟩
    intro w hw
    have hf : independentWordMetricFlux G c w = independentWordMetricFlux G old w := by
      apply independentWordMetricFlux_congr_lower
      intro u hu
      have hn : u.length ≠ n + 1 := by omega
      simp only [c, dite_eq_right hn]
    rw [hf]
    by_cases hn : w.length = n + 1
    · simp only [c, dite_eq_left hn]
      exact (hex w hn).choose_spec
    · simp only [c, dite_eq_right hn]
      exact hold w (by omega)

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! A bounded all-time mean-zero inverse vanishes before its forcing begins. -/

theorem cellInverse_before_start_zero_ae
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D : ℝ → RawJet2 1 ℂ) (hD : IsCellInverseValue ⟨G, v, 0, 0⟩ src F D)
    (a : ℝ)
    (hs : ∀ᵐ r ∂volume.restrict (Iic a),
      src r =ᵐ[volume.restrict AVenhance.unitCube] 0)
    (hF : ∀ᵐ r ∂volume.restrict (Iic a),
      F r =ᵐ[volume.restrict AVenhance.unitCube] 0) :
    ∀ t, t ≤ a → cellValue D t =ᵐ[volume.restrict AVenhance.unitCube] cellValue 0 t := by
  have hZ := cellInverse_zero_of_inverse hD
  obtain ⟨V, hV⟩ := hv.2.1
  let K := (cellEnergyNorm univ D).toReal +
    (cellEnergyNorm univ (0 : ℝ → RawJet2 1 ℂ)).toReal
  intro t ht
  have hbound (n : ℕ) : ‖cellRawTrace D t - cellRawTrace 0 t‖ ^ 2 ≤
      Real.exp (-(4 * Real.pi ^ 2) * (n : ℝ)) * K ^ 2 := by
    have hst : t - n ≤ t := sub_le_self t (Nat.cast_nonneg n)
    have hsub : Icc (t - n) t ⊆ univ := subset_univ _
    have hpa : Icc (t - n) t ⊆ Iic a := fun _ hr => hr.2.trans ht
    have hd := cellSolution_restrict hsub ordConnected_Icc hD.1
    have hd0 := cellSolution_source_congr_sections (Icc (t - n) t) ⟨G, v, 0, 0⟩
      src 0 F 0 D
      (hs.filter_mono (ae_mono (Measure.restrict_mono hpa le_rfl)))
      (hF.filter_mono (ae_mono (Measure.restrict_mono hpa le_rfl))) hd
    have he := cellRaw_meanZero_difference_decay hst hG hv V hV 0 0
      MemLp.zero MemLp.zero D 0 hd0
      (cellSolution_restrict hsub ordConnected_Icc hZ.1)
      (fun r _ => hD.2.1 r) (fun r _ => hZ.2.1 r) t ⟨hst, le_rfl⟩
    have hn : ‖cellRawTrace D (t - n) - cellRawTrace 0 (t - n)‖ ≤ K :=
      (norm_sub_le _ _).trans (add_le_add
        (cellRawTrace_norm_le_energy D hD.1 hD.2.2 (t - n))
        (cellRawTrace_norm_le_energy 0 hZ.1 hZ.2.2 (t - n)))
    rw [show t - (t - (n : ℝ)) = n by ring] at he
    exact he.trans (mul_le_mul_of_nonneg_left
      (by simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg _) hn)
      (Real.exp_pos _).le)
  have hl : Tendsto (fun n : ℕ => Real.exp (-(4 * Real.pi ^ 2) * (n : ℝ)) * K ^ 2)
      atTop (𝓝 0) := by
    simpa only [zero_add] using cellPullback_exp_budget_tendsto_zero 0 (K ^ 2)
  have hz := le_of_tendsto_of_tendsto' tendsto_const_nhds hl hbound
  have hn : ‖cellRawTrace D t - cellRawTrace 0 t‖ = 0 := by
    nlinarith [norm_nonneg (cellRawTrace D t - cellRawTrace 0 t)]
  have he := sub_eq_zero.mp (norm_eq_zero.mp hn)
  have htrace := cellRawTrace_ae D t (hD.1.2.2.1 t (mem_univ _)).1
  rw [he] at htrace
  exact htrace.symm.trans (cellRawTrace_ae 0 t (hZ.1.2.2.1 t (mem_univ _)).1)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Actual inverse transition mixed jets spend one derivative of the joint center map. -/

theorem weak_transfer_matrix_inverse_eq_joint_slow_jacobian_inverse
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (A : RealChain)
    (hl : A.WellSlotted) (slot : ℤ) (t : ℝ) (Z : Vec 2 × Vec 2) :
    (childTransition D slot t (A.recenter D (D.eps A.ctxLevel • Z.2))
      (Z.1 + (D.eps A.ctxLevel)⁻¹ • (D.eps A.ctxLevel • Z.2)))⁻¹ =
      (jacMatrix (fun y => weakTransferCenterJoint D A slot t (Z.1, y)) Z.2)⁻¹ := by
  have hε : 0 < D.eps A.ctxLevel := Construction.Stream.ocEpsilon_pos hΛ
  let C := weakTransferCenterMap D A slot t Z.1
  have hC : ContDiff ℝ (⊤ : ℕ∞) C :=
    (weak_transfer_child_center_joint_smooth D A hl slot t).comp
      (contDiff_const.prodMk contDiff_id)
  have he : jacMatrix (fun y => weakTransferCenterJoint D A slot t (Z.1, y)) Z.2 =
      jacMatrix C (D.eps A.ctxLevel • Z.2) :=
    rescaledChart_jacMatrix (D.eps A.ctxLevel) hε C hC Z.2
  rw [he]
  exact weak_transfer_matrix_inverse_eq_center_jacobian_inverse D hζ A hl slot t
    Z.1 (D.eps A.ctxLevel • Z.2) hε.ne'

theorem weak_transfer_joint_slow_jacobian_det_one (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (A : RealChain) (hl : A.WellSlotted) (hp : Odd A.slot)
    (ha : GeomAreaPreserving (A.geom D)) (slot : ℤ) (t : ℝ) (Z : Vec 2 × Vec 2) :
    (jacMatrix (fun y => weakTransferCenterJoint D A slot t (Z.1, y)) Z.2).det = 1 := by
  have hε : 0 < D.eps A.ctxLevel := Construction.Stream.ocEpsilon_pos hΛ
  let C := weakTransferCenterMap D A slot t Z.1
  have hC : ContDiff ℝ (⊤ : ℕ∞) C :=
    (weak_transfer_child_center_joint_smooth D A hl slot t).comp
      (contDiff_const.prodMk contDiff_id)
  change (jacMatrix (rescaledChart (D.eps A.ctxLevel) C) Z.2).det = 1
  rw [rescaledChart_jacMatrix (D.eps A.ctxLevel) hε C hC]
  exact weak_transfer_center_jacobian_det_one D hΛ hζ A hl hp ha slot t Z.1 _

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev Set AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Carrier coefficient extension preserves the native inverse, including the centered ordered corrections. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d D N R sX sZ : ℕ} {a b : ℝ}

theorem independentCarrierCoefficientExtension_inverse_on (V : Set (Vec d))
    (c : Vec d → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (P : Vec d) (hP : P ∈ V)
    (Ω : Set (Vec 2)) (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (hc : IsLiftSequenceOn Ω Q sX sZ a b N R (c P)) (hh n : ℕ) (hhh : hh ≤ R)
    (hn : 1 ≤ n) (hnN : n ≤ N) (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (X : Vec 2) (hX : X ∈ Ω) :
    IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ a b 0
      (fun t z => liftCellSource Q (independentCarrierCoefficientExtension V c P) (fun _ => f) hh n t X z)
      (fun t z => liftApply n (independentCarrierCoefficientExtension V c P hh n) (fun _ => f) t X z) := by
  have hi := hc.2.2.2.2.2.2 hh hhh n hn hnN f hf X hX
  have hcn : independentCarrierCoefficientExtension V c P hh n = c P hh n := by
    simp only [independentCarrierCoefficientExtension, ite_eq_right (by omega : n ≠ 0), ite_eq_left hP]
  rw [hcn]
  apply cellFieldInverse_source_congr_on _ _ sZ a b 0 _ _ _ _ hi
  intro t ht
  funext z
  exact liftCellSource_slow_open_congr_predecessors isOpen_univ Q (c P)
    (independentCarrierCoefficientExtension V c P) (fun _ => f) hh n hn t (by
      intro p q hpq m _hm α Y _hY z v u
      have hpR : p ≤ R := by rcases hpq with hpq | ⟨rfl, _⟩ <;> omega
      exact (independentCarrierCoefficientExtension_copy_on V c P hP Ω Q hc p hpR q m α t ht Y z v u).symm)
    X (mem_univ X) z

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.EntryWeakProofs

/-! Divergence forcing preserves the centered mean in the original Galerkin curves. -/

theorem rawFluxSource_constant_pairing (src : ℝ → Vec 2 → ℂ)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (t : ℝ)
    (z : TorusHk 1 ℂ) (hz : ∀ j, cellDerivativeCLM j z = 0) :
    cellRawSourceFunctional 0 src F t z =
      inner ℝ (cellSourceSlice src t) (torusHkValueCLM z) := by
  simp only [cellRawSourceFunctional, ContinuousLinearMap.coe_coe, cellSourceFunctional,
    sub_apply, sum_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    Pi.zero_apply, star_zero, cellShiftedDerivativeCLM, mul_zero, cellScalarCLM,
    ContinuousLinearMap.lsmul_apply, zero_smul, add_apply, hz, add_zero,
    inner_zero_right, Finset.sum_const_zero, sub_zero]

theorem MolecularGalerkinLimitData.finite_flux_mean_zero {a b : ℝ} {hab : a ≤ b}
    {P : MolecularData} {src : ℝ → Vec 2 → ℂ} {initial : ComplexCellL2}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (D : MolecularGalerkinLimitData a b hab P src F initial)
    (hv : IsCellDrift P.v) (hm : cellMean initial = 0)
    (hsrc : ∀ᵐ t ∂volume.restrict (Icc a b), cellMean (cellSourceSlice src t) = 0) :
    ∀ N t, t ∈ Icc a b →
      cellMean (cellGalerkinValue N (extendCurve hab (D.curve N) t)) = 0 := by
  intro N t ht
  let y := extendCurve hab (D.curve N)
  let dy := linearRhs (fun r => cellGalerkinOperator N (dataGeneratorB P r))
    (fun r => cellGalerkinForcing N (cellRawSourceFunctional 0 src F r)) y
  have htest (z : TorusHk 1 ℂ) := cellGalerkin_full_test_primitive hab N
    (dataGeneratorB P) (fun r => cellRawSourceFunctional 0 src F r)
    y dy (D.variational N) initial (D.initial_value N) z t ht
  have hreal := htest cellH1One
  have himag := htest (cellH1Scalar Complex.I cellH1One)
  rw [molecularOne_galerkin_fixed, cellH1One_value] at hreal
  rw [molecularConstant_galerkin_fixed, cellH1Scalar_value, cellH1One_value] at himag
  have hgR (r : ℝ) : dataGeneratorForm P r (y r).val cellH1One = 0 := by
    rw [← dataComplexGenerator_re, dataComplexGenerator_one P hv]
    rfl
  have hgI (r : ℝ) : dataGeneratorForm P r (y r).val (cellH1Scalar Complex.I cellH1One) = 0 := by
    rw [← dataComplexGenerator_im, dataComplexGenerator_one P hv]
    rfl
  have hsR : ∀ᵐ r ∂volume.restrict (Icc a b), cellRawSourceFunctional 0 src F r cellH1One = 0 := by
    filter_upwards [hsrc] with r hr
    rw [rawFluxSource_constant_pairing src F r cellH1One cellH1One_derivative,
      cellH1One_value, ← cellComplexPair_re,
      cellComplexPair_one, hr]
    rfl
  have hsI : ∀ᵐ r ∂volume.restrict (Icc a b), cellRawSourceFunctional 0 src F r
      (cellH1Scalar Complex.I cellH1One) = 0 := by
    filter_upwards [hsrc] with r hr
    rw [rawFluxSource_constant_pairing src F r _ (fun j => by
      rw [cellH1Scalar_derivative, cellH1One_derivative, map_zero]),
      cellH1Scalar_value, cellH1One_value, ← cellComplexPair_im, cellComplexPair_one, hr]
    rfl
  change inner ℝ (cellGalerkinValue N (y t)) (cellConstantCLM 1) =
    inner ℝ initial (cellConstantCLM 1) +
      ∫ r in a..t, dataGeneratorForm P r (y r).val cellH1One + _ at hreal
  change inner ℝ (cellGalerkinValue N (y t)) (cellScalarCLM Complex.I (cellConstantCLM 1)) =
    inner ℝ initial (cellScalarCLM Complex.I (cellConstantCLM 1)) +
      ∫ r in a..t, dataGeneratorForm P r (y r).val (cellH1Scalar Complex.I cellH1One) + _ at himag
  have hsub : Set.uIoc a t ⊆ Icc a b := by
    rw [uIoc_of_le ht.1]
    exact fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩
  have hiR : (∫ r in a..t, dataGeneratorForm P r (y r).val cellH1One +
      cellRawSourceFunctional 0 src F r cellH1One) = 0 := by
    apply (intervalIntegral.integral_congr_ae_restrict ?_).trans (intervalIntegral.integral_zero)
    filter_upwards [ae_mono (Measure.restrict_mono hsub le_rfl) hsR] with r hr
    rw [hgR, hr]
    exact zero_add _
  have hiI : (∫ r in a..t, dataGeneratorForm P r (y r).val (cellH1Scalar Complex.I cellH1One) +
      cellRawSourceFunctional 0 src F r (cellH1Scalar Complex.I cellH1One)) = 0 := by
    apply (intervalIntegral.integral_congr_ae_restrict ?_).trans (intervalIntegral.integral_zero)
    filter_upwards [ae_mono (Measure.restrict_mono hsub le_rfl) hsI] with r hr
    rw [hgI, hr]
    exact zero_add _
  rw [hiR, add_zero] at hreal
  rw [hiI, add_zero] at himag
  rw [← cellComplexPair_re, ← cellComplexPair_re, cellComplexPair_one,
    cellComplexPair_one, hm] at hreal
  rw [← cellComplexPair_im, ← cellComplexPair_im, cellComplexPair_one,
    cellComplexPair_one, hm] at himag
  exact Complex.ext hreal himag

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Literal inverse transition and determinant use the centered slow Jacobian. -/

theorem weak_transfer_matrix_inverse_eq_centered_slow_jacobian_inverse
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (A : RealChain)
    (hl : A.WellSlotted) (slot : ℤ) (t : ℝ) (Z : Vec 2 × Vec 2) :
    (childTransition D slot t (A.recenter D (D.eps A.ctxLevel • Z.2))
      (Z.1 + (D.eps A.ctxLevel)⁻¹ • (D.eps A.ctxLevel • Z.2)))⁻¹ =
      (jacMatrix (fun y => weakTransferCenteredJoint D A slot t (Z.1, y)) Z.2)⁻¹ := by
  rw [weak_transfer_matrix_inverse_eq_joint_slow_jacobian_inverse D hΛ hζ A hl]
  rw [weak_transfer_centered_slow_jacobian D A hl slot t
    (Construction.Stream.ocEpsilon_pos hΛ).ne']

theorem weak_transfer_centered_slow_jacobian_det_one (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (A : RealChain) (hl : A.WellSlotted) (hp : Odd A.slot)
    (ha : GeomAreaPreserving (A.geom D)) (slot : ℤ) (t : ℝ) (Z : Vec 2 × Vec 2) :
    (jacMatrix (fun y => weakTransferCenteredJoint D A slot t (Z.1, y)) Z.2).det = 1 := by
  rw [← weak_transfer_centered_slow_jacobian D A hl slot t
    (Construction.Stream.ocEpsilon_pos hΛ).ne']
  exact weak_transfer_joint_slow_jacobian_det_one D hΛ hζ A hl hp ha slot t Z

/-! Literal inverse transfers depend only on the native geometry and scheduling metadata. -/

theorem weak_transfer_inverse_geometry_congr (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (A B : RealChain) (hA : A.WellSlotted) (hB : B.WellSlotted)
    (hctx : A.ctxLevel = B.ctxLevel) (hslot : A.slot = B.slot) (hgeom : A.geom D = B.geom D)
    (slot : ℤ) (t : ℝ) (z h : Vec 2) :
    (childTransition D slot t (A.recenter D (D.eps A.ctxLevel • h))
      (z + (D.eps A.ctxLevel)⁻¹ • (D.eps A.ctxLevel • h)))⁻¹ =
    (childTransition D slot t (B.recenter D (D.eps B.ctxLevel • h))
      (z + (D.eps B.ctxLevel)⁻¹ • (D.eps B.ctxLevel • h)))⁻¹ := by
  rw [weak_transfer_matrix_inverse_eq_centered_slow_jacobian_inverse D hΛ hζ A hA slot t (z, h),
    weak_transfer_matrix_inverse_eq_centered_slow_jacobian_inverse D hΛ hζ B hB slot t (z, h)]
  have he : weakTransferCenteredJoint D A slot t = weakTransferCenteredJoint D B slot t := by
    funext Z
    unfold weakTransferCenteredJoint
    rw [hgeom, hctx, hslot]
  rw [he]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! The literal physical slow-flux cell mean retains its individual matrix-entry budget. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def normalizedLiftFluxMeanComponentReserve (H : ℕ)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (f : ℝ → Vec 2 → ι → ℝ)
    (hh n : ℕ) (A : Vec 2 →L[ℝ] ℝ) (v : ι) (k : Fin 2)
    (QA : ∀ u, JointSourceReserve H (fun t z Y => ((Real.exp (A Y))⁻¹ • liftFluxX Q Cc f hh n t Y z k) u)) :
    JointSourceReserve H (fun t _ Y => (Real.exp (A Y))⁻¹ • fieldCellMean (fun z => liftFluxX Q Cc f hh n t Y z k) v) := by
  let Qwhole := jointSourcePiReserve H
    (fun u t z Y => ((Real.exp (A Y))⁻¹ • liftFluxX Q Cc f hh n t Y z k) u) QA
  have he : (fun t (_ : Vec 2) Y => fieldCellMean
      (fun z => ((Real.exp (A Y))⁻¹ • liftFluxX Q Cc f hh n t Y z k) v)) =
      fun t (_ : Vec 2) Y => (Real.exp (A Y))⁻¹ • fieldCellMean (fun z => liftFluxX Q Cc f hh n t Y z k) v := by
    funext t z Y
    have hp := fieldCellMean_clm
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) v)
      (Qwhole.fast_contDiff t Y).continuous
    change fieldCellMean (fun z => ((Real.exp (A Y))⁻¹ • liftFluxX Q Cc f hh n t Y z k) v) =
      fieldCellMean (fun z => ((Real.exp (A Y))⁻¹ • liftFluxX Q Cc f hh n t Y z k)) v at hp
    rw [hp]
    simp only [fieldCellMean_smul, Pi.smul_apply]
  exact (QA v).mean.congrSource he

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! Actual mean-zero inverse traces give mean-zero classical higher readouts. -/

theorem realHigherCarrier_inverse_mean_zero (K : ℕ) (hK : 2 ≤ K)
    (C : CellCoefficients) (f : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D : ℝ → RawJet2 1 ℂ) (hD : IsCellInverseValue C f F D)
    (t : ℝ) (w : TorusHk K ℂ)
    (hw : torusHkValueCLM w =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t) :
    fieldCellMean (realClassicalLift K (mapTorusHk Complex.reCLM w)) = 0 := by
  let _ : IsFiniteMeasure (volume.restrict AVenhance.unitCube) :=
    ⟨by rw [Measure.restrict_apply_univ, cellCube_volume_one]; exact ENNReal.one_lt_top⟩
  have hm := (hD.1.2.2.1 t (mem_univ t)).1
  have he : realClassicalLift K (mapTorusHk Complex.reCLM w) =ᵐ[
      volume.restrict AVenhance.unitCube] fun z => (cellValue D t z).re := by
    filter_upwards [realClassicalLift_value_ae K hK (mapTorusHk Complex.reCLM w),
      mapTorusHk_jet_ae Complex.reCLM w (valueIndex2 K), hw] with z hz hy hx
    exact hz.trans (hy.trans (congrArg Complex.re hx))
  change (∫ z in AVenhance.unitCube, realClassicalLift K (mapTorusHk Complex.reCLM w) z) = 0
  rw [integral_congr_ae he]
  have hmap : (∫ z in AVenhance.unitCube, (cellValue D t z).re) = (cellMean (cellValue D t)).re :=
    Complex.reCLM.integral_comp_comm (hm.integrable (by norm_num))
  rw [hmap]
  rw [hD.2.1 t, Complex.zero_re]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Genuine triangular word inverses inherit the actual source's zero past. -/

variable {I : Type*}

theorem independent_flux_list_past_zero (l : List I)
    (F : I → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (a : ℝ)
    (hz : ∀ i ∈ l, ∀ᵐ t ∂volume.restrict (Iic a),
      F i t =ᵐ[volume.restrict AVenhance.unitCube] 0) :
    ∀ᵐ t ∂volume.restrict (Iic a),
      (l.map F).sum t =ᵐ[volume.restrict AVenhance.unitCube] 0 := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have ht := ih (fun j hj => hz j (by simp [hj]))
    filter_upwards [hz i (by simp), ht] with t hi hl
    filter_upwards [hi, hl] with z hiz hlz
    simp only [List.map_cons, List.sum_cons, Pi.add_apply]
    rw [hiz, hlz]
    exact zero_add _

theorem independent_word_inverse_before_start_zero (K : ℕ)
    (G : List I → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (f : List I → ℝ → Vec 2 → ℂ)
    (F : List I → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (c : List I → ℝ → RawJet2 1 ℂ)
    (hG : IsCellMetric (G [])) {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hsol : ∀ w, w.length ≤ K → IsCellInverseValue ⟨G [], v, 0, 0⟩
      (fun t => cellQ0 (f w t)) (F w + independentWordMetricFlux G c w) (c w))
    (a : ℝ)
    (hf : ∀ w, w.length ≤ K → ∀ᵐ t ∂volume.restrict (Iic a),
      f w t =ᵐ[volume.restrict AVenhance.unitCube] 0)
    (hF : ∀ w, w.length ≤ K → ∀ᵐ t ∂volume.restrict (Iic a),
      F w t =ᵐ[volume.restrict AVenhance.unitCube] 0) :
    ∀ w, w.length ≤ K → ∀ t, t ≤ a →
      cellValue (c w) t =ᵐ[volume.restrict AVenhance.unitCube] 0 := by
  intro w hw
  generalize he : w.length = n
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
    have hs : ∀ᵐ t ∂volume.restrict (Iic a), cellQ0 (f w t) =ᵐ[
        volume.restrict AVenhance.unitCube] 0 := by
      filter_upwards [hf w hw] with t ht
      filter_upwards [cellQ0_congr_ae (f w t) 0 ht] with z hz
      rw [hz]
      simp [cellQ0, cellMean]
    have hj := independent_flux_list_past_zero (independentWordForcing w)
      (fun p => cellMetricFlux (G p.1) (c p.2)) a (fun p hp => by
        have hl := (independentWordForcing_lengths w p hp).2.2
        have hk : p.2.length ≤ K := by omega
        exact cellSolution_past_zero_metric_flux _ (hsol p.2 hk).1 a
          (ih p.2.length (by omega) p.2 hk rfl) (G p.1))
    have hsum : ∀ᵐ t ∂volume.restrict (Iic a),
        (F w + independentWordMetricFlux G c w) t =ᵐ[volume.restrict AVenhance.unitCube] 0 := by
      filter_upwards [hF w hw, hj] with t ht hu
      filter_upwards [ht, hu] with z hz hzz
      change F w t z + independentWordMetricFlux G c w t z = 0
      change independentWordMetricFlux G c w t z = 0 at hzz
      rw [hz, hzz]
      exact zero_add _
    intro t ht
    simpa only [cellValue, Pi.zero_apply] using
      cellInverse_before_start_zero_ae hG hv _ _ (c w) (hsol w hw) a hs hsum t ht

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! The exact full planar triangular difference equation, including all metric perturbation terms. -/

variable {I : Type*}

theorem independent_word_difference_inverse_value
    (G H : List I → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (f g : List I → ℝ → Vec 2 → ℂ)
    (F F' : List I → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D E : List I → ℝ → RawJet2 1 ℂ) (α : List I) (r : ℝ)
    (hGsym : ∀ t x, (G [] t x).IsSymm) (hHsym : ∀ t x, (H [] t x).IsSymm)
    (hD : IsCellInverseValue ⟨G [], v, 0, 0⟩ (f α)
      (F α + independentWordMetricFlux G D α) (D α))
    (hE : IsCellInverseValue ⟨H [], v, 0, 0⟩ (g α)
      (F' α + independentWordMetricFlux H E α) (E α)) :
    IsCellInverseValue ⟨G [], v, 0, 0⟩ (r • (g α - f α))
      (((r • (F' α - F α) + independentWordMetricFlux (fun β => r • (H β - G β)) E α) +
        cellMetricFlux (r • (H [] - G [])) (E α)) +
          independentWordMetricFlux G (fun β => r • (E β - D β)) α)
      (r • (E α - D α)) := by
  have hc := cellInverse_metric_change (G []) (H []) v (g α)
    (F' α + independentWordMetricFlux H E α) (E α) hGsym hHsym hE
  have hd := cellInverse_smul (cellInverse_sub hD hc) r
  have heq :
      r • (F' α + independentWordMetricFlux H E α + cellMetricFlux (H [] - G []) (E α) -
        (F α + independentWordMetricFlux G D α)) =
      (((r • (F' α - F α) + independentWordMetricFlux (fun β => r • (H β - G β)) E α) +
        cellMetricFlux (r • (H [] - G [])) (E α)) +
          independentWordMetricFlux G (fun β => r • (E β - D β)) α) := by
    rw [show F' α + independentWordMetricFlux H E α + cellMetricFlux (H [] - G []) (E α) -
        (F α + independentWordMetricFlux G D α) =
      (F' α - F α) + (independentWordMetricFlux H E α - independentWordMetricFlux G D α) +
        cellMetricFlux (H [] - G []) (E α) by abel]
    rw [smul_add, smul_add, independentWordMetricFlux_quotient_split, ← cellMetricFlux_smul_metric]
    abel
  rw [heq] at hd
  exact hd

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter
open scoped Topology
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.EntryWeakProofs

/-! Every closed-time molecular trace retains the spatial Sobolev order of the data. -/

theorem MolecularGalerkinLimitData.higher_trace {a b : ℝ} {hab : a ≤ b}
    {P : MolecularData} {src : ℝ → Vec 2 → ℂ} {initial : ComplexCellL2}
    (D : MolecularGalerkinLimitData a b hab P src (fun _ _ => 0) initial)
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (K : ℕ) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ∀ t, ContDiff ℝ (K : ℕ∞) (P.v t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ t j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (S : ℝ → TorusHk K ℂ) (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hs : ∀ t, (S t).val (valueIndex2 K) = cellSourceSlice src t)
    (u₀ : TorusHk K ℂ) (hinit : initial = torusHkValueCLM u₀)
    (u : ℝ → ComplexCellL2) (hu : CellWeakHilbertCurve a b u D.limit D.dualState)
    (hi : u a = initial) :
    ∀ t ∈ Icc a b, ∃ w : TorusHk K ℂ, torusHkValueCLM w = u t := by
  obtain ⟨R, hR⟩ := D.uniform_high_norm K Cv hCv hv hp hb S hS hs u₀ hinit
  intro t ht
  let v := fun n => dataFourierHighCLM (D.subsequence n) K
    (cellGalerkinValue (D.subsequence n) (extendCurve hab (D.curve (D.subsequence n)) t))
  refine higherTrace_exists_of_bounded_moments K v (u t) R
    (fun n => hR (D.subsequence n) t ht) (fun z => ?_)
  have hh := D.trace_moments_tendsto hsrc MemLp.zero u hu hi z t ht
  simpa only [v, dataFourierHigh_value] using hh

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! Uniform higher energy for the actual centered molecular Galerkin sequence with divergence forcing. -/

theorem MolecularGalerkinLimitData.uniform_ul_flux_energy_bound {a b : ℝ} {hab : a ≤ b}
    {P : MolecularData} {src : ℝ → Vec 2 → ℂ} {initial : ComplexCellL2}
    {flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (D : MolecularGalerkinLimitData a b hab P src flux initial)
    (hdiv : IsCellDrift P.v) (hm : cellMean initial = 0)
    (hsrc : ∀ᵐ t ∂volume.restrict (Icc a b), cellMean (cellSourceSlice src t) = 0)
    (K : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ∀ t, ContDiff ℝ (K : ℕ∞) (P.v t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ t j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (S : ℝ → TorusHk K ℂ) (hs : ∀ᵐ t ∂volume.restrict (Icc a b),
      (S t).val (valueIndex2 K) = cellSourceSlice src t)
    (F : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ)))
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : MemLp F 2 (volume.restrict (Icc a b)))
    (hf : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ j,
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).compLpL
        2 (volume.restrict AVenhance.unitCube)) ((F t).val (valueIndex2 K)) =
          cellSourceSlice (fun s x => flux s x j) t)
    (u₀ : TorusHk K ℂ) (hinit : initial = torusHkValueCLM u₀)
    (hsmall : (∑ j : Fin (K + 1), factorialRootWeight ρ j.val *
      finiteTransportBudget (E := ℂ) K Cv j) ≤ 1 / 8)
    (B : ℝ) (hB : 0 ≤ B)
    (hshort : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → t - s ≤ 1 →
      (∫ r in s..t, 4 * (factorialNormSq ρ (S r).val + factorialNormSq ρ (F r).val)) ≤ B) :
    ∀ N t, t ∈ Icc a b →
      factorialNormSq ρ (dataFourierHighCLM N K
        (cellGalerkinValue N (extendCurve hab (D.curve N) t))).val ≤
          factorialNormSq ρ u₀.val + B / (1 - Real.exp (-(1 / 2))) + B := by
  intro N t ht
  let y := extendCurve hab (D.curve N)
  let dy := linearRhs (fun r => cellGalerkinOperator N (dataGeneratorB P r))
    (fun r => cellGalerkinForcing N (cellRawSourceFunctional 0 src flux r)) y
  have he : ∀ᵐ r ∂volume.restrict (Icc a b), ∀ z : CellGalerkinSpace (E := ℂ) N,
      inner ℝ (cellGalerkinValue N (dy r)) (cellGalerkinValue N z) =
        dataGeneratorForm P r (y r).val z.val +
          inner ℝ ((S r).val (valueIndex2 K)) (cellGalerkinValue N z) -
          ∑ j : Fin 2, inner ℝ
            (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).compLpL
              2 (volume.restrict AVenhance.unitCube)) ((F r).val (valueIndex2 K)))
            (cellDerivativeCLM j z.val) := by
    have h := (D.variational N).equation
    rw [uIcc_of_le hab] at h
    filter_upwards [h, hs, hf] with r hr hsr hfr
    intro z
    have hh := hr z
    change inner ℝ (cellGalerkinValue N (dy r)) (cellGalerkinValue N z) =
      dataGeneratorForm P r (y r).val z.val + cellRawSourceFunctional 0 src flux r z.val at hh
    have hz : cellGalerkinValue N z = torusHkValueCLM z.val := rfl
    rw [hz] at hh ⊢
    simpa only [cellRawSourceFunctional, ContinuousLinearMap.coe_coe,
      cellSourceFunctional, sub_apply, sum_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, Pi.zero_apply, star_zero, cellShiftedDerivative_zero_apply,
      ← hsr, hfr, add_sub_assoc] using hh
  have hh := dataFinite_uniform_ul_flux_energy hab N K ρ hρ P Cv hCv hv hp hb y dy S F hS hF
    (D.variational N).time he (D.finite_flux_mean_zero hdiv hm hsrc N) hsmall B hB hshort t ht
  have hi : factorialNormSq ρ (dataFourierHighCLM N K (cellGalerkinValue N (y a))).val ≤
      factorialNormSq ρ u₀.val := by
    dsimp only [y]
    rw [D.initial_value N, hinit]
    exact dataFourierHigh_initial_factorial_le N K ρ u₀
  have hh' : factorialNormSq ρ (dataFourierHighCLM N K
      (cellGalerkinValue N (y t))).val ≤
      factorialNormSq ρ (dataFourierHighCLM N K (cellGalerkinValue N (y a))).val +
        B / (1 - Real.exp (-(1 / 2))) + B := by
    simpa only [dataWeightedFourierCLM_apply, factorialWeightedJet_normSq] using hh
  exact hh'.trans (add_le_add (add_le_add hi le_rfl) le_rfl)

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational AVenhance.Infra.ODE
namespace AVRegularity.EntryWeakProofs

/-! Uniform higher Sobolev norm for the molecular sequence with scalar and flux forcing. -/

theorem MolecularGalerkinLimitData.uniform_ul_flux_norm_bound {a b : ℝ} {hab : a ≤ b}
    {P : MolecularData} {src : ℝ → Vec 2 → ℂ} {initial : ComplexCellL2}
    {flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (D : MolecularGalerkinLimitData a b hab P src flux initial)
    (hdiv : IsCellDrift P.v) (hm : cellMean initial = 0)
    (hsrc : ∀ᵐ t ∂volume.restrict (Icc a b), cellMean (cellSourceSlice src t) = 0)
    (K : ℕ) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ∀ t, ContDiff ℝ (K : ℕ∞) (P.v t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ t j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (S : ℝ → TorusHk K ℂ) (hs : ∀ᵐ t ∂volume.restrict (Icc a b),
      (S t).val (valueIndex2 K) = cellSourceSlice src t)
    (F : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ)))
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : MemLp F 2 (volume.restrict (Icc a b)))
    (hf : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ j,
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).compLpL
        2 (volume.restrict AVenhance.unitCube)) ((F t).val (valueIndex2 K)) =
          cellSourceSlice (fun s x => flux s x j) t)
    (u₀ : TorusHk K ℂ) (hinit : initial = torusHkValueCLM u₀)
    (hsmall : (∑ j : Fin (K + 1), factorialRootWeight 1 j.val *
      finiteTransportBudget (E := ℂ) K Cv j) ≤ 1 / 8)
    (B : ℝ) (hB : 0 ≤ B)
    (hshort : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → t - s ≤ 1 →
      (∫ r in s..t, 4 * (factorialNormSq 1 (S r).val + factorialNormSq 1 (F r).val)) ≤ B) :
    ∀ N t, t ∈ Icc a b →
      ‖dataFourierHighCLM N K (cellGalerkinValue N (extendCurve hab (D.curve N) t))‖ ≤
        Real.sqrt ((factorialNormSq 1 u₀.val + B / (1 - Real.exp (-(1 / 2))) + B) /
          factorialWeightMin 1 K) := by
  intro N t ht
  let w := dataFourierHighCLM N K (cellGalerkinValue N (extendCurve hab (D.curve N) t))
  have he := D.uniform_ul_flux_energy_bound hdiv hm hsrc K 1 (by norm_num) Cv hCv
    hv hp hb S hs F hS hF hf u₀ hinit hsmall B hB hshort N t ht
  have hw := factorialNormSq_lower 1 w.val
  have hmin : 0 < factorialWeightMin 1 K := factorialWeightMin_pos 1 (by norm_num)
  have hden : 0 < 1 - Real.exp (-(1 / 2 : ℝ)) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hE : 0 ≤ factorialNormSq 1 u₀.val + B / (1 - Real.exp (-(1 / 2))) + B :=
    add_nonneg (add_nonneg (factorialNormSq_nonneg _ _) (div_nonneg hB hden.le)) hB
  apply (Real.le_sqrt (norm_nonneg _) (div_nonneg hE hmin.le)).2
  apply (le_div_iff₀ hmin).2
  change factorialWeightMin 1 K * ‖w‖ ^ 2 ≤ factorialNormSq 1 w.val at hw
  simpa only [mul_comm] using hw.trans he

end AVRegularity.EntryWeakProofs
end
