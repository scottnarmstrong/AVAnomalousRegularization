-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.Buffer.OrderZeroPhysicalWeakIdentity
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
public import AVRegularity.Construction.Preservation.Buffer.ShiftedEnergyEndpoint
public import AVRegularity.KernelEnergy.TorusKernelFiniteTraceLimit
public import AVRegularity.CycleJoint.ReferencePhysicalSpatialSmooth
public import AVRegularity.Definitions.Construction.ScheduleFloor
import AVenhance.Infra.Construction.StreamAdmissible

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! The original native certificate bounds the dimensional slow/fast coefficient. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_dimensional_flux_diagonal_bounds
    {G : GenStage D hr Dm bw j₀} {k : InvConsts} {M : ℕ}
    (hG : G.IsContextCertified k) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1))
    (dom : G.fam.Domain) (N : CompIn G.comps → ℕ)
    (hs : G.fam.IsSmoothOn dom (D.eps (G.level - 1)) N)
    (p : OddSlot) (A : Set ℝ) (hAP : A ⊆ ocPulseWindow D.α D.q D.Λ G.level p.1)
    (hdom : ∀ t ∈ A,
      ∀ Y : Vec 2, (t, Y) ∈ dom p (G.actual p))
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (c : Fin 2)
    (hm : 0 ≤ compReserve k v.1) (hm2 : compReserve k v.1 ≤ 2)
    (ν e : ℝ) (n : ℕ) (hn : n ≤ N v) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ t ∈ A, ∀ j ≤ n, ∀ Y : Vec 2,
        ‖iteratedFDeriv ℝ j (fun X : Vec 2 =>
          G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p)
            v u γ d I t X (e⁻¹ • X) c) Y‖ ≤ C j := by
  obtain ⟨C, hC, hbound⟩ := contextCertified_native_flux_diagonal_bounds
    hG hpar hi hj hb hε p v u γ d I c hm hm2 e⁻¹ n
  obtain ⟨_, f, _, _, _, _, he, _⟩ :=
    contextCertified_exists_native_complex_bound hG hi hj hb hε p v u γ d I c hm hm2
  refine ⟨fun j => ‖ν * e ^ (d - 2)‖ * C j,
    fun j => mul_nonneg (norm_nonneg _) (hC j), ?_⟩
  intro t ht j hjn Y
  let sf : Vec 2 → ℝ := fun X => G.fam.flux p
    (nativeStageContext G hi hj p X) v u γ d I t 0 (e⁻¹ • X) c
  have hraw := CycleWords.molecular_joint_contDiff G.fam dom
    (D.eps (G.level - 1)) hε.ne' N hs p (G.actual p) t (hdom t ht) v u γ d I
  have hreg : ContDiff ℝ (n : ℕ∞) (fun X : Vec 2 =>
      G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p)
        v u γ d I t X (e⁻¹ • X) c) := by
    have hh := (hraw.comp ((contDiff_id.const_smul (D.eps (G.level - 1))⁻¹).prodMk
      (contDiff_id.const_smul e⁻¹))).const_smul (ν * e ^ (d - 2))
    have hhscalar : ContDiff ℝ (N v : ℕ∞) (fun X : Vec 2 =>
        G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p)
          v u γ d I t X (e⁻¹ • X) c) :=
      (ContinuousLinearMap.proj c : Vec 2 →L[ℝ] ℝ).contDiff.comp hh
    exact hhscalar.of_le (by exact_mod_cast hn)
  have heq : (fun X : Vec 2 => G.fam.dimFlux ν e (D.eps (G.level - 1)) p
      (G.actual p) v u γ d I t X (e⁻¹ • X) c) =
      fun X => (ν * e ^ (d - 2)) * sf X := by
    funext X
    exact actual_native_dimFlux_eq G hi hj p (hnat.2.2.1 p) v u γ d I c t f
      (fun ctx X z => he ctx t (hAP ht) X z) hε.ne' ν e X (e⁻¹ • X)
  rw [heq] at hreg ⊢
  by_cases ha : ν * e ^ (d - 2) = 0
  · simp only [ha, zero_mul, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, le_refl]
  · have hsreg : ContDiff ℝ (n : ℕ∞) sf := by
      have hh := hreg.const_smul (ν * e ^ (d - 2))⁻¹
      simpa only [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ ha, one_mul] using hh
    change ‖iteratedFDeriv ℝ j (fun X => (ν * e ^ (d - 2)) • sf X) Y‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' (hsreg.contDiffAt.of_le (by exact_mod_cast hjn)),
      norm_smul]
    exact mul_le_mul_of_nonneg_left (hbound t (hAP ht) j hjn Y) (norm_nonneg _)

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance
namespace AVRegularity.Construction.Preservation.Buffer

/-! The incoming native piece has exactly the background flow inverse and Jacobian. -/

open CycleJointProofs CycleReference
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_material_eq_homeomorph {G : GenStage D hr Dm bw j₀} {M : ℕ}
    (hnat : G.IsNatural M) (p : OddSlot) (t : ℝ) :
    (G.fam.piece p).material t =
      streamFlowHomeomorph (D.hΦ (G.level - 1)) t (D.slotAnchor G.level p.1) := by
  apply Homeomorph.ext
  intro x
  exact congrFun ((hnat.1 p).2.2.2.2 t) x

theorem native_inverse_material_eq_flow {G : GenStage D hr Dm bw j₀} {M : ℕ}
    (hnat : G.IsNatural M) (p : OddSlot) (t : ℝ) :
    ⇑((G.fam.piece p).material t).symm =
      fun x => streamFlow (D.Φ (G.level - 1)) (D.hΦ (G.level - 1))
        (D.slotAnchor G.level p.1) x t := by
  rw [native_material_eq_homeomorph hnat p t]
  rfl

theorem native_inverse_jacobian_eq_natural {G : GenStage D hr Dm bw j₀} {M : ℕ}
    (hnat : G.IsNatural M) (p : OddSlot) (t : ℝ) :
    chartInvJacobian ⇑((G.fam.piece p).material t).symm =
      naturalPreparationJacobian (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1) t := by
  funext x
  rw [chartInvJacobian_homeomorph_symm ((G.fam.piece p).material t)
    (((G.fam.piece p).material_smooth t).differentiable (by simp))
    (((G.fam.piece p).material_symm_smooth t).differentiable (by simp)),
    native_inverse_material_eq_flow hnat p t]
  have hf := (hnat.1 p).2.2.2.2 t
  rw [hf]
  rfl

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Actual dimensional native flux sampled by the stage flow has uniform spatial jets. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_dimensional_flux_sampled_bounds
    {G : GenStage D hr Dm bw j₀} {k : InvConsts} {M : ℕ}
    (hG : G.IsContextCertified k) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1))
    (dom : G.fam.Domain) (N : CompIn G.comps → ℕ)
    (hs : G.fam.IsSmoothOn dom (D.eps (G.level - 1)) N)
    (p : OddSlot) (A : Set ℝ) (hAP : A ⊆ ocPulseWindow D.α D.q D.Λ G.level p.1)
    (hdom : ∀ t ∈ A,
      ∀ Y : Vec 2, (t, Y) ∈ dom p (G.actual p))
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (c : Fin 2)
    (hm : 0 ≤ compReserve k v.1) (hm2 : compReserve k v.1 ≤ 2)
    (ν e : ℝ) (n : ℕ) (hn : n ≤ N v)
    (T : Set ℝ) (hT : IsCompact T)
    (hAT : A ⊆ T) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ t ∈ A, ∀ j ≤ n, ∀ Y : Vec 2,
        ‖iteratedFDeriv ℝ j (fun X : Vec 2 =>
          G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p)
            v u γ d I t
            (streamFlow (D.Φ (G.level - 1)) (D.hΦ (G.level - 1))
              (D.slotAnchor G.level p.1) X t)
            (e⁻¹ • streamFlow (D.Φ (G.level - 1)) (D.hΦ (G.level - 1))
              (D.slotAnchor G.level p.1) X t) c) Y‖ ≤ C j := by
  obtain ⟨C, hC, hbnd⟩ := native_dimensional_flux_diagonal_bounds hG hpar hnat
    hi hj hb hε dom N hs p A hAP hdom v u γ d I c hm hm2 ν e n hn
  apply native_flow_pullback_jet_bounds (D.hΦ (G.level - 1))
    (D.slotAnchor G.level p.1) T hT
    A hAT n
    (fun t X => G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p)
      v u γ d I t X (e⁻¹ • X) c) _ C hC hbnd
  intro t ht
  exact (dimensional_flux_diagonal_contDiff G.fam dom ν e (D.eps (G.level - 1))
    hε.ne' N hs p (G.actual p) t (hdom t ht) v u γ d I c).of_le (by exact_mod_cast hn)

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.CycleReference AVRegularity.CycleJointProofs
namespace AVRegularity.Construction.Preservation.Buffer

/-! The actual weighted native sample has uniform scalar budgets on the working window. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

def nativeWeightedSampledFlux (G : GenStage D hr Dm bw j₀) (ν e : ℝ)
    (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (t : ℝ) (X : Vec 2) : Vec 2 :=
  G.fam.weight p t • G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I t
    (streamFlow (D.Φ (G.level - 1)) (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1) X t)
    (e⁻¹ • streamFlow (D.Φ (G.level - 1)) (D.hΦ (G.level - 1))
      (D.slotAnchor G.level p.1) X t)

theorem native_weighted_sampled_scalar_budgets
    {G : GenStage D hr Dm bw j₀} {k : InvConsts} {M : ℕ}
    (hG : G.IsContextCertified k) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural M)
    (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level) (hb : 0 < bw)
    (hε : 0 < D.eps (G.level - 1)) (a b mres : ℝ) (N : CompIn G.comps → ℕ)
    (hs : G.fam.IsSmoothOn (G.innerDomain (Set.Icc a b) mres) (D.eps (G.level - 1)) N)
    (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u)
    (hm : 0 ≤ compReserve k v.1) (hm2 : compReserve k v.1 ≤ 2)
    (ν e ρ : ℝ) (hρ : 0 ≤ ρ) (n : ℕ) (hn : n ≤ N v) :
    ∃ MB : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ,
      (∀ d I, 0 ≤ MB d I) ∧
      (∀ t ∈ Set.Icc a b, ∀ d I c, ContDiff ℝ (n : ℕ)
        (fun X => nativeWeightedSampledFlux G ν e p v u γ d I t X c)) ∧
      ∀ t ∈ Set.Icc a b, ∀ d I c j, j ≤ n → ∀ X,
        ρ ^ j * ‖iteratedFDeriv ℝ j
          (fun Y => nativeWeightedSampledFlux G ν e p v u γ d I t Y c) X‖ ≤ MB d I := by
  let W := Set.Icc a b
  let A := W ∩ ocPulseWindow D.α D.q D.Λ G.level p.1
  let raw := fun d (I : DerivativeWord2 (d - 1)) t X =>
    G.fam.dimFlux ν e (D.eps (G.level - 1)) p (G.actual p) v u γ d I t
      (streamFlow (D.Φ (G.level - 1)) (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1) X t)
      (e⁻¹ • streamFlow (D.Φ (G.level - 1)) (D.hΦ (G.level - 1))
        (D.slotAnchor G.level p.1) X t)
  have hdom (t : ℝ) (ht : t ∈ A) (Y : Vec 2) :
      (t, Y) ∈ G.innerDomain W mres p (G.actual p) := by
    apply G.innerDomain_native W mres p (hnat.2.2.1 p) hi hj t _ Y
    exact ⟨by rw [(hnat.1 p).2.1]; exact ht.2, ht.1⟩
  have hraw (d : ℕ) (I : DerivativeWord2 (d - 1)) (t : ℝ) (ht : t ∈ A) (c : Fin 2) :
      ContDiff ℝ (n : ℕ) (fun X => raw d I t X c) :=
    (dimensional_flux_flow_sample_contDiff G.fam (G.innerDomain W mres) ν e
      (D.eps (G.level - 1)) hε.ne' N hs p (G.actual p) t (hdom t ht) v u γ d I c
      (D.Φ (G.level - 1)) (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1)).of_le
      (by exact_mod_cast hn)
  have hz (t : ℝ) (ht : t ∉ A) (hW : t ∈ W) : G.fam.weight p t = 0 := by
    apply G.fam.weight_zero p t
    intro hout
    apply ht
    exact ⟨hW, by rw [← (hnat.1 p).2.1]; exact hout⟩
  have hreg (t : ℝ) (ht : t ∈ W) (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2) :
      ContDiff ℝ (n : ℕ) (fun X => nativeWeightedSampledFlux G ν e p v u γ d I t X c) := by
    change ContDiff ℝ (n : ℕ) (fun X => G.fam.weight p t • raw d I t X c)
    by_cases h : t ∈ A
    · exact (hraw d I t h c).const_smul _
    · simp only [hz t h ht, zero_smul]
      exact contDiff_const
  have hex (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2) :
      ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∀ t ∈ W, ∀ j ≤ n, ∀ X,
        ‖iteratedFDeriv ℝ j (fun Y => nativeWeightedSampledFlux G ν e p v u γ d I t Y c) X‖ ≤ C j := by
    obtain ⟨C, hC, hbound⟩ := native_dimensional_flux_sampled_bounds hG hpar hnat hi hj hb hε
      (G.innerDomain W mres) N hs p A (fun _ ht => ht.2) hdom v u γ d I c hm hm2 ν e n hn
      W isCompact_Icc (fun _ ht => ht.1)
    refine ⟨C, hC, ?_⟩
    intro t ht j hjn X
    change ‖iteratedFDeriv ℝ j (fun Y => G.fam.weight p t • raw d I t Y c) X‖ ≤ C j
    by_cases h : t ∈ A
    · rw [iteratedFDeriv_const_smul_apply' ((hraw d I t h c).contDiffAt.of_le
        (by exact_mod_cast hjn)), norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right (family_weight_abs_le_one G.fam p t) (norm_nonneg _)).trans
        (by rw [one_mul]; exact hbound t h j hjn X)
    · simp only [hz t h ht, zero_smul, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
      exact hC j
  have hbudget (d : ℕ) (I : DerivativeWord2 (d - 1)) :=
    scalar_component_common_scaled_jet_budget W n ρ hρ
      (fun t X => nativeWeightedSampledFlux G ν e p v u γ d I t X) (hex d I)
  choose MB hMB hbudget using hbudget
  exact ⟨MB, hMB, hreg, fun t ht d I c j hjn X => hbudget d I t ht c j hjn X⟩

end AVRegularity.Construction.Preservation.Buffer
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Joint measurability of the incoming native samples along its actual inverse flow. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_weighted_sample_joint_measurable
    {G : GenStage D hr Dm bw j₀} {M : ℕ} {k : InvConsts}
    (hnat : G.IsNatural M) (hcert : G.IsContextCertified k)
    (hΛ : 1 ≤ D.Λ) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (ν e E tS tZ mres : ℝ) (n : CompIn G.comps → ℕ)
    (hs : G.fam.IsSmoothOn (G.innerDomain (Set.Icc tS tZ) mres) E n)
    (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) :
    Measurable (fun z : Set.Icc tS tZ × Vec 2 => G.fam.weight p z.1 •
      G.fam.dimFlux ν e E p (G.actual p) v u γ d I z.1
        (D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) z.2 z.1)
        (e⁻¹ • D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) z.2 z.1)) := by
  have hy : Continuous (fun z : Set.Icc tS tZ × Vec 2 =>
      D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) z.2 z.1) := by
    exact (CycleReference.streamFlow_joint_smooth (D.hΦ (G.level - 1))).continuous.comp
      (continuous_const.prodMk (continuous_snd.prodMk
        (continuous_subtype_val.comp continuous_fst)))
  exact (native_weighted_dimFlux_joint_measurable hnat hcert hΛ hi hj ν e E tS tZ mres n hs
    p v u γ d I).comp
      (measurable_fst.prodMk (hy.measurable.prodMk (hy.const_smul (e⁻¹)).measurable))
end

/-! Joint measurability of the incoming stage's actual weighted Piola arrays. -/

section
open CycleJointProofs
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_weighted_piece_array_joint_measurable
    {G : GenStage D hr Dm bw j₀} {M : ℕ} {k : InvConsts}
    (hnat : G.IsNatural M) (hcert : G.IsContextCertified k)
    (hΛ : 1 ≤ D.Λ) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (ν e E tS tZ mres : ℝ) (n : CompIn G.comps → ℕ)
    (hs : G.fam.IsSmoothOn (G.innerDomain (Set.Icc tS tZ) mres) E n)
    (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u)
    (r : ℕ) (A : DerivativeWord2 r) (a : Fin 2) :
    Measurable (fun z : Set.Icc tS tZ × Vec 2 => G.fam.weight p z.1 *
      transportedCoeff (chartInvJacobian ⇑((G.fam.piece p).material z.1).symm)
        (G.fam.identity v u γ).maxOrder
        (fun d I => G.fam.dimFlux ν e E p (G.actual p) v u γ d I z.1
          (((G.fam.piece p).material z.1).symm z.2)
          (e⁻¹ • ((G.fam.piece p).material z.1).symm z.2)) r A z.2 a) := by
  let K := naturalPreparationJacobian (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1)
  let B := fun d (I : DerivativeWord2 (d - 1)) (z : Set.Icc tS tZ × Vec 2) =>
    G.fam.weight p z.1 • G.fam.dimFlux ν e E p (G.actual p) v u γ d I z.1
      (D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) z.2 z.1)
      (e⁻¹ • D.flowOf (G.level - 1) (D.slotAnchor G.level p.1) z.2 z.1)
  have hB : ∀ d I i, Measurable (fun z => B d I z i) := by
    intro d I i
    exact (measurable_pi_apply i).comp
      (native_weighted_sample_joint_measurable hnat hcert hΛ hi hj ν e E tS tZ mres n hs
        p v u γ d I)
  have hm := transportedCoeff_joint_measurable tS tZ K
    (naturalPreparationJacobian_entry_smooth (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1))
    (G.fam.identity v u γ).maxOrder B hB r A a
  convert hm using 1
  funext z
  dsimp [B, K]
  rw [transportedCoeff_smul_native]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [native_inverse_jacobian_eq_natural hnat p z.1,
    native_inverse_material_eq_flow hnat p z.1]
  rfl
end

end AVRegularity.Construction.Preservation.Buffer
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Joint measurability of the incoming stage's literal Eulerian coefficients. -/

section
open CycleJointProofs
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_constituentPhysical_joint_measurable
    {G : GenStage D hr Dm bw j₀} {M : ℕ} {k : InvConsts}
    (hnat : G.IsNatural M) (hcert : G.IsContextCertified k)
    (hΛ : 1 ≤ D.Λ) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (ν e E tS tZ mres : ℝ) (n : CompIn G.comps → ℕ)
    (hs : G.fam.IsSmoothOn (G.innerDomain (Set.Icc tS tZ) mres) E n)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ) :
    Measurable (fun z : Set.Icc tS tZ × Vec 2 =>
      constituentPhysical G.fam ν e E G.actual v u γ d z.1 z.2) := by
  let b := fun p (z : Set.Icc tS tZ × Vec 2) a (A : DerivativeWord2 (d - 1)) =>
    transportedCoeff (chartInvJacobian ⇑((G.fam.piece p).material z.1).symm)
      (G.fam.identity v u γ).maxOrder
      (fun d' I => G.fam.dimFlux ν e E p (G.actual p) v u γ d' I z.1
        (((G.fam.piece p).material z.1).symm z.2)
        (e⁻¹ • ((G.fam.piece p).material z.1).symm z.2)) (d - 1) A z.2 a
  change Measurable (fun z : Set.Icc tS tZ × Vec 2 => ∑ᶠ p,
    G.fam.weight p z.1 • nativeArrayAssembly (d - 1) (G.fam.identity v u γ).map (b p z))
  refine measurable_piece_finsum_onWindow G.fam tS tZ
    (fun p z => G.fam.weight p z.1 •
      nativeArrayAssembly (d - 1) (G.fam.identity v u γ).map (b p z)) ?_ ?_
  · intro p
    have hm := nativeArrayAssembly_measurable (d - 1) (G.fam.identity v u γ).map
      (fun z a A => G.fam.weight p z.1 * b p z a A)
      (fun a A => native_weighted_piece_array_joint_measurable hnat hcert hΛ hi hj
        ν e E tS tZ mres n hs p v u γ (d - 1) A a)
    convert hm using 1
    funext z
    exact ((nativeArrayAssembly (d - 1) (G.fam.identity v u γ).map).map_smul
      (G.fam.weight p z.1) (b p z)).symm
  · intro p z hout
    rw [G.fam.weight_zero p z.1 hout]
    exact zero_smul ℝ (nativeArrayAssembly (d - 1) (G.fam.identity v u γ).map (b p z))

theorem native_physCoeff_joint_measurable
    {G : GenStage D hr Dm bw j₀} {M : ℕ} {k : InvConsts}
    (hnat : G.IsNatural M) (hcert : G.IsContextCertified k)
    (hΛ : 1 ≤ D.Λ) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (tS tZ mres : ℝ) (n : CompIn G.comps → ℕ)
    (hs : G.fam.IsSmoothOn (G.innerDomain (Set.Icc tS tZ) mres)
      (D.eps (G.level - 1)) n)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ) :
    Measurable (fun z : Set.Icc tS tZ × Vec 2 => G.physCoeff v u γ d z.1 z.2) :=
  native_constituentPhysical_joint_measurable hnat hcert hΛ hi hj
    (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) tS tZ mres n hs v u γ d
end

/-! Molecular smoothing of one actual finite kernel evolution, independent of its initial
higher Fourier jets. -/

section
open CoupledEnergy.Galerkin CoupledEnergy.Variational KernelEnergy
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
    {a T ρ ν b : ℝ} {K D : ℕ}

theorem finite_kernel_molecular_buffer
    (P : (j : Fin (K + 1)) →
      TorusKernelOperator (h := h) (Γ := Γ) (G := G) a T ρ ν j.val D)
    (π : ι → ℝ) (hπ : ∀ j, (P j).π = π)
    (hBdata : ∀ j, (P j).B = (P (Fin.last K)).B)
    (hCdata : ∀ j, (P j).C = (P (Fin.last K)).C)
    (hSdata : ∀ j, (P j).S = (P (Fin.last K)).S)
    (hb : 0 < b) (hbT : a + b ≤ T) (hr : ρ ^ 2 ≤ (5 * ν / 4) * b)
    (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a T, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (hvp : ∀ t ∈ Set.Icc a T, AVenhance.IsZ2Periodic (v t))
    (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
    (hd : ∀ t ∈ Set.Icc a T, ∀ x,
      ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
    (hjets : ∀ t ∈ Set.Icc a T, ∀ l, 1 ≤ l → l ≤ K → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (initial : CoupledPlainCoefficients (h := h) N)
    (y : ℝ → CoupledPlainCoefficients (h := h) N) (hycont : Continuous y)
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun t => plainMatrixCLM ((P (Fin.last K)).projectedMatrix N v t))
      (fun _ => 0) initial a T y)
    (hint : IntervalIntegrable (AVenhance.Infra.ODE.linearRhs
      (fun t => plainMatrixCLM ((P (Fin.last K)).projectedMatrix N v t))
      (fun _ => 0) y) volume a T) :
    ∀ j ≤ K, ∀ t ∈ Set.Icc (a + b) T,
      massNormSq ρ π (fun i => (coupledPlainSynthesis N i j (y t)).val) +
        (5 * ν / 4) * (∫ τ in (a + b)..t,
          massGradNormSq ρ π (fun i => (coupledPlainSynthesis N i (j + 1) (y τ)).val)) ≤
      bufferEnergyCost j * massNormSq ρ π (fun i => (coupledPlainSynthesis N i 0 (y a)).val) := by
  let Q := P (Fin.last K)
  have hπpos : ∀ i, 0 < π i := by
    intro i
    rw [← hπ (Fin.last K)]
    exact Q.hπ i
  have hc : 0 ≤ 5 * ν / 4 := div_nonneg
    (mul_nonneg (by norm_num) Q.diffusivity_pos.le) (by norm_num)
  have hyac := hy.absolutelyContinuousOnInterval Q.htime hint
  have hdiff (j : ℕ) (hj : j ≤ K) :
      ∀ᵐ t ∂volume.restrict (Set.Icc a T),
        deriv (fun s => massNormSq ρ π (fun i => (coupledPlainSynthesis N i j (y s)).val)) t +
          (5 * ν / 4) * massGradNormSq ρ π
            (fun i => (coupledPlainSynthesis N i (j + 1) (y t)).val) ≤ 0 := by
    let jj : Fin (K + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    have hyj := kernelODE_lower_order (P jj) Q hj (hBdata jj) (hCdata jj) (hSdata jj)
      N v initial y hy
    have hAj := projectedMatrixCLM_order (P jj) Q hj (hBdata jj) (hCdata jj) (hSdata jj) N v
    have hintj : IntervalIntegrable (AVenhance.Infra.ODE.linearRhs
        (fun t => plainMatrixCLM ((P jj).projectedMatrix N v t))
        (fun _ => plainSourceCoefficients N (fun _ => j) (fun _ => 0) (fun _ => 0)) y)
        volume a T := by
      simpa only [hAj, plainKernelZeroSource] using hint
    have hh := (P jj).kernelODE_mass_homogeneous_deriv_le N v hv hvp αv B lam hα hB hlam
      hsmall hstrain hd (fun t ht l hl hlj x => hjets t ht l hl (hlj.trans hj) x)
      y initial hyj hintj
    simpa only [hπ jj] using hh
  apply molecular_energy_after_buffer_from hb hbT hc
    (massNormSq_nonneg ρ π hπpos _) hr
    (fun j _ => plainSynthesis_mass_absolutelyContinuous N (fun _ => j) ρ π hyac)
    (fun j _ => (plainSynthesis_massGrad_continuous N (fun _ => j) ρ π hycont).intervalIntegrable
      (μ := volume) a T)
    (fun _ _ _ _ => massNormSq_nonneg ρ π hπpos _)
    (fun _ _ _ _ => massGradNormSq_nonneg ρ π hπpos _) hdiff
    (fun j _ _ _ => fourier_mass_adjacent_order N j ρ π (fun i => (hπpos i).le) _)
    (le_refl _)
end

end AVRegularity.Construction.Preservation.Buffer
end

section
open Filter MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Molecular smoothing of one actual finite kernel evolution, independent of its initial
higher Fourier jets. -/

section
open scoped Topology
open CoupledEnergy.Galerkin CoupledEnergy.Variational KernelEnergy
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
    {a T ρ ν b : ℝ} {K D : ℕ}

theorem exists_higher_carrier_of_finite_kernel_buffer
    (P : (j : Fin (K + 1)) →
      TorusKernelOperator (h := h) (Γ := Γ) (G := G) a T ρ ν j.val D)
    (π : ι → ℝ) (hπ : ∀ j, (P j).π = π)
    (hBdata : ∀ j, (P j).B = (P (Fin.last K)).B)
    (hCdata : ∀ j, (P j).C = (P (Fin.last K)).C)
    (hSdata : ∀ j, (P j).S = (P (Fin.last K)).S)
    (hb : 0 < b) (hbT : a + b ≤ T) (hr : ρ ^ 2 ≤ (5 * ν / 4) * b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a T, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (hvp : ∀ t ∈ Set.Icc a T, AVenhance.IsZ2Periodic (v t))
    (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
    (hd : ∀ t ∈ Set.Icc a T, ∀ x,
      ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
    (hjets : ∀ t ∈ Set.Icc a T, ∀ l, 1 ≤ l → l ≤ K → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (modes : ℕ → ℕ)
    (initial : (N : ℕ) → CoupledPlainCoefficients (h := h) (modes N))
    (y : (N : ℕ) → ℝ → CoupledPlainCoefficients (h := h) (modes N))
    (hycont : ∀ N, Continuous (y N))
    (hy : ∀ N, AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun t => plainMatrixCLM ((P (Fin.last K)).projectedMatrix (modes N) v t))
      (fun _ => 0) (initial N) a T (y N))
    (hint : ∀ N, IntervalIntegrable (AVenhance.Infra.ODE.linearRhs
      (fun t => plainMatrixCLM ((P (Fin.last K)).projectedMatrix (modes N) v t))
      (fun _ => 0) (y N)) volume a T)

    (M : ℝ) (hinit : ∀ N, massNormSq ρ π
      (fun i => (coupledPlainSynthesis (modes N) i 0 (y N a)).val) ≤ M)
    (j : ℕ) (hj : j ≤ K) (t : ℝ) (ht : t ∈ Set.Icc (a + b) T)
    (g : ∀ i, TorusHk 0 (h i))
    (hpair : ∀ i, ∀ ψ : TorusHk 1 (h i),
      Tendsto (fun N => inner ℝ (torusHkValueCLM (coupledPlainSynthesis (modes N) i j (y N t)))
        (torusHkValueCLM ψ)) atTop
        (𝓝 (inner ℝ (torusHkValueCLM (g i)) (torusHkValueCLM ψ)))) :
    ∃ F : ∀ i, TorusHk j (h i),
      (∀ i, truncateTorusHk (Nat.zero_le j) (F i) = g i) ∧
      Real.sqrt (massNormSq ρ π (fun i => (F i).val)) ≤
        Real.sqrt (bufferEnergyCost j * M) := by
  have hπpos : ∀ i, 0 < π i := by
    intro i
    rw [← hπ (Fin.last K)]
    exact (P (Fin.last K)).hπ i
  apply exists_higher_carrier_of_uniform_mass_bound_and_H1_pairings (fun _ => j)
    ρ (P (Fin.last K)).radius_pos π hπpos (Real.sqrt (bufferEnergyCost j * M))
    (fun N i => coupledPlainSynthesis (modes N) i j (y N t)) g _ hpair
  intro N
  have he := finite_kernel_molecular_buffer P π hπ hBdata hCdata hSdata hb hbT hr
    (modes N) v hv hvp αv B lam hα hB hlam hsmall hstrain hd hjets
    (initial N) (y N) (hycont N) (hy N) (hint N) j hj t ht
  have hc : 0 ≤ 5 * ν / 4 := div_nonneg
    (mul_nonneg (by norm_num) (P (Fin.last K)).diffusivity_pos.le) (by norm_num)
  have hdiss : 0 ≤ (5 * ν / 4) * (∫ τ in (a + b)..t,
      massGradNormSq ρ π (fun i => (coupledPlainSynthesis (modes N) i (j + 1) (y N τ)).val)) :=
    mul_nonneg hc (intervalIntegral.integral_nonneg_of_forall ht.1
      (fun τ => massGradNormSq_nonneg ρ π hπpos _))
  apply Real.sqrt_le_sqrt
  exact (le_add_of_nonneg_right hdiss).trans (he.trans
    (mul_le_mul_of_nonneg_left (hinit N) (bufferEnergyCost_nonneg j)))
end

/-! The order-zero closed-trace sequence inherits all reserved molecular buffer orders. -/

section
open scoped Topology
open CoupledEnergy.Galerkin CoupledEnergy.Variational KernelEnergy
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
    {a T ρ ν b : ℝ} {K D : ℕ}

theorem exists_higher_carrier_of_order_zero_kernel_sequence
    (P : (j : Fin (K + 1)) →
      TorusKernelOperator (h := h) (Γ := Γ) (G := G) a T ρ ν j.val D)
    (π : ι → ℝ) (hπ : ∀ j, (P j).π = π)
    (hBdata : ∀ j, (P j).B = (P (Fin.last K)).B)
    (hCdata : ∀ j, (P j).C = (P (Fin.last K)).C)
    (hSdata : ∀ j, (P j).S = (P (Fin.last K)).S)
    (hb : 0 < b) (hbT : a + b ≤ T) (hr : ρ ^ 2 ≤ (5 * ν / 4) * b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a T, ContDiff ℝ (↑(⊤ : ℕ∞)) (v t))
    (hvp : ∀ t ∈ Set.Icc a T, AVenhance.IsZ2Periodic (v t))
    (αv B lam : ℝ) (hα : 0 ≤ αv) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : αv * B * ρ ^ 2 ≤ ν / 8)
    (hd : ∀ t ∈ Set.Icc a T, ∀ x,
      ∑ q : Fin 2, fderiv ℝ (v t) x (basisVec q) q = 0)
    (hjets : ∀ t ∈ Set.Icc a T, ∀ l, 1 ≤ l → l ≤ K → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        αv * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hv_bdd : ∃ V : ℝ, ∀ t ∈ Set.Icc a T, ∀ x, ‖v t x‖ ≤ V)
    (hv_meas : Measurable (fun z : Set.Icc a T × Vec 2 => v z.1 z.2))
    (f : ∀ i, TorusHk 0 (h i)) (modes : ℕ → ℕ)
    (y : (N : ℕ) → C(Set.Icc a T, CoupledPlainCoefficients (h := h) (modes N)))
    (hy : ∀ N, AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun t => plainMatrixCLM ((P ⟨0, Nat.zero_lt_succ K⟩).projectedMatrix (modes N) v t))
      (fun _ => 0) (plainInitialCoefficients (modes N) (fun _ => 0) f) a T
      (AVenhance.Infra.ODE.extendCurve (P ⟨0, Nat.zero_lt_succ K⟩).htime (y N)))
    (j : ℕ) (hj : j ≤ K) (t : ℝ) (ht : t ∈ Set.Icc (a + b) T)
    (g : ∀ i, TorusHk 0 (h i))
    (hpair : ∀ i, ∀ ψ : TorusHk 1 (h i),
      Tendsto (fun N => inner ℝ (torusHkValueCLM (coupledPlainSynthesis (modes N) i 0
        (AVenhance.Infra.ODE.extendCurve (P ⟨0, Nat.zero_lt_succ K⟩).htime (y N) t)))
        (torusHkValueCLM ψ)) atTop
        (𝓝 (inner ℝ (torusHkValueCLM (g i)) (torusHkValueCLM ψ)))) :
    ∃ F : ∀ i, TorusHk j (h i),
      (∀ i, truncateTorusHk (Nat.zero_le j) (F i) = g i) ∧
      Real.sqrt (massNormSq ρ π (fun i => (F i).val)) ≤
        Real.sqrt (bufferEnergyCost j * massNormSq ρ π (fun i => (f i).val)) := by
  let z : Fin (K + 1) := ⟨0, Nat.zero_lt_succ K⟩
  let Q := P z
  let curve := fun N => AVenhance.Infra.ODE.extendCurve Q.htime (y N)
  have hmatrix := projectedMatrixCLM_order Q (P (Fin.last K)) (Nat.zero_le K)
    ((hBdata z).trans (hBdata (Fin.last K)).symm)
    ((hCdata z).trans (hCdata (Fin.last K)).symm)
    ((hSdata z).trans (hSdata (Fin.last K)).symm)
  have hπpos (i : ι) : 0 < π i := by
    rw [← hπ z]
    exact Q.hπ i
  apply exists_higher_carrier_of_finite_kernel_buffer P π hπ hBdata hCdata hSdata
    hb hbT hr v hv hvp αv B lam hα hB hlam hsmall hstrain hd hjets modes
    (fun N => plainInitialCoefficients (modes N) (fun _ => 0) f) curve
    (fun N => AVenhance.Infra.ODE.continuous_extendCurve Q.htime (y N))
    (fun N => by rw [← hmatrix]; exact hy N)
    (fun N => by rw [← hmatrix]; exact kernel_curve_rhs_intervalIntegrable Q (modes N) v hv_bdd hv_meas (y N))
    (massNormSq ρ π (fun i => (f i).val))
    (fun N => finite_rough_initial_mass_le (modes N) ρ π hπpos f Q.htime _ _ _ (hy N))
    j hj t ht g
  intro i ψ
  have he (N : ℕ) : torusHkValueCLM (coupledPlainSynthesis (modes N) i j (curve N t)) =
      torusHkValueCLM (coupledPlainSynthesis (modes N) i 0 (curve N t)) := by
    rw [← torusHkValue_truncate (Nat.zero_le j), coupledPlainSynthesis_truncate]
  simpa only [he] using hpair i ψ
end

end AVRegularity.Construction.Preservation.Buffer
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Integrate the literal order-zero physical flux using the weighted dissipation bound. -/

open AVRegularity.KernelEnergy AVRegularity.CoupledEnergy.Variational
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν 0 D)

theorem total_flux_value_integral_le (w : ∀ i, ℝ → TorusHk 1 (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b))) (i : ι) {M : ℝ}
    (henergy : (5 * ν / 4) *
      (∫ t in Set.Icc a b, massGradNormSq ρ P.π (fun i => (w i t).val)) ≤ M) :
    (∫ t in a..b, ‖CoupledEnergy.Galerkin.torusHkValueCLM
      (ν • torusGradientTensor (w i t) + P.carrierFlux w i t)‖) ≤
      (Real.sqrt (P.π i) * (ν * (1 + P.θ))) * Real.sqrt (b - a) *
        Real.sqrt (M / (5 * ν / 4)) := by
  have hν := P.diffusivity_pos
  have hθ := P.theta_nonneg_of_component i
  apply flux_integral_le_of_energy P.htime
    (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg P.diffusivity_pos.le (by linarith only [hθ])))
    (by positivity : 0 < 5 * ν / 4)
    _ (total_flux_value_memLp P w hw i) _ (kernel_gradient_time_integrable a b ρ P.π w hw)
    (fun t _ => massGradNormSq_nonneg ρ P.π P.hπ (fun i => (w i t).val)) _ henergy
  intro t ht
  have he : P.carrierFlux w i t = P.flux t ht (fun j => w j t) i := by
    unfold AVRegularity.KernelEnergy.TorusKernelOperator.carrierFlux
    simp only [Set.projIcc_of_mem P.htime ht]
  rw [he]
  exact total_flux_value_norm_le P t ht (fun j => w j t) i

end TorusKernelOperator

end AVRegularity.Construction.Preservation.Buffer
end

section
open MeasureTheory Homogenization AVenhance
namespace AVRegularity.Construction.Preservation.Buffer

/-! Literal stream velocities supply the qualitative drift hypotheses of the kernel buffer. -/

theorem stream_kernel_drift_data {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (a b : ℝ) :
    (∀ t ∈ Set.Icc a b, ContDiff ℝ (↑(⊤ : ℕ∞)) (streamVel φ t)) ∧
    (∀ t ∈ Set.Icc a b, IsZ2Periodic (streamVel φ t)) ∧
    (∀ t ∈ Set.Icc a b, ∀ x,
      ∑ q : Fin 2, fderiv ℝ (streamVel φ t) x (basisVec q) q = 0) ∧
    (∃ V : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, ‖streamVel φ t x‖ ≤ V) ∧
    Measurable (fun z : Set.Icc a b × Vec 2 => streamVel φ z.1 z.2) := by
  have hv := Infra.Construction.smoothPeriodic_streamVel hφ
  obtain ⟨V, _hV, hbV⟩ :=
    CycleJointProofs.streamVel_bounded_on_compact_time hφ (Set.Icc a b) isCompact_Icc
  refine ⟨fun t _ => hv.smooth.comp (contDiff_const.prodMk contDiff_id),
    fun t _ => ?_, fun t _ x => ?_, ⟨V, hbV⟩, ?_⟩
  · intro n x
    simpa using hv.periodic 0 n t x
  · simpa only [Infra.Flow.spatialDivergence,
      Infra.Flow.jointSpatialFDeriv_eq_slice hv, Fin.sum_univ_two,
      Infra.Flow.Liouville.flowBasis0, Infra.Flow.Liouville.flowBasis1, basisVec] using
      Velocity.Port.Section2FlowIdentities.streamVel_spatialDivergence_eq_zero hφ t x
  · exact hv.smooth.continuous.measurable.comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Uniform genuine scalar and Piola jet budgets give a finite native operator seminorm. -/

open CycleJointProofs
variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem native_transport_coefficientSeminorm_finite
    (a b : ℝ) (K : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ t ∈ Set.Icc a b, ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun x => K t x i j))
    (N Dγ n r : ℕ) (C E ρ : ℝ) (hC : 1 ≤ C) (hE : 0 < E)
    (hρ : 0 < ρ) (hρE : ρ ≤ E) (hn : n + Dγ ≤ N)
    (hKC : ∀ t ∈ Set.Icc a b, ∀ i l j, j ≤ N → ∀ x,
      E ^ j * ‖iteratedFDeriv ℝ j (fun y => K t y i l) x‖ ≤ C)
    (B : ℝ → ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2 → Vec 2)
    (hB : ∀ t ∈ Set.Icc a b, ∀ d I i, ContDiff ℝ (n : ℕ) (fun x => B t d I x i))
    (MB : ∀ d : ℕ, DerivativeWord2 (d - 1) → ℝ) (hMB : ∀ d I, 0 ≤ MB d I)
    (hBj : ∀ t ∈ Set.Icc a b, ∀ d ∈ Finset.Icc (r + 1) Dγ, ∀ I i j, j ≤ n → ∀ y,
      ρ ^ j * ‖iteratedFDeriv ℝ j (fun x => B t d I x i) y‖ ≤ MB d I)
    (Cmap : U →L[ℝ] V) :
    coefficientSeminorm ρ n a b (fun t x => nativeArrayAssembly r Cmap
      (fun i A => transportedCoeff (K t) Dγ (fun d I => B t d I x) r A x i)) ≠ ⊤ := by
  let M : ℝ := ∑ _i : Fin 2, ∑ _A : DerivativeWord2 r, ‖Cmap‖ *
    (∑ d ∈ Finset.Icc (r + 1) Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ _l : Fin 2,
      (((n + 1 : ℕ) * (2 : ℝ) ^ n) ^ 2 * C *
        (3 * (N + 1 : ℕ) * 2 ^ N * C) ^ Dγ) * (MB d I * E⁻¹ ^ (d - 1 - r)))
  have hM : 0 ≤ M := by
    dsimp only [M]
    apply Finset.sum_nonneg; intro _i _
    apply Finset.sum_nonneg; intro _A _
    apply mul_nonneg (norm_nonneg _)
    apply Finset.sum_nonneg; intro d _
    apply Finset.sum_nonneg; intro I _
    apply Finset.sum_nonneg; intro _l _
    exact mul_nonneg (by positivity) (mul_nonneg (hMB d I) (pow_nonneg (inv_nonneg.mpr hE.le) _))
  refine pointwise_coefficient_seminorm_finite ρ hρ n a b _ ?_ (fun _ => M) (fun _ => hM) ?_
  · intro t ht
    apply nativeArrayAssembly_spatial_smooth r n Cmap
    intro i A
    exact transportedCoeff_spatial_smooth (K t) (hK t ht) Dγ n (B t) (hB t ht) r A i
  · intro t ht j hj x
    exact uniform_native_transport_assembly_jet_bound (K t) (hK t ht) N Dγ Dγ n j r
      le_rfl hj C E ρ hC hE hρ.le hρE (by omega) (hKC t ht) (B t)
      (fun d I i => (hB t ht d I i).of_le (by exact_mod_cast hj)) MB hMB
      (fun d hd I i l hl y => hBj t ht d hd I i l (hl.trans hj) y) Cmap x

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Spatial regularity of the incoming native coefficients on their certified domain. -/

section
open CycleJointProofs
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_constituentPhysical_spatial_smooth
    {G : GenStage D hr Dm bw j₀} {M : ℕ}
    (hnat : G.IsNatural M) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (ν e E tS tZ mres : ℝ) (hE : E ≠ 0) (n : CompIn G.comps → ℕ)
    (hs : G.fam.IsSmoothOn (G.innerDomain (Set.Icc tS tZ) mres) E n)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (t : ℝ) (ht : t ∈ Set.Icc tS tZ) :
    ContDiff ℝ (n v : ℕ) (constituentPhysical G.fam ν e E G.actual v u γ d t) := by
  let b := fun p s x a (A : DerivativeWord2 (d - 1)) =>
    transportedCoeff (chartInvJacobian ⇑((G.fam.piece p).material s).symm)
      (G.fam.identity v u γ).maxOrder
      (fun d' I => G.fam.dimFlux ν e E p (G.actual p) v u γ d' I s
        (((G.fam.piece p).material s).symm x)
        (e⁻¹ • ((G.fam.piece p).material s).symm x)) (d - 1) A x a
  change ContDiff ℝ (n v : ℕ) (fun x : Vec 2 => ∑ᶠ p,
    G.fam.weight p t • nativeArrayAssembly (d - 1) (G.fam.identity v u γ).map (b p t x))
  refine piece_finsum_spatial_smooth_onWindow G.fam tS tZ
    (fun p s x => G.fam.weight p s •
      nativeArrayAssembly (d - 1) (G.fam.identity v u γ).map (b p s x)) (n v) ?_ ?_ t ht
  · intro p s hs'
    by_cases hout : s ∈ (G.fam.piece p).output
    · have hm := natural_constituent_operator_smooth G.fam ν e E hE n
        (G.innerDomain (Set.Icc tS tZ) mres) hs p (G.actual p) v u γ (d - 1)
        (D.Φ (G.level - 1)) (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1) s
        (fun Y => G.innerDomain_native (Set.Icc tS tZ) mres p
          (hnat.2.2.1 p) hi hj s ⟨hout, hs'⟩ Y)
      convert hm.const_smul (G.fam.weight p s) using 1
      funext x
      dsimp [b]
      rw [native_inverse_jacobian_eq_natural hnat p s,
        native_inverse_material_eq_flow hnat p s]
    · have he : (fun x : Vec 2 => G.fam.weight p s •
          nativeArrayAssembly (d - 1) (G.fam.identity v u γ).map (b p s x)) =
          fun _ => 0 := by
        funext x
        rw [G.fam.weight_zero p s hout]
        exact zero_smul ℝ (nativeArrayAssembly (d - 1) (G.fam.identity v u γ).map (b p s x))
      rw [he]
      exact contDiff_const
  · intro p s x hout
    rw [G.fam.weight_zero p s hout]
    exact zero_smul ℝ (nativeArrayAssembly (d - 1) (G.fam.identity v u γ).map (b p s x))

theorem native_physCoeff_spatial_smooth
    {G : GenStage D hr Dm bw j₀} {M : ℕ}
    (hnat : G.IsNatural M) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (tS tZ mres : ℝ) (hE : D.eps (G.level - 1) ≠ 0) (n : CompIn G.comps → ℕ)
    (hs : G.fam.IsSmoothOn (G.innerDomain (Set.Icc tS tZ) mres)
      (D.eps (G.level - 1)) n)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (t : ℝ) (ht : t ∈ Set.Icc tS tZ) :
    ContDiff ℝ (n v : ℕ) (G.physCoeff v u γ d t) :=
  native_constituentPhysical_spatial_smooth hnat hi hj (D.kap G.level) (D.eps G.level)
    (D.eps (G.level - 1)) tS tZ mres hE n hs v u γ d t ht
end

/-! Each actual weighted piece is spatially regular throughout the working window. -/

section
open CycleJointProofs
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_weighted_piece_spatial_smooth
    {G : GenStage D hr Dm bw j₀} {M : ℕ}
    (hnat : G.IsNatural M) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (ν e E a b mres : ℝ) (hE : E ≠ 0) (N : CompIn G.comps → ℕ)
    (hs : G.fam.IsSmoothOn (G.innerDomain (Set.Icc a b) mres) E N)
    (p : OddSlot) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (r : ℕ)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ContDiff ℝ (N v : ℕ) (fun x => G.fam.weight p t •
      nativeArrayAssembly r (G.fam.identity v u γ).map
        (fun i A => transportedCoeff (chartInvJacobian ⇑((G.fam.piece p).material t).symm)
          (G.fam.identity v u γ).maxOrder
          (fun d I => G.fam.dimFlux ν e E p (G.actual p) v u γ d I t
            (((G.fam.piece p).material t).symm x)
            (e⁻¹ • ((G.fam.piece p).material t).symm x)) r A x i)) := by
  by_cases hout : t ∈ (G.fam.piece p).output
  · have hm := natural_constituent_operator_smooth G.fam ν e E hE N
      (G.innerDomain (Set.Icc a b) mres) hs p (G.actual p) v u γ r
      (D.Φ (G.level - 1)) (D.hΦ (G.level - 1)) (D.slotAnchor G.level p.1) t
      (fun Y => G.innerDomain_native (Set.Icc a b) mres p
        (hnat.2.2.1 p) hi hj t ⟨hout, ht⟩ Y)
    convert hm.const_smul (G.fam.weight p t) using 1
    funext x
    rw [native_inverse_jacobian_eq_natural hnat p t,
      native_inverse_material_eq_flow hnat p t]
  · rw [G.fam.weight_zero p t hout]
    have he : (fun x => (0 : ℝ) • nativeArrayAssembly r (G.fam.identity v u γ).map
        (fun i A => transportedCoeff (chartInvJacobian ⇑((G.fam.piece p).material t).symm)
          (G.fam.identity v u γ).maxOrder
          (fun d I => G.fam.dimFlux ν e E p (G.actual p) v u γ d I t
            (((G.fam.piece p).material t).symm x)
            (e⁻¹ • ((G.fam.piece p).material t).symm x)) r A x i)) = fun _ => 0 := by
      funext x
      exact zero_smul ℝ (nativeArrayAssembly r (G.fam.identity v u γ).map
        (fun i A => transportedCoeff (chartInvJacobian ⇑((G.fam.piece p).material t).symm)
          (G.fam.identity v u γ).maxOrder
          (fun d I => G.fam.dimFlux ν e E p (G.actual p) v u γ d I t
            (((G.fam.piece p).material t).symm x)
            (e⁻¹ • ((G.fam.piece p).material t).symm x)) r A x i))
    rw [he]
    exact contDiff_const
end

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance
namespace AVRegularity.Construction.Preservation.Buffer

/-! Spatial periodicity passes to any fixed spacetime derivative. -/

theorem spacetime_directional_periodic (f : ℝ × Vec 2 → ℝ)
    (hp : ∀ t, IsZ2Periodic (fun x => f (t, x))) (v : ℝ × Vec 2) (t : ℝ) :
    IsZ2Periodic (fun x => CycleJointProofs.spacetimeDirectionalField f v (t, x)) := by
  intro k x
  have he : (fun p : ℝ × Vec 2 => f ((0, latticeShift k) + p)) = f := by
    funext p
    rcases p with ⟨r, y⟩
    simpa only [Prod.mk_add_mk, zero_add, add_comm (latticeShift k)] using hp r k y
  have hd := congrArg (fun F => fderiv ℝ F (t, x)) he
  rw [fderiv_comp_add_left] at hd
  simpa only [CycleJointProofs.spacetimeDirectionalField, Prod.mk_add_mk, zero_add,
    add_comm (latticeShift k)] using congrArg (fun A => A v) hd

end AVRegularity.Construction.Preservation.Buffer
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleJointProofs AVRegularity.CycleEvolution
namespace AVRegularity.Construction.Preservation.Buffer

/-! Smooth periodic spacetime fields are genuine strong-time periodic H1 tests. -/

def smoothScalarTorusH1 (f : ℝ × Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ t, IsZ2Periodic (fun x => f (t, x))) (t : ℝ) : TorusHk 1 ℝ :=
  (cellSmoothScalarH1 (fun x => f (t, x))
    (hf.comp (contDiff_const.prodMk contDiff_id)) (hp t)).toHk

theorem smoothScalarTorusH1_value_ae (f : ℝ × Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : ∀ t, IsZ2Periodic (fun x => f (t, x))) (t : ℝ) :
    (smoothScalarTorusH1 f hf hp t).val (valueIndex2 1) =ᵐ[volume.restrict unitCube]
      fun x => f (t, x) := by
  exact torusJetToL2_ae _ _ _

theorem smoothScalarTorusH1_gradient_ae (f : ℝ × Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : ∀ t, IsZ2Periodic (fun x => f (t, x)))
    (t : ℝ) (w : DerivativeWord2 1) :
    (smoothScalarTorusH1 f hf hp t).val ⟨⟨1, by omega⟩, w⟩ =ᵐ[volume.restrict unitCube]
      fun x => fderiv ℝ f (t, x) (0, basisVec (w 0)) := by
  apply (torusJetToL2_ae _ _ _).trans
  apply Filter.Eventually.of_forall
  intro x
  change fderiv ℝ (fun y => f (t, y)) x (basisVec (w 0)) = _
  exact CycleWords.joint_spatial_gradient_eq f (hf.of_le (by simp)) t x (w 0)

theorem smoothScalarTorusH1_strong_time (f : ℝ × Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : ∀ t, IsZ2Periodic (fun x => f (t, x)))
    {a b : ℝ} (hab : a ≤ b) :
    StrongTimeRegularity a b (smoothScalarTorusH1 f hf hp)
      (smoothScalarTorusH1 (spacetimeDirectionalField f (1, 0))
        (spacetimeDirectionalField_smooth f hf (1, 0))
        (spacetime_directional_periodic f hp (1, 0))) := by
  let D := spacetimeDirectionalField f (1, 0)
  have hD := spacetimeDirectionalField_smooth f hf (1, 0)
  have hpD := spacetime_directional_periodic f hp (1, 0)
  apply torusHk_strong_time_of_jets
  rintro ⟨⟨n, hn⟩, w⟩
  have hn1 : n ≤ 1 := Nat.le_of_lt_succ hn
  interval_cases n
  · have hw : w = Fin.elim0 := Subsingleton.elim _ _
    subst w
    exact smooth_scalar_cell_strong_time hab f hf _ _
      (smoothScalarTorusH1_value_ae f hf hp)
      (smoothScalarTorusH1_value_ae D hD hpD)
  · let v : ℝ × Vec 2 := (0, basisVec (w 0))
    let G := spacetimeDirectionalField f v
    have hG := spacetimeDirectionalField_smooth f hf v
    apply smooth_scalar_cell_strong_time hab G hG _ _
    · exact fun t => smoothScalarTorusH1_gradient_ae f hf hp t w
    · intro t
      apply (smoothScalarTorusH1_gradient_ae D hD hpD t w).trans
      apply Filter.Eventually.of_forall
      intro x
      exact smoothField_directional_derivative_commute f (hf.of_le (by simp))
        (t, x) (1, 0) v

end AVRegularity.Construction.Preservation.Buffer
end
