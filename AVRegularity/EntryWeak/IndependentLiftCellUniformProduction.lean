-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.IndependentLiftCoefficientAUniformProduction

section
section
/-! A clamped transfer uses finitely many reference germs, so its full-time naturality has an open common slice. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedSpace ℝ P] in
theorem independentWeakCutoffPartition_translation (D : OCData) (m : ℕ)
    (f : ℤ → ℝ → Vec 2 → P → Vec 2) (δ : P)
    (hf : ∀ slot, IndependentSourceTranslationInvariant δ (f slot)) :
    IndependentSourceTranslationInvariant δ (independentWeakCutoffPartition D m f) := by
  intro t z Y
  unfold independentWeakCutoffPartition
  congr 1
  funext slot
  rw [hf slot t z Y]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Literal proof-indexed weak partitions preserve phase symmetries and finite-window source germs. -/
@[expose] public noncomputable section
open Homogenization Set
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedSpace ℝ P] in
theorem independentWeakConditionalPartition_translation
    (D : OCData) (m : ℕ) (Eligible : ℤ → Prop)
    (f : ∀ slot, Eligible slot → ℝ → Vec 2 → P → Vec 2) (δ : P)
    (hf : ∀ slot h, IndependentSourceTranslationInvariant δ (f slot h)) :
    IndependentSourceTranslationInvariant δ
      (independentWeakCutoffPartition D m (fun slot t z Y => ∑ᶠ h : Eligible slot, f slot h t z Y)) := by
  apply independentWeakCutoffPartition_translation
  intro slot t z Y
  apply finsum_congr
  intro h
  exact hf slot h t z Y

end AVRegularity.EntryWeakProofs
end
end

section
/-! Centered chart differences retain the independent coarse spatial center. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def independentMovingCenteredChart (f : P × Vec 2 → Vec 2) (θ : ℝ)
    (Y : (P × Vec 2) × Vec 2) : Vec 2 :=
  θ⁻¹ • (f (Y.1.1, Y.1.2 + θ • Y.2) - f Y.1)

theorem independentMovingCenteredChart_contDiff (f : P × Vec 2 → Vec 2)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (θ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (independentMovingCenteredChart f θ) := by
  exact ((hf.comp ((contDiff_fst.comp contDiff_fst).prodMk
    ((contDiff_snd.comp contDiff_fst).add (contDiff_snd.const_smul θ)))).sub
      (hf.comp contDiff_fst)).const_smul θ⁻¹

theorem independentMovingCenteredChart_jet_bound (f : P × Vec 2 → Vec 2)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (θ : ℝ) (hθ : θ ≠ 0) (hθ₁ : |θ| ≤ 1)
    (K n : ℕ) (hn : n ≤ K) (B : ℝ) (hB : 0 ≤ B)
    (Y : (P × Vec 2) × Vec 2) (S : ℝ) (hY : ‖Y.2‖ ≤ S)
    (hb : ∀ i, 1 ≤ i → i ≤ K + 1 →
      ∀ Z ∈ segment ℝ Y.1 (Y.1.1, Y.1.2 + θ • Y.2),
        ‖iteratedFDeriv ℝ i f Z‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (independentMovingCenteredChart f θ) Y‖ ≤
      (2 : ℝ) ^ K * B * (S + K) := by
  let F := fun Z : P × (Vec 2 × Vec 2) =>
    θ⁻¹ • (f (Z.1, Z.2.1 + θ • Z.2.2) - f (Z.1, Z.2.1))
  have hF : ContDiff ℝ (n : ℕ∞) F := by
    exact ((hf.of_le (by simp)).comp (contDiff_fst.prodMk
      ((contDiff_fst.comp contDiff_snd).add
        ((contDiff_snd.comp contDiff_snd).const_smul θ)))).sub
      ((hf.of_le (by simp)).comp
        (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd))) |>.const_smul θ⁻¹
  have he : independentMovingCenteredChart f θ =
      F ∘ independentTransferReassociate (P := P) := rfl
  rw [he]
  have hh := finite_affine_derivative_norm_le F n hF
    independentTransferReassociate independentTransferReassociate_norm_le 0 Y
  simp only [add_zero] at hh
  exact hh.trans (independent_spatial_difference_joint_menu_bound f K n
    (hf.of_le (by simp)) hn B hB θ hθ hθ₁ Y.1.1 Y.1.2 Y.2 S hY hb)

theorem independentMovingCenteredChart_disk_jet_bound (f : P × Vec 2 → Vec 2)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (θ : ℝ) (hθ : θ ≠ 0) (hθ₁ : |θ| ≤ 1)
    (K n : ℕ) (hn : n ≤ K) (B : ℝ) (hB : 0 ≤ B)
    (Y : (P × Vec 2) × Vec 2) (R S : ℝ)
    (hX : ‖Y.1.2‖ ≤ R) (hY : ‖Y.2‖ ≤ S)
    (hb : ∀ i, 1 ≤ i → i ≤ K + 1 → ∀ Z : Vec 2, ‖Z‖ ≤ R + S →
      ‖iteratedFDeriv ℝ i f (Y.1.1, Z)‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (independentMovingCenteredChart f θ) Y‖ ≤
      (2 : ℝ) ^ K * B * (S + K) := by
  apply independentMovingCenteredChart_jet_bound f hf θ hθ hθ₁ K n hn B hB Y S hY
  intro i hi hiK Z hZ
  have hS : 0 ≤ S := (norm_nonneg _).trans hY
  have hstep : ‖θ • Y.2‖ ≤ S := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hθ₁ (norm_nonneg _)).trans
      (by simpa only [one_mul] using hY)
  have hend : ‖Y.1.2 + θ • Y.2‖ ≤ R + S :=
    (norm_add_le _ _).trans (add_le_add hX hstep)
  have hz := independent_spatial_segment_norm_le Y.1.1 Y.1.2
    (Y.1.2 + θ • Y.2) Z (R + S) (hX.trans (le_add_of_nonneg_right hS)) hend hZ
  have hp := independent_spatial_segment_parameter Y.1.1 Y.1.2
    (Y.1.2 + θ • Y.2) Z hZ
  have he : Z = (Y.1.1, Z.2) := Prod.ext hp rfl
  rw [he]
  exact hb i hi hiK Z.2 hz

end AVRegularity.EntryWeakProofs
end
end

section
/-! The inverse fresh chart is produced from earlier reverse-time chart jets and genuine re-anchoring. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def independentCenteredChildInverseModel (D : OCData) (m : ℕ) (slot : ℤ) (u r : ℝ)
    (Fr Iu Fu : P × Vec 2 → Vec 2) (θ : ℝ) (Y : P × (Vec 2 × (Vec 2 × Vec 2))) : Vec 2 :=
  independentCenteredChildChart D m slot r u Fr Iu Fu θ
    (independentCenteredChildReanchorInput D m slot u r θ Y)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Inverse Piola matrices retain both the coarse spatial center and the finer slow variable. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def independentMovingTransferJetCost (K : ℕ) (B S : ℝ) : ℝ :=
  positiveJetCompositionBudget (K + 1)
    (max (max 1 ((2 : ℝ) ^ (K + 1) * B * (S + 2 * Real.pi + (K + 1))))
      (weakTransferJointShearCost (K + 1)))

theorem independent_moving_transfer_inverse_jacobian_jets
    (f : P × Vec 2 → Vec 2) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (θ : ℝ) (hθ : θ ≠ 0) (hθ₁ : |θ| ≤ 1)
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (m : ℕ) (slot : ℤ) (hp : Odd slot) (u t : ℝ)
    (hsmall : |u - t| * ocA D.α D.q D.Λ m ≤ 1)
    (K n : ℕ) (hn : n ≤ K) (B R S : ℝ) (hB : 0 ≤ B)
    (hdet : ∀ Y : ((P × Vec 2) × Vec 2) × Vec 2,
      (jacMatrix (fun x => independentCenteredTransfer (independentMovingCenteredChart f θ)
        D m slot u t (Y.1.1, Y.1.2, x)) Y.2).det = 1)
    (X : ((P × Vec 2) × Vec 2) × Vec 2)
    (hX : ‖X.1.1.2‖ ≤ R) (hS : ‖X.2‖ ≤ S)
    (hb : ∀ a, 1 ≤ a → a ≤ K + 2 → ∀ Z : Vec 2,
      ‖Z‖ ≤ R + (S + 2 * Real.pi) →
        ‖iteratedFDeriv ℝ a f (X.1.1.1, Z)‖ ≤ B)
    (i j : Fin 2) :
    ‖iteratedFDeriv ℝ n (fun Y : ((P × Vec 2) × Vec 2) × Vec 2 =>
      (jacMatrix (fun x => independentCenteredTransfer (independentMovingCenteredChart f θ)
        D m slot u t (Y.1.1, Y.1.2, x)) Y.2)⁻¹ i j) X‖ ≤
      independentMovingTransferJetCost K B S := by
  apply independent_centered_transfer_inverse_jacobian_jets
    (independentMovingCenteredChart f θ) (independentMovingCenteredChart_contDiff f hf θ)
    D hΛ hζ m slot hp u t hsmall K n hn
    (max 1 ((2 : ℝ) ^ (K + 1) * B * (S + 2 * Real.pi + (K + 1))))
    (le_max_left _ _) hdet X _ i j
  intro a ha haK
  let W := X.2 + D.relDisp m slot u t (X.1.2 + X.2)
  have hd := weak_relative_displacement_value_bound D hΛ hζ m slot hp u t (X.1.2 + X.2)
  have hd' : ‖D.relDisp m slot u t (X.1.2 + X.2)‖ ≤ 2 * Real.pi := hd.trans (by
    calc
      _ = (2 * Real.pi) * (|u - t| * ocA D.α D.q D.Λ m) := by ring
      _ ≤ (2 * Real.pi) * 1 := mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = _ := mul_one _)
  have hW : ‖W‖ ≤ S + 2 * Real.pi :=
    (norm_add_le _ _).trans (add_le_add hS hd')
  have hh := independentMovingCenteredChart_disk_jet_bound f hf θ hθ hθ₁
    (K + 1) a haK B hB (X.1.1, W) R (S + 2 * Real.pi) hX hW
    (fun b hb₁ hbK Z hZ => hb b hb₁ (by omega) Z hZ)
  exact hh.trans (by simpa only [Nat.cast_add, Nat.cast_one] using
    (le_max_right 1 ((2 : ℝ) ^ (K + 1) * B * (S + 2 * Real.pi + (K + 1)))))

end AVRegularity.EntryWeakProofs
end
end

section
/-! Full independent forcing copies the native synthetic recurrence with no assumptions on outgoing fields. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {d D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independent_lift_coefficient_a_source_slice (H : ℕ) (hH : 1 ≤ H)
    (edge : ConstituentEdges D (fun _ : ι => ℝ)) (hD : 1 ≤ D)
    (a : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec d → Vec 2)
    (L : Vec 2 →L[ℝ] Vec d) (hL : ‖L‖ ≤ 1) (offset : Vec d) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → Vec d → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (c : ℕ → ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (hh n : ℕ) (hn : 1 ≤ n) (out inp : ι)
    (QG : ∀ i j, IndependentParameterSourceReserve (H + 1) (fun t _ Y => G t Y i j))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      IndependentParameterSourceReserve (H + D + 2) (fun t z Y => c p q m.val α t z Y v u))
    (Qa : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      IndependentParameterSourceReserve (H + 1) (a v u d γ α)) (t : ℝ) (z X : Vec 2) :
    independentLiftCoefficientASource edge a L A η G v c hh n out inp t z (L X + offset) =
      normalizedLiftASource
        ⟨η, fun t X => G t (L X + offset), v,
          independentConstituentEdgeSlice edge a Qa L offset⟩
        (fun p q => independentScalarCoefficientSlice (c p q) L offset)
        (fun _ X => Real.exp (A X) • (Pi.single inp (1 : ℝ) : ι → ℝ)) hh n A t z X out := by
  have hpre1 : hh < hh ∨ (hh = hh ∧ n - 1 < n) := Or.inr ⟨rfl, by omega⟩
  have hpre2 (hn2 : 2 ≤ n) : hh < hh ∨ (hh = hh ∧ n - 2 < n) := Or.inr ⟨rfl, by omega⟩
  symm
  apply independent_lift_a_source_affine H hH edge hD a L hL offset A η G v
    (fun p q => independentScalarCoefficientSlice (c p q) L offset)
    (fun _ X => Real.exp (A X) • (Pi.single inp (1 : ℝ) : ι → ℝ))
    (fun p q t z Y w => independentScalarLiftTestSource q (c p q) A w inp t z Y)
    hh n out QG
    (fun u => independentScalarLiftTestSourceReserve (H + 2) (n - 1) (c hh (n - 1)) A u inp
      (fun m α => (Qc hh (n - 1) hpre1 m α u inp).restrictOrder (H + 2) (by omega)))
    (fun hn2 u => independentScalarLiftTestSourceReserve (H + 2) (n - 2) (c hh (n - 2)) A u inp
      (fun m α => (Qc hh (n - 2) (hpre2 hn2) m α u inp).restrictOrder (H + 2) (by omega)))
    (fun hhh j _ u => independentScalarLiftTestSourceReserve (H + 1 + D) (n - j)
      (c (hh - 1) (n - j)) A u inp (fun m α =>
        (Qc (hh - 1) (n - j) (Or.inl (by omega)) m α u inp).restrictOrder (H + 1 + D) (by omega)))
    Qa (fun p q _ t X z => independent_coefficient_slice_apply q (c p q) L offset A inp t X z)
    hn t z X

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine full independent flux reserves produce their actual cell means with retained matrix weights. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {d D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentLiftFluxMean_uniform_production (H : ℕ)
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
    ∃ Q : IndependentParameterSourceReserve H (fun t _ Y => fieldCellMean (fun z => independentLiftFluxSource edge a J A η G v c hh n out inp k t z Y)),
      ∀ r ≤ H, Q.budget r ≤ finiteMatrixPower M hh out inp *
        (((d : ℝ) + 1) ^ H * ((H + 1 : ℕ) *
          independentLiftFluxProductionCost H D n count A η BG BV BE B)) := by
  obtain ⟨Q, hQ⟩ := independentLiftFlux_uniform_production H edge a J hJ A η G v c
    hh n hn hhpos out inp k QG Qv Qc Qa M hM count BG BV BE B hBG hBV hBE hB
    hG hv hc he hm hlen
  exact ⟨Q.mean, Q.mean_uniform_budget (finiteMatrixPower M hh out inp)
    (independentLiftFluxProductionCost H D n count A η BG BV BE B) hQ⟩

end AVRegularity.EntryWeakProofs
end
end

section
/-! The moving centered difference is the literal recentered native geometry chart. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem centeredGeometryChart_recenter_scale (D : OCData) (A : RealChain)
    (hA : A.WellSlotted) (ρ θ u : ℝ) (X W : Vec 2) :
    centeredGeometryChart ((A.recenter D (ρ • X)).geom D) (ρ * θ) u W =
      θ⁻¹ • (centeredGeometryChart (A.geom D) ρ u (X + θ • W) -
        centeredGeometryChart (A.geom D) ρ u X) := by
  rw [geom_recenter D A hA (ρ • X), centeredGeometryChart_difference]
  simp only [centeredGeometryChart, mul_inv_rev, smul_smul, smul_add, add_assoc]

end AVRegularity.EntryWeakProofs
end
end

section
/-! The last fresh stored child has exactly the independent mixed chart model. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem independentFreshScaledStepChart_eq_model {r : ℕ} (D : OCData) (A : RealChain) (hA : A.WellSlotted)
    (slots : Fin (r + 1) → ℤ) (birthLength : Fin (r + 1) → ℝ)
    (ρ θ ell u : ℝ) (hρ : ρ ≠ 0) (hθ : θ ≠ 0) (he : D.eps (A.ctxLevel + r) ≠ 0)
    (hscale : D.eps (A.ctxLevel + r) = ρ * θ) (hbirth : birthLength (Fin.last r) = ρ * ell)
    (Y : Vec (4 * (r + 1)) × Vec 2) :
    let B := fun P => independentFreshChain A (fun j => slots j.castSucc)
      (fun j => birthLength j.castSucc) P
    let parentSlot := (A.slots ++ List.ofFn (fun j : Fin r => slots j.castSucc)).getLastD 0
    let anchor := D.slotAnchor (A.ctxLevel + r + 1) (slots (Fin.last r))
    centeredGeometryChart ((independentFreshChain A slots birthLength Y.1).geom D)
      (D.eps (A.ctxLevel + r)) u Y.2 =
      independentCenteredChildChart D (A.ctxLevel + r) parentSlot u anchor
        (fun Z : Vec (4 * r) × Vec 2 => centeredGeometryChart ((B Z.1).geom D) ρ u Z.2)
        (fun Z : Vec (4 * r) × Vec 2 => centeredGeometryChartInv ((B Z.1).geom D) ρ anchor Z.2)
        (fun Z : Vec (4 * r) × Vec 2 => centeredGeometryChart ((B Z.1).geom D) ρ anchor Z.2)
        θ (independentFreshScaledStepCoordinates r ell Y) := by
  dsimp only
  let B := fun P => independentFreshChain A (fun j => slots j.castSucc)
    (fun j => birthLength j.castSucc) P
  let p := independentFreshPrefixProjection r Y.1
  let c := independentFreshChild birthLength (Fin.last r) Y.1
  have hc : c.center = ρ • (ell • independentFreshChildProjection (Fin.last r) false Y.1) := by
    rw [independentFreshChild_center, hbirth, smul_smul]
  have hg : ChainGeometry.InvLaw ((B p).geom D) := actualOffset_inverse_law D (B p)
  rw [independentFreshChain_geom_succ D A hA]
  exact childGeom_chart_eq_independentCenteredChildChart D (A.ctxLevel + r) (B p).slot
    (fun P => (B P).geom D) p hg
    (D.slotAnchor (A.ctxLevel + r + 1) (slots (Fin.last r))) u ρ θ
    hρ hθ he hscale c (ell • independentFreshChildProjection (Fin.last r) false Y.1) Y.2 hc

end AVRegularity.EntryWeakProofs
end
end

section
/-! The last stored inverse child chart uses the same reverse-time independent model. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem independentFreshScaledStepChartInv_eq_model {r : ℕ} (D : OCData) (A : RealChain) (hA : A.WellSlotted)
    (slots : Fin (r + 1) → ℤ) (birthLength : Fin (r + 1) → ℝ)
    (ρ θ ell u : ℝ) (hρ : ρ ≠ 0) (hθ : θ ≠ 0) (he : D.eps (A.ctxLevel + r) ≠ 0)
    (hscale : D.eps (A.ctxLevel + r) = ρ * θ) (hbirth : birthLength (Fin.last r) = ρ * ell)
    (Y : Vec (4 * (r + 1)) × Vec 2) :
    let B := fun P => independentFreshChain A (fun j => slots j.castSucc)
      (fun j => birthLength j.castSucc) P
    let parentSlot := (A.slots ++ List.ofFn (fun j : Fin r => slots j.castSucc)).getLastD 0
    let anchor := D.slotAnchor (A.ctxLevel + r + 1) (slots (Fin.last r))
    centeredGeometryChartInv ((independentFreshChain A slots birthLength Y.1).geom D)
      (D.eps (A.ctxLevel + r)) u Y.2 =
      independentCenteredChildChart D (A.ctxLevel + r) parentSlot anchor u
        (fun Z : Vec (4 * r) × Vec 2 => centeredGeometryChart ((B Z.1).geom D) ρ anchor Z.2)
        (fun Z : Vec (4 * r) × Vec 2 => centeredGeometryChartInv ((B Z.1).geom D) ρ u Z.2)
        (fun Z : Vec (4 * r) × Vec 2 => centeredGeometryChart ((B Z.1).geom D) ρ u Z.2)
        θ (independentCenteredChildReanchorInput D (A.ctxLevel + r) parentSlot u anchor θ
          (independentFreshScaledStepCoordinates r ell Y)) := by
  dsimp only
  let B := fun P => independentFreshChain A (fun j => slots j.castSucc)
    (fun j => birthLength j.castSucc) P
  let p := independentFreshPrefixProjection r Y.1
  let c := independentFreshChild birthLength (Fin.last r) Y.1
  have hc : c.center = ρ • (ell • independentFreshChildProjection (Fin.last r) false Y.1) := by
    rw [independentFreshChild_center, hbirth, smul_smul]
  have hg : ChainGeometry.InvLaw ((B p).geom D) := actualOffset_inverse_law D (B p)
  rw [independentFreshChain_geom_succ D A hA]
  exact childGeom_inverse_chart_eq_independentCenteredChildChart D (A.ctxLevel + r) (B p).slot
    (fun P => (B P).geom D) p hg
    (D.slotAnchor (A.ctxLevel + r + 1) (slots (Fin.last r))) u ρ θ
    hρ hθ he hscale c (ell • independentFreshChildProjection (Fin.last r) false Y.1) Y.2 hc

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine finite-flow closeness is uniform over every fresh independent center and phase. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

theorem uniform_fresh_native_spatial_closeness (α s q : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (J : ℕ) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ D : OCData,
      D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      ∀ A : RealChain, M ≤ A.baseLevel → A.children = [] → ∀ p : ℕ → ℤ, A.slots = [p 0] →
      (∀ n ≤ J, Odd (p n)) →
      (∀ n < J, IsScheduledIn D (A.baseLevel + 1 + n) (p (n + 1)) (p n)) →
      ∀ birthLength : ℕ → ℝ, ∀ n ≤ J, ∀ P : Vec (4 * n), ∀ u ∈ nativeWeakChartWindow D A.baseLevel J p n,
      ∀ x, let g := (independentFreshChain A (fun j : Fin n => p (j + 1))
        (fun j => birthLength j) P).geom D
      ‖fderiv ℝ (fun y => g.1 u y g.2.2) x - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1 ∧
      ‖fderiv ℝ (fun y => g.1 g.2.2 y u) x - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1 := by
  obtain ⟨M, hM, hclose⟩ := uniform_finite_weak_chart_eventually_close α s q hα₀ hα₁ hs₀ hs₁ hq Λ hΛ ζ hζ J
  refine ⟨M, hM, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq A hAM hchildren p hslots hp hs birthLength n hn P u hu x
  dsimp only
  rw [independentFreshChain_geom_eq_indexed D A p hchildren hslots birthLength P]
  rw [finiteWeakChainGeom_anchor]
  have hΛ₁ : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have ha : |D.slotAnchor (A.baseLevel + 1 + n) (p n) -
      D.slotAnchor (A.baseLevel + 1 + n) (p n)| ≤
      finiteChainWindowRadius J n * ocTauPP D.α D.q D.Λ (A.baseLevel + 1 + n) :=
    nativeWeakChartWindow_anchor D hΛ₁ A.baseLevel J p n
  have hb := hclose D hDα hDq hDΛ hDζ hseq A.baseLevel hAM A.base p
    (independentFreshChildSeq birthLength P) hp hs n hn
  exact ⟨(hb u _ hu ha x).trans (by norm_num), (hb _ u ha hu x).trans (by norm_num)⟩

end AVRegularity.EntryWeakProofs
end
end

section
/-! Earlier disk reserves also produce the full inverse mixed jets after genuine re-anchoring. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem centered_native_inverse_mixed_production
    (D : OCData) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (m : ℕ) (slot : ℤ) (hp : Odd slot) (u r : ℝ)
    (hsmall : |u - r| * ocA D.α D.q D.Λ m ≤ 1)
    (g : P → ChainGeom) (p : P) (hg : GeomSpatialSmooth (g p))
    (ρ : ℝ) (hρ : 0 < ρ) (θ : ℝ) (hθ : θ ≠ 0) (hθ₁ : |θ| ≤ 1)
    (hforward : ∀ x, ‖fderiv ℝ (fun y => (g p).1 u y (g p).2.2) x -
      ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1)
    (hinverse : ∀ x, ‖fderiv ℝ (fun y => (g p).1 (g p).2.2 y u) x -
      ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1)
    (K n : ℕ) (hn : 1 ≤ n) (hnK : n ≤ K) (B : ℝ) (hB : 1 ≤ B)
    (C phase H : Vec 2) (hC : ‖C‖ ≤ 1) (S : ℝ) (hH : ‖H‖ ≤ S) :
    let Fr := fun Z : P × Vec 2 => centeredGeometryChart (g Z.1) ρ r Z.2
    let Iu := fun Z : P × Vec 2 => centeredGeometryChartInv (g Z.1) ρ u Z.2
    let Fu := fun Z : P × Vec 2 => centeredGeometryChart (g Z.1) ρ u Z.2
    ContDiff ℝ (⊤ : ℕ∞) Fr → ContDiff ℝ (⊤ : ℕ∞) Iu → ContDiff ℝ (⊤ : ℕ∞) Fu →
    (∀ f ∈ [Fr, Iu, Fu], ∀ i, 1 ≤ i → i ≤ K + 1 → ∀ X : Vec 2,
      ‖X‖ ≤ centeredParentRadius (2 * Real.pi) S →
      ‖iteratedFDeriv ℝ i f (p, X)‖ ≤ B) →
    ‖iteratedFDeriv ℝ n (independentCenteredChildInverseModel D m slot u r Fr Iu Fu θ)
      (p, C, phase, H)‖ ≤ nativeMixedChartInverseCost K B S := by
  dsimp only
  intro hFr hIu hFu hb
  let Fr := fun Z : P × Vec 2 => centeredGeometryChart (g Z.1) ρ r Z.2
  let Iu := fun Z : P × Vec 2 => centeredGeometryChartInv (g Z.1) ρ u Z.2
  let Fu := fun Z : P × Vec 2 => centeredGeometryChart (g Z.1) ρ u Z.2
  let F := independentCenteredChildChart D m slot r u Fr Iu Fu θ
  let G := independentCenteredChildReanchorInput (P := P) D m slot u r θ
  let A := max (independentCenteredChildChartMixedCost K B 2 S) (1 + (2 * Real.pi) ^ (K + 1))
  have hA : 1 ≤ A := (le_add_of_nonneg_right (by positivity)).trans (le_max_right _ _)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    independentCenteredChildChart_contDiff D m slot r u Fr Iu Fu hFr hIu hFu θ
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := independentCenteredChildReanchorInput_contDiff D m slot u r θ
  have hcenter : ‖(G (p, C, phase, H)).2.1‖ ≤ 1 + 2 * Real.pi :=
    independentCenteredChildBase_value_le D hΛ hζ m slot hp u r θ hsmall hθ₁
      (p, C, phase, H) 1 hC
  have hsmall' : |r - u| * ocA D.α D.q D.Λ m ≤ 1 := by
    simpa only [abs_sub_comm] using hsmall
  change ‖iteratedFDeriv ℝ n (F ∘ G) (p, C, phase, H)‖ ≤ K.factorial * A ^ (K + 1)
  apply finite_positive_jet_composition_bound F G hF hG K n hn hnK (p, C, phase, H) A hA
  · intro i hi hiK
    exact (centered_native_forward_mixed_production D hΛ hζ m slot hp r u hsmall'
      g p hg ρ hρ θ hθ hθ₁ hforward hinverse K i hi hiK B hB
      (G (p, C, phase, H)).2.1 (G (p, C, phase, H)).2.2.1 H hcenter S hH
      hFr hIu hFu hb).trans (le_max_left _ _)
  · intro i hi hiK
    exact (independentCenteredChildReanchorInput_positive_jet_bound D hΛ hζ m slot hp u r θ
      hsmall hθ₁ K i hi hiK (p, C, phase, H)).trans (le_max_right _ _)

end AVRegularity.EntryWeakProofs
end
end
end

section
section
/-! Exact affine normalization of the physical flux from genuine earlier test fields. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {d D H : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independent_lift_flux_affine
    (edge : ConstituentEdges D (fun _ : ι => ℝ)) (hD : 1 ≤ D)
    (a : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec d → Vec 2)
    (Qa : ∀ v u e, ∀ γ ∈ edge v u e, ∀ α, IndependentParameterSourceReserve H (a v u e γ α))
    (J : Vec 2 →L[ℝ] Vec d) (hJ : ‖J‖ ≤ 1) (offset : Vec d) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → Vec d → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (F : ℕ → ℕ → ℝ → Vec 2 → Vec d → ι → ℝ)
    (hh n : ℕ) (hn : 2 ≤ n) (hhpos : hh ≠ 0) (out inp : ι) (k : Fin 2)
    (Qf : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ w,
      IndependentParameterSourceReserve (H + D + 1) (fun t z Y => F p q t z Y w))
    (hcopy : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → ∀ t X z,
      liftApply q (Cc p q) (fun _ X => Real.exp (A X) • Pi.single inp (1 : ℝ)) t X z =
        Real.exp (A X) • F p q t z (J X + offset)) (t : ℝ) (z X : Vec 2) :
    (Real.exp (A X))⁻¹ •
      (liftFluxX ⟨η, fun t X => G t (J X + offset), v,
        independentConstituentEdgeSlice edge a Qa J offset⟩ Cc
        (fun _ X => Real.exp (A X) • Pi.single inp (1 : ℝ)) hh n t X z k) out =
      independentLiftFluxCrossSource J A η G v (fun t z Y => F hh (n - 1) t z Y out)
        (fun t z Y => F hh (n - 2) t z Y out) k t z (J X + offset) -
      Real.sqrt η • ∑ j ∈ Finset.Icc 1 (min D n),
        independentSourceFluxComponentCoefficient edge a J A η (F (hh - 1) (n - j))
          k (j - 1) out t z (J X + offset) := by
  have hp₁ : hh < hh ∨ (hh = hh ∧ n - 1 < n) := Or.inr ⟨rfl, by omega⟩
  have hp₂ : hh < hh ∨ (hh = hh ∧ n - 2 < n) := Or.inr ⟨rfl, by omega⟩
  have hc (p q : ℕ) (hp : p < hh ∨ (p = hh ∧ q < n)) (w : ι) :
      (fun t z X => normalizedLiftTestField (Cc p q) q A inp w 1 t X z) =
      (fun t z X => F p q t z (J X + offset) w) := by
    funext t z X
    unfold normalizedLiftTestField
    have he := congrFun (hcopy p q hp t X z) w
    rw [he]
    simp only [Pi.smul_apply, smul_smul, inv_mul_cancel₀ (Real.exp_ne_zero _), one_smul]
  let Q₁ := fun w => ((Qf hh (n - 1) hp₁ w).restrictOrder (H + 1) (by omega)).affineSlice J hJ offset
  let Q₂ := fun w => ((Qf hh (n - 2) hp₂ w).restrictOrder (H + 1) (by omega)).affineSlice J hJ offset
  rw [normalizedLiftFluxX_decomposition H _ Cc A hh n hn hhpos inp out k
    (fun w => (Q₁ w).congrSource (hc hh (n - 1) hp₁ w).symm)
    (fun w => (Q₂ w).congrSource (hc hh (n - 2) hp₂ w).symm)]
  simp only [hc hh (n - 1) hp₁ out, hc hh (n - 2) hp₂ out]
  rw [independent_lift_flux_cross_affine J hJ offset A η G v _ _
    ((Qf hh (n - 1) hp₁ out).restrictOrder (H + 1) (by omega))
    ((Qf hh (n - 2) hp₂ out).restrictOrder (H + 1) (by omega))]
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  have hp : hh - 1 < hh ∨ (hh - 1 = hh ∧ n - j < n) := Or.inl (by omega)
  have hfield : liftApply (n - j) (Cc (hh - 1) (n - j))
      (fun _ X => Real.exp (A X) • Pi.single inp (1 : ℝ)) t =
      (fun X z => Real.exp (A X) • F (hh - 1) (n - j) t z (J X + offset)) := by
    funext X z
    exact hcopy _ _ hp t X z
  rw [hfield]
  exact independent_source_flux_taylor_affine edge hD a Qa J hJ offset A η
    (F (hh - 1) (n - j)) (fun w => (Qf _ _ hp w).restrictOrder (H + D) (by omega))
    k (j - 1) (by have := (Finset.mem_Icc.mp hj).2; omega) out t z X

end AVRegularity.EntryWeakProofs
end
end

section
/-! Finite source and mean-correction prices precede all actual family data. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

def independentLiftAProductionMenuCost (K D N count : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (η BG BV BE B : ℝ) : ℝ :=
  ∑ h : Fin (K + 1), ∑ n : Fin (N + 1),
    independentLiftCoefficientAProductionCost h.val D n.val count A η BG BV BE B

theorem independentLiftAProductionMenuCost_nonneg (K D N count : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (η BG BV BE B : ℝ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 0 ≤ B) :
    0 ≤ independentLiftAProductionMenuCost K D N count A η BG BV BE B :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
    (fun _ _ => independentLiftCoefficientAProductionCost_nonneg _ _ _ _ _ _ _ _ _ _ hBG hBV hBE hB))

theorem finiteDoubleMenu_entry_le (K N h n : ℕ) (hh : h ≤ K) (hn : n ≤ N)
    (C : ℕ → ℕ → ℝ) (hC : ∀ h n, 0 ≤ C h n) :
    C h n ≤ ∑ k : Fin (K + 1), ∑ l : Fin (N + 1), C k.val l.val := by
  have hi : C h n ≤ ∑ l : Fin (N + 1), C h l.val :=
    Finset.single_le_sum (fun (l : Fin (N + 1)) _ => hC h l.val) (Finset.mem_univ (⟨n, by omega⟩ : Fin (N + 1)))
  have ho : (∑ l : Fin (N + 1), C h l.val) ≤
      ∑ k : Fin (K + 1), ∑ l : Fin (N + 1), C k.val l.val :=
    Finset.single_le_sum (fun (k : Fin (K + 1)) _ => Finset.sum_nonneg (fun (l : Fin (N + 1)) _ => hC k.val l.val))
      (Finset.mem_univ (⟨h, by omega⟩ : Fin (K + 1)))
  exact hi.trans ho

theorem independentLiftAProductionCost_le_menu (K D N count h n : ℕ) (hh : h ≤ K) (hn : n ≤ N)
    (A : Vec 2 →L[ℝ] ℝ) (η BG BV BE B : ℝ)
    (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 0 ≤ B) :
    independentLiftCoefficientAProductionCost h D n count A η BG BV BE B ≤
      independentLiftAProductionMenuCost K D N count A η BG BV BE B := by
  exact finiteDoubleMenu_entry_le K N h n hh hn
    (fun h n => independentLiftCoefficientAProductionCost h D n count A η BG BV BE B)
    (fun h n => independentLiftCoefficientAProductionCost_nonneg h D n count A η BG BV BE B hBG hBV hBE hB)

def independentLiftMeanCompositionCost (d H j : ℕ) (A : Vec 2 →L[ℝ] ℝ) (B BF : ℝ) : ℝ :=
  (liftApplyFiniteWordCount j : ℝ) *
    (‖ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)‖ * 2 ^ H * B *
      ((1 + ‖A‖) ^ j * (((d : ℝ) + 1) ^ (H + j) * ((H + j + 1 : ℕ) * BF))))

theorem independentLiftMeanCompositionCost_nonneg (d H j : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (B BF : ℝ) (hB : 0 ≤ B) (hBF : 0 ≤ BF) :
    0 ≤ independentLiftMeanCompositionCost d H j A B BF := by
  unfold independentLiftMeanCompositionCost
  positivity

end AVRegularity.EntryWeakProofs
end
end

section
/-! The finite mean-composition price is uniform over every retained derivative order. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentLiftMeanCompositionSourceReserve_uniform_matrix_budget (H j : ℕ)
    (c : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (L : Vec 2 →L[ℝ] Vec d) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ)
    (F : ℝ → Vec 2 → Vec d → ι → ℝ) (v : ι)
    (Qc : ∀ m : Fin (j + 1), ∀ α : DerivativeWord2 m.val, ∀ u,
      IndependentParameterSourceReserve H (fun t z Y => c m.val α t z Y v u))
    (QF : ∀ u, IndependentParameterSourceReserve (H + j) (fun t z Y => F t z Y u))
    (M : ι → ι → ℝ) (hM : ∀ v u, 0 ≤ M v u) (a b : ℕ) (w : ι)
    (B BF : ℝ) (hB : 0 ≤ B) (hBF : 0 ≤ BF)
    (hQc : ∀ m α u r, r ≤ H → (Qc m α u).budget r ≤ finiteMatrixPower M a v u * B)
    (hQF : ∀ u r, r ≤ H + j → (QF u).budget r ≤ finiteMatrixPower M b u w * BF)
    (r : ℕ) (hr : r ≤ H) :
    (independentLiftMeanCompositionSourceReserve H j c L hL A F v Qc QF).budget r ≤
      finiteMatrixPower M (a + b) v w * independentLiftMeanCompositionCost d H j A B BF := by
  have hb := independentLiftMeanCompositionSourceReserve_matrix_budget H j c L hL A F v Qc QF
    M hM a b w B BF hB hBF hQc hQF r hr
  apply hb.trans
  rw [mul_comm (finiteMatrixPower M (a + b) v w)]
  apply mul_le_mul_of_nonneg_right _ (finiteMatrixPower_nonneg M hM _ _ _)
  unfold independentLiftMeanCompositionCost
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg (pow_nonneg (by positivity) _)
    (mul_nonneg (pow_nonneg (by positivity) _) (mul_nonneg (Nat.cast_nonneg _) hBF)))
  apply mul_le_mul_of_nonneg_right _ hB
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hr) (norm_nonneg _)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Produced incoming fields agree with native path edges on their licensed slow slices. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.EntryWeakProofs
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {h H : ℕ}

theorem independentPathTemplate_fixed_context_clock_copy
    (G : GenStage D hr Dm bw j₀) (π : StagePath G h) (p : OddSlot)
    (anchor c : StageCtx D bw j₀ G.level p)
    (field : Fin h → (d : Finset.Icc 2 Dm) → DerivativeWord2 (d.val - 1) →
      ℝ → Vec 2 → P → Vec 2)
    (Q : ∀ v u d, ∀ γ ∈ pathEdges G π p anchor v u d, ∀ α,
      IndependentParameterSourceReserve H (independentPathTemplateField field v u d γ α))
    (L : Vec 2 →L[ℝ] P) (Y : P) (U : Set (Vec 2)) (clock t : ℝ)
    (hc : ∀ j d, d.val ≤ (G.fam.identity _ _ (π.step j).2.2).maxOrder →
      ∀ α X, X ∈ U → ∀ z,
        G.fam.flux p c _ _ (π.step j).2.2 d.val α (clock * t) X z =
          field j d α t z (L X + Y)) :
    SlowOpenEdgeEq U t (liftEdges clock 1 (pathEdges G π p c))
      (independentConstituentEdgeSlice (pathEdges G π p anchor)
        (independentPathTemplateField field) Q L Y) := by
  classical
  intro v u d
  unfold independentConstituentEdgeSlice liftEdges
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  unfold pathEdges
  split
  next hvu =>
    split
    next hd =>
      apply List.Forall₂.cons _ List.Forall₂.nil
      refine ⟨rfl, ?_⟩
      intro α X hX z
      simp only [one_smul, List.mem_singleton,
        independentPathTemplateField, dite_eq_left hvu.2]
      exact hc ⟨u.val, hvu.2⟩ d hd α X hX z
    · exact List.Forall₂.nil
  · exact List.Forall₂.nil

end AVRegularity.EntryWeakProofs
end
end

section
/-! Produced independent forcing and earlier coefficients copy the actual centered inverse source. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {d D H : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independent_lift_cell_source_affine
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec d → Vec 2)
    (L : Vec 2 →L[ℝ] Vec d) (hL : ‖L‖ ≤ 1) (offset : Vec d)
    (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → Vec d → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (c : ℕ → ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (Q : LiftOperatorData ι (fun _ => ℝ) D) (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ))
    (f : ℝ → Vec 2 → ι → ℝ) (hh n : ℕ) (out inp : ι)
    (QA : ∀ u, IndependentParameterSourceReserve H
      (independentLiftCoefficientASource edge a L A η G v c hh n u inp))
    (QM : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ p ∈ Finset.HasAntidiagonal.antidiagonal hh, ∀ u,
      IndependentParameterSourceReserve (H + j)
        (independentLiftCoefficientASource edge a L A η G v c p.2 (n - j) u inp))
    (hA : ∀ t z X u, independentLiftCoefficientASource edge a L A η G v c hh n u inp t z
      (L X + offset) = normalizedLiftASource Q Cc f hh n A t z X u)
    (hM : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      ∀ t z X u, independentLiftCoefficientASource edge a L A η G v c p.2 (n - j) u inp t z
        (L X + offset) = normalizedLiftASource Q Cc f p.2 (n - j) A t z X u)
    (t : ℝ) (z X : Vec 2)
    (hcopy : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      ∀ m : Fin (j + 1), ∀ α : DerivativeWord2 m.val, ∀ u,
      Cc p.1 j m.val α t X z out u 1 = c p.1 j m.val α t z (L X + offset) out u) :
    independentLiftCoefficientCellSource edge a L A η G v c hh n out inp t z (L X + offset) =
      normalizedLiftCellSource Q Cc f hh n A t z X out := by
  apply independent_centered_recurrence_eq_actual Q Cc f hh n A out
    (fun t z Y u => independentLiftCoefficientASource edge a L A η G v c hh n u inp t z Y)
    QA _ t z X (L X + offset) (hA t · X ·)
  intro j hj p hp
  exact (independent_lift_mean_composition_affine j (c p.1 j) Q Cc f p.2 (n - j) p.1
    L hL offset A _ (QM j hj p hp) (hM j hj p hp) out t z X (hcopy j hj p hp)).symm

end AVRegularity.EntryWeakProofs
end
end

section
/-! Ordered mean corrections retain the response of their produced positive coefficient factor. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentLiftMeanCompositionCost_response (H j : ℕ)
    (A : Vec 2 →L[ℝ] ℝ) (θ B BF : ℝ) :
    independentLiftMeanCompositionCost d H j A (θ * B) BF =
      θ * independentLiftMeanCompositionCost d H j A B BF := by
  unfold independentLiftMeanCompositionCost
  ring

theorem independentLiftMeanCompositionSource_uniform_response (H j : ℕ)
    (c : (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (L : Vec 2 →L[ℝ] Vec d) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ)
    (F : ℝ → Vec 2 → Vec d → ι → ℝ) (v : ι)
    (Qc : ∀ m : Fin (j + 1), ∀ α : DerivativeWord2 m.val, ∀ u,
      IndependentParameterSourceReserve H (fun t z Y => c m.val α t z Y v u))
    (QF : ∀ u, IndependentParameterSourceReserve (H + j) (fun t z Y => F t z Y u))
    (M : ι → ι → ℝ) (hM : ∀ v u, 0 ≤ M v u) (a b : ℕ) (w : ι)
    (θ B BF : ℝ) (hθ : 0 ≤ θ) (hB : 0 ≤ B) (hBF : 0 ≤ BF)
    (hQc : ∀ m α u r, r ≤ H → (Qc m α u).budget r ≤ (θ * finiteMatrixPower M a v u) * B)
    (hQF : ∀ u r, r ≤ H + j → (QF u).budget r ≤ finiteMatrixPower M b u w * BF)
    (r : ℕ) (hr : r ≤ H) :
    (independentLiftMeanCompositionSourceReserve H j c L hL A F v Qc QF).budget r ≤
      (θ * finiteMatrixPower M (a + b) v w) * independentLiftMeanCompositionCost d H j A B BF := by
  have hc m α u r (hr : r ≤ H) :
      (Qc m α u).budget r ≤ finiteMatrixPower M a v u * (θ * B) :=
    (hQc m α u r hr).trans_eq (by ring)
  have hb := independentLiftMeanCompositionSourceReserve_uniform_matrix_budget H j c L hL A F v
    Qc QF M hM a b w (θ * B) BF (mul_nonneg hθ hB) hBF hc hQF r hr
  rw [independentLiftMeanCompositionCost_response] at hb
  exact hb.trans_eq (by ring)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Constructed fluxes and their cell means preserve the same primitive phase translations. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs
variable {d D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentLiftFluxSource_translation_invariant
    (δ : Vec d) (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec d → Vec 2)
    (J : Vec 2 →L[ℝ] Vec d) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → Vec d → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (c : ℕ → ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (hG : ∀ t Y i j, G t (Y + δ) i j = G t Y i j)
    (ha : ∀ v u e γ, γ ∈ edge v u e → ∀ α, IndependentSourceTranslationInvariant δ (a v u e γ α))
    (hc : ∀ p q m α v u, IndependentSourceTranslationInvariant δ (fun t z Y => c p q m α t z Y v u))
    (hh n : ℕ) (out inp : ι) (k : Fin 2) :
    IndependentSourceTranslationInvariant δ (independentLiftFluxSource edge a J A η G v c hh n out inp k) := by
  let F := fun p q t z Y w => independentScalarLiftTestSource q (c p q) A w inp t z Y
  have hF (p q : ℕ) (w : ι) : IndependentSourceTranslationInvariant δ (fun t z Y => F p q t z Y w) :=
    independentScalarLiftTestSource_translation_invariant δ q (c p q) (hc p q) A w inp
  have hd (j : Fin 2) := (hF hh (n - 1) out).fastPartial j
  have hs (j : Fin 2) := (hF hh (n - 2) out).covariantSlow J A j
  intro t z Y
  have hcross : independentLiftFluxCrossSource J A η G v (fun t z Y => F hh (n - 1) t z Y out)
      (fun t z Y => F hh (n - 2) t z Y out) k t z (Y + δ) =
        independentLiftFluxCrossSource J A η G v (fun t z Y => F hh (n - 1) t z Y out)
          (fun t z Y => F hh (n - 2) t z Y out) k t z Y := by
    have hd' (j : Fin 2) := hd j t z Y
    dsimp only at hd'
    dsimp only [independentLiftFluxCrossSource]
    simp_rw [hF hh (n - 1) out t z Y, hG t Y, hd', hs _ t z Y]
  change _ - _ = _ - _
  rw [hcross]
  congr 1
  apply congrArg (fun w : ℝ => Real.sqrt η • w)
  apply Finset.sum_congr rfl
  intro j hj
  exact independentSourceFluxComponentCoefficient_translation_invariant δ edge a J A η
    (F (hh - 1) (n - j)) ha (hF (hh - 1) (n - j)) k (j - 1) out t z Y

end AVRegularity.EntryWeakProofs
end
end

section
/-! Every ordered mean correction is produced from genuine earlier fields at a common matrix price. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {d D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentLiftCorrection_uniform_production (H : ℕ)
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec d → Vec 2)
    (L : Vec 2 →L[ℝ] Vec d) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → Vec d → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (c : ℕ → ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (hh n : ℕ) (hn : 1 ≤ n) (hnD : n ≤ D) (out inp : ι)
    (j : ℕ) (hj : j ∈ Finset.Icc 1 (n - 2))
    (p : ℕ × ℕ) (hp : p ∈ Finset.HasAntidiagonal.antidiagonal hh)
    (QG : ∀ i j, IndependentParameterSourceReserve (H + D + 1) (fun t _ Y => G t Y i j))
    (Qv : ∀ i, IndependentParameterSourceReserve (H + D) (fun t z (_ : Vec d) => v t z i))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      IndependentParameterSourceReserve (H + 2 * D + 2) (fun t z Y => c p q m.val α t z Y v u))
    (Qa : ∀ v u e, ∀ γ ∈ edge v u e, ∀ α,
      IndependentParameterSourceReserve (H + D + 1) (a v u e γ α))
    (M : ι → ι → ℝ) (hM : ∀ v u, 0 ≤ M v u) (count : ℕ)
    (BG BV BE B : ℝ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 0 ≤ B)
    (hG : ∀ i j r, r ≤ H + D + 1 → (QG i j).budget r ≤ BG)
    (hv : ∀ i r, r ≤ H + D → (Qv i).budget r ≤ BV)
    (hc : ∀ p q hpq m α v u r, r ≤ H + 2 * D + 2 →
      (Qc p q hpq m α v u).budget r ≤ finiteMatrixPower M p v u * B)
    (he : ∀ w u e γ hγ α r, r ≤ H + D + 1 → (Qa w u e γ hγ α).budget r ≤ M w u * BE)
    (hmap : ∀ w u e γ, γ ∈ edge w u e → ‖γ.map‖ ≤ 1)
    (hlen : ∀ w u e, (edge w u e).length ≤ count) :
    ∃ Q : IndependentParameterSourceReserve H (independentLiftMeanCompositionSource j (c p.1 j) L A
      (fun t z Y w => independentLiftCoefficientASource edge a L A η G v c p.2 (n - j) w inp t z Y) out),
      ∀ r ≤ H, Q.budget r ≤ finiteMatrixPower M hh out inp *
        independentLiftMeanCompositionCost d H j A B
          (independentLiftAProductionMenuCost (H + D) D n count A η BG BV BE B) := by
  have hj' := Finset.mem_Icc.mp hj
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hpre : p.1 < hh ∨ (p.1 = hh ∧ j < n) := by
    by_cases hlt : p.1 < hh
    · exact Or.inl hlt
    · exact Or.inr ⟨by omega, by omega⟩
  have hmeanPre (r s : ℕ) (hrs : r < p.2 ∨ (r = p.2 ∧ s < n - j)) :
      r < hh ∨ (r = hh ∧ s < n) := by
    rcases hrs with hrs | ⟨hrs, hsn⟩
    · exact Or.inl (by omega)
    · by_cases hlt : r < hh
      · exact Or.inl hlt
      · exact Or.inr ⟨by omega, by omega⟩
  let BA := independentLiftAProductionMenuCost (H + D) D n count A η BG BV BE B
  have hBA := independentLiftAProductionMenuCost_nonneg (H + D) D n count A η BG BV BE B hBG hBV hBE hB
  have hprod w : ∃ Q : IndependentParameterSourceReserve (H + j)
      (independentLiftCoefficientASource edge a L A η G v c p.2 (n - j) w inp),
      ∀ r ≤ H + j, Q.budget r ≤ finiteMatrixPower M p.2 w inp * BA := by
    obtain ⟨Q, hQ⟩ := independentLiftCoefficientA_uniform_production (H + j) edge a L hL A η G v c
      p.2 (n - j) (by omega) w inp
      (fun i k => (QG i k).restrictOrder (H + j + 1) (by omega))
      (fun i => (Qv i).restrictOrder (H + j) (by omega))
      (fun r s hrs m α v u => (Qc r s (hmeanPre r s hrs) m α v u).restrictOrder
        ((H + j) + D + 2) (by omega))
      (fun v u e γ hγ α => (Qa v u e γ hγ α).restrictOrder (H + j + 1) (by omega))
      M hM count BG BV BE B hBG hBV hBE hB
      (fun i k r hr => hG i k r (by omega)) (fun i r hr => hv i r (by omega))
      (fun r s hrs m α v u k hk => hc r s (hmeanPre r s hrs) m α v u k (by omega))
      (fun u e γ hγ α r hr => he w u e γ hγ α r (by omega)) (hmap w) (hlen w)
    refine ⟨Q, ?_⟩
    intro r hr
    exact (hQ r hr).trans (mul_le_mul_of_nonneg_left
      (independentLiftAProductionCost_le_menu (H + D) D n count (H + j) (n - j)
        (by omega) (Nat.sub_le _ _) A η BG BV BE B hBG hBV hBE hB)
      (finiteMatrixPower_nonneg M hM p.2 w inp))
  choose QM hQM using hprod
  let QC := fun m α w => (Qc p.1 j hpre m α out w).restrictOrder H (by omega)
  refine ⟨independentLiftMeanCompositionSourceReserve H j (c p.1 j) L hL A _ out QC QM, ?_⟩
  intro r hr
  have hh' := independentLiftMeanCompositionSourceReserve_uniform_matrix_budget H j (c p.1 j)
    L hL A _ out QC QM M hM p.1 p.2 inp B BA hB hBA
    (fun m α w s hs => hc p.1 j hpre m α out w s (by omega)) hQM r hr
  simpa only [hp'] using hh'

end AVRegularity.EntryWeakProofs
end
end

section
/-! Actual ordered corrections retain the response budget of their produced coefficient factor. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {d D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentLiftCorrection_uniform_response (H : ℕ)
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec d → Vec 2)
    (L : Vec 2 →L[ℝ] Vec d) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → Vec d → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (c : ℕ → ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (hh n : ℕ) (hn : 1 ≤ n) (hnD : n ≤ D) (out inp : ι)
    (j : ℕ) (hj : j ∈ Finset.Icc 1 (n - 2))
    (p : ℕ × ℕ) (hp : p ∈ Finset.HasAntidiagonal.antidiagonal hh)
    (QG : ∀ i j, IndependentParameterSourceReserve (H + D + 1) (fun t _ Y => G t Y i j))
    (Qv : ∀ i, IndependentParameterSourceReserve (H + D) (fun t z (_ : Vec d) => v t z i))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      IndependentParameterSourceReserve (H + 2 * D + 2) (fun t z Y => c p q m.val α t z Y v u))
    (Qa : ∀ v u e, ∀ γ ∈ edge v u e, ∀ α,
      IndependentParameterSourceReserve (H + D + 1) (a v u e γ α))
    (M : ι → ι → ℝ) (hM : ∀ v u, 0 ≤ M v u) (count : ℕ)
    (θ BG BV BE B : ℝ) (hθ : 0 ≤ θ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 0 ≤ B)
    (hG : ∀ i j r, r ≤ H + D + 1 → (QG i j).budget r ≤ BG)
    (hv : ∀ i r, r ≤ H + D → (Qv i).budget r ≤ BV)
    (hc : ∀ p q hpq m α v u r, r ≤ H + 2 * D + 2 →
      (Qc p q hpq m α v u).budget r ≤ finiteMatrixPower M p v u * B)
    (he : ∀ w u e γ hγ α r, r ≤ H + D + 1 → (Qa w u e γ hγ α).budget r ≤ M w u * BE)
    (hmap : ∀ w u e γ, γ ∈ edge w u e → ‖γ.map‖ ≤ 1)
    (hlen : ∀ w u e, (edge w u e).length ≤ count)
    (QC : ∀ m : Fin (j + 1), ∀ α : DerivativeWord2 m.val, ∀ w,
      IndependentParameterSourceReserve H (fun t z Y => c p.1 j m.val α t z Y out w))
    (hQC : ∀ m α w r, r ≤ H → (QC m α w).budget r ≤ (θ * finiteMatrixPower M p.1 out w) * B) :
    ∃ Q : IndependentParameterSourceReserve H (independentLiftMeanCompositionSource j (c p.1 j) L A
      (fun t z Y w => independentLiftCoefficientASource edge a L A η G v c p.2 (n - j) w inp t z Y) out),
      ∀ r ≤ H, Q.budget r ≤ (θ * finiteMatrixPower M hh out inp) *
        independentLiftMeanCompositionCost d H j A B
          (independentLiftAProductionMenuCost (H + D) D n count A η BG BV BE B) := by
  have hj' := Finset.mem_Icc.mp hj
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hmeanPre (r s : ℕ) (hrs : r < p.2 ∨ (r = p.2 ∧ s < n - j)) :
      r < hh ∨ (r = hh ∧ s < n) := by
    rcases hrs with hrs | ⟨hrs, hsn⟩
    · exact Or.inl (by omega)
    · by_cases hlt : r < hh
      · exact Or.inl hlt
      · exact Or.inr ⟨by omega, by omega⟩
  let BA := independentLiftAProductionMenuCost (H + D) D n count A η BG BV BE B
  have hBA := independentLiftAProductionMenuCost_nonneg (H + D) D n count A η BG BV BE B hBG hBV hBE hB
  have hprod w : ∃ Q : IndependentParameterSourceReserve (H + j)
      (independentLiftCoefficientASource edge a L A η G v c p.2 (n - j) w inp),
      ∀ r ≤ H + j, Q.budget r ≤ finiteMatrixPower M p.2 w inp * BA := by
    obtain ⟨Q, hQ⟩ := independentLiftCoefficientA_uniform_production (H + j) edge a L hL A η G v c
      p.2 (n - j) (by omega) w inp
      (fun i k => (QG i k).restrictOrder (H + j + 1) (by omega))
      (fun i => (Qv i).restrictOrder (H + j) (by omega))
      (fun r s hrs m α v u => (Qc r s (hmeanPre r s hrs) m α v u).restrictOrder
        ((H + j) + D + 2) (by omega))
      (fun v u e γ hγ α => (Qa v u e γ hγ α).restrictOrder (H + j + 1) (by omega))
      M hM count BG BV BE B hBG hBV hBE hB
      (fun i k r hr => hG i k r (by omega)) (fun i r hr => hv i r (by omega))
      (fun r s hrs m α v u k hk => hc r s (hmeanPre r s hrs) m α v u k (by omega))
      (fun u e γ hγ α r hr => he w u e γ hγ α r (by omega)) (hmap w) (hlen w)
    refine ⟨Q, ?_⟩
    intro r hr
    exact (hQ r hr).trans (mul_le_mul_of_nonneg_left
      (independentLiftAProductionCost_le_menu (H + D) D n count (H + j) (n - j)
        (by omega) (Nat.sub_le _ _) A η BG BV BE B hBG hBV hBE hB)
      (finiteMatrixPower_nonneg M hM p.2 w inp))
  choose QM hQM using hprod
  refine ⟨independentLiftMeanCompositionSourceReserve H j (c p.1 j) L hL A _ out QC QM, ?_⟩
  intro r hr
  have hh' := independentLiftMeanCompositionSource_uniform_response H j (c p.1 j)
    L hL A _ out QC QM M hM p.1 p.2 inp θ B BA hθ hB hBA hQC hQM r hr
  simpa only [hp'] using hh'

end AVRegularity.EntryWeakProofs
end
end

section
/-! Complete independent inverse forcing retains the exact stored matrix grade at one finite menu price. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {d D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def independentLiftCellProductionCost (d H D hh n count : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (η BG BV BE B : ℝ) : ℝ :=
  let BA := independentLiftAProductionMenuCost (H + D) D n count A η BG BV BE B
  (1 + ((d : ℝ) + 1) ^ H * (H + 1 : ℕ)) * BA +
    ∑ j ∈ Finset.Icc 1 (n - 2), ∑ _p ∈ Finset.HasAntidiagonal.antidiagonal hh,
      independentLiftMeanCompositionCost d H j A B BA

theorem independentLiftCellProductionCost_nonneg (d H D hh n count : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (η BG BV BE B : ℝ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 0 ≤ B) :
    0 ≤ independentLiftCellProductionCost d H D hh n count A η BG BV BE B := by
  have hBA := independentLiftAProductionMenuCost_nonneg (H + D) D n count A η BG BV BE B hBG hBV hBE hB
  exact add_nonneg (mul_nonneg (by positivity) hBA)
    (Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun _ _ =>
      independentLiftMeanCompositionCost_nonneg d H j A B _ hB hBA)))

theorem independentLiftCoefficientCellSource_uniform_production (H : ℕ)
    (edge : ConstituentEdges D (fun _ : ι => ℝ))
    (a : ∀ (_v _u : ι) (e : Finset.Icc 2 D), Constituent e.val ℝ ℝ →
      DerivativeWord2 (e.val - 1) → ℝ → Vec 2 → Vec d → Vec 2)
    (L : Vec 2 →L[ℝ] Vec d) (hL : ‖L‖ ≤ 1) (A : Vec 2 →L[ℝ] ℝ) (η : ℝ)
    (G : ℝ → Vec d → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2)
    (c : ℕ → ℕ → (m : ℕ) → DerivativeWord2 m → ℝ → Vec 2 → Vec d → ι → ι → ℝ)
    (hh n : ℕ) (hn : 1 ≤ n) (hnD : n ≤ D) (out inp : ι)
    (QG : ∀ i j, IndependentParameterSourceReserve (H + D + 1) (fun t _ Y => G t Y i j))
    (Qv : ∀ i, IndependentParameterSourceReserve (H + D) (fun t z (_ : Vec d) => v t z i))
    (Qc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) →
      ∀ m : Fin (q + 1), ∀ α : DerivativeWord2 m.val, ∀ v u,
      IndependentParameterSourceReserve (H + 2 * D + 2) (fun t z Y => c p q m.val α t z Y v u))
    (Qa : ∀ v u e, ∀ γ ∈ edge v u e, ∀ α,
      IndependentParameterSourceReserve (H + D + 1) (a v u e γ α))
    (M : ι → ι → ℝ) (hM : ∀ v u, 0 ≤ M v u) (count : ℕ)
    (BG BV BE B : ℝ) (hBG : 0 ≤ BG) (hBV : 0 ≤ BV) (hBE : 0 ≤ BE) (hB : 0 ≤ B)
    (hG : ∀ i j r, r ≤ H + D + 1 → (QG i j).budget r ≤ BG)
    (hv : ∀ i r, r ≤ H + D → (Qv i).budget r ≤ BV)
    (hc : ∀ p q hpq m α v u r, r ≤ H + 2 * D + 2 →
      (Qc p q hpq m α v u).budget r ≤ finiteMatrixPower M p v u * B)
    (he : ∀ w u e γ hγ α r, r ≤ H + D + 1 → (Qa w u e γ hγ α).budget r ≤ M w u * BE)
    (hmap : ∀ w u e γ, γ ∈ edge w u e → ‖γ.map‖ ≤ 1)
    (hlen : ∀ w u e, (edge w u e).length ≤ count) :
    ∃ Q : IndependentParameterSourceReserve H
      (independentLiftCoefficientCellSource edge a L A η G v c hh n out inp),
      ∀ r ≤ H, Q.budget r ≤ finiteMatrixPower M hh out inp *
        independentLiftCellProductionCost d H D hh n count A η BG BV BE B := by
  let BA := independentLiftAProductionMenuCost (H + D) D n count A η BG BV BE B
  have hprodA : ∃ Q : IndependentParameterSourceReserve H
      (independentLiftCoefficientASource edge a L A η G v c hh n out inp),
      ∀ r ≤ H, Q.budget r ≤ finiteMatrixPower M hh out inp * BA := by
    obtain ⟨Q, hQ⟩ := independentLiftCoefficientA_uniform_production H edge a L hL A η G v c
      hh n hn out inp
      (fun i j => (QG i j).restrictOrder (H + 1) (by omega))
      (fun i => (Qv i).restrictOrder H (by omega))
      (fun p q hpq m α v u => (Qc p q hpq m α v u).restrictOrder (H + D + 2) (by omega))
      (fun v u e γ hγ α => (Qa v u e γ hγ α).restrictOrder (H + 1) (by omega))
      M hM count BG BV BE B hBG hBV hBE hB
      (fun i j r hr => hG i j r (by omega)) (fun i r hr => hv i r (by omega))
      (fun p q hpq m α v u r hr => hc p q hpq m α v u r (by omega))
      (fun u e γ hγ α r hr => he out u e γ hγ α r (by omega)) (hmap out) (hlen out)
    refine ⟨Q, ?_⟩
    intro r hr
    exact (hQ r hr).trans (mul_le_mul_of_nonneg_left
      (independentLiftAProductionCost_le_menu (H + D) D n count H n (by omega) le_rfl
        A η BG BV BE B hBG hBV hBE hB) (finiteMatrixPower_nonneg M hM hh out inp))
  obtain ⟨QA, hQA⟩ := hprodA
  choose QT hQT using fun j (hj : j ∈ Finset.Icc 1 (n - 2)) p
    (hp : p ∈ Finset.HasAntidiagonal.antidiagonal hh) =>
      independentLiftCorrection_uniform_production H edge a L hL A η G v c hh n hn hnD out inp
        j hj p hp QG Qv Qc Qa M hM count BG BV BE B hBG hBV hBE hB hG hv hc he hmap hlen
  refine ⟨independentCenteredRecurrenceSourceReserve hh n _ _ QA QT, ?_⟩
  intro r hr
  exact independentCenteredRecurrenceSourceReserve_priced_budget hh n _ _ QA QT
    (finiteMatrixPower M hh out inp) BA (fun j _ => independentLiftMeanCompositionCost d H j A B BA)
    hQA hQT r hr

end AVRegularity.EntryWeakProofs
end
end
end
