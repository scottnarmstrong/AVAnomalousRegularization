-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.GenSem.Op.Chart
import AVRegularity.Proofs.GenSem.Jet.Chart

@[expose] public noncomputable section

section
open Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.GenSem

/-! **Extraction of the coefficient `fluxCoeff` of an array flux operator.** Evaluating
`L f y = applyArr K A f y 0` on the monomial `mono 0 I` at `0` gives the symmetrized sum of the
entries of order `|I|` at `0`; the value is represented when the entry values at `0` are. -/

section
/-- **Evaluation on a monomial at the center.** -/
theorem applyArr_mono_zero (K : ℕ) (A : CArr) {m : ℕ} (I : DerivativeWord2 m) (hm : m ≤ K) :
    applyArr K A (fun Y => ∏ j, (Y - 0) (I j)) 0 0 = ∑ σ : Equiv.Perm (Fin m), A m (I ∘ σ) 0 0 :=
  applyArr_mono K A 0 0 I hm

/-- **`fluxCoeff` of an array flux operator** at `0`. -/
theorem fluxCoeff_applyArr (K : ℕ) (A : Fin 2 → CArr) (d : ℕ) (I : DerivativeWord2 (d - 1))
    (hd : d - 1 ≤ K) (c : Fin 2) :
    fluxCoeff (fun g y k => applyArr K (A k) g y 0) d I 0 c =
      (((d - 1).factorial : ℝ)⁻¹) * ∑ σ : Equiv.Perm (Fin (d - 1)), A c (d - 1) (I ∘ σ) 0 0 := by
  unfold fluxCoeff
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [applyArr_mono_zero K (A c) I hd]

variable {Λ : Type*} {R : (Λ → ℝ) → Prop}

/-- The extracted coefficient is represented when the entry values at `0` are. -/
theorem rep_fluxCoeff_applyArr (hR : RepAlg R) {K : ℕ} {A : Λ → Fin 2 → CArr} (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (hd : d - 1 ≤ K) (c : Fin 2)
    (hA : ∀ m (α : DerivativeWord2 m), R (fun l => A l c m α 0 0)) :
    R (fun l => fluxCoeff (fun g y k => applyArr K (A l k) g y 0) d I 0 c) := by
  have e : (fun l => fluxCoeff (fun g y k => applyArr K (A l k) g y 0) d I 0 c) =
      fun l => (((d - 1).factorial : ℝ)⁻¹) *
        ∑ σ : Equiv.Perm (Fin (d - 1)), A l c (d - 1) (I ∘ σ) 0 0 :=
    funext fun l => fluxCoeff_applyArr K (A l) d I hd c
  rw [e]
  exact hR.smul (hR.finsetSum _ fun σ _ => hA _ _) _
end

/-! **Represented jets of the transformed array.** Generic over the index `Λ` and the
algebra `R` (family instance and context instance alike). The chart data are hypotheses:
`N l 0 = 0`, `N` smooth with represented components (order `r`); `Ψ` smooth with represented
components of order `r + K`; the matrix `M` has represented entries (order `r`, smooth);
the input arrays have represented jets (order `r`). Then every entry of `chartArr` has represented
jets of order `r`. -/

section
variable {Λ : Type*} {R : (Λ → ℝ) → Prop}

theorem arrJetG_chartArr (hR : RepAlg R) {r K : ℕ} {M : Λ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {N Ψ : Λ → Vec 2 → Vec 2} {A : Λ → Fin 2 → CArr}
    (hN0 : ∀ l, N l 0 = 0) (hNs : ∀ l, ContDiff ℝ r (N l))
    (hNj : ∀ b, JetRepG R r (fun l y => N l y b))
    (hΨs : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (Ψ l)) (hΨj : ∀ b, JetRepG R (r + K) (fun l y => Ψ l y b))
    (hMj : ∀ c k, JetRepG R r (fun l p => M l p c k))
    (hMs : ∀ c k l, ContDiff ℝ r (fun p => M l p c k))
    (hA : ∀ k, ArrJetG R r (fun l => A l k)) (c : Fin 2) :
    ArrJetG R r (fun l => chartArr (M l) (N l) (Ψ l) K (A l) c) := by
  intro m' γ
  -- the entry of the input array and of the Faà di Bruno array, composed with `N`
  have hAc : ∀ k m (α : DerivativeWord2 m),
      JetRepG R r (fun l y => A l k m α (N l y) 0) := fun k m α =>
    JetRepG.comp hR hN0 (fun l => (hA k m α).2 l) hNs (hA k m α).1 hNj
  have hAs : ∀ k m (α : DerivativeWord2 m) l, ContDiff ℝ r (fun y => A l k m α (N l y) 0) :=
    fun k m α l => ((hA k m α).2 l).comp (hNs l)
  have hFc : ∀ m ∈ Finset.range (K + 1), ∀ (α : DerivativeWord2 m),
      JetRepG R r (fun l y => fdbArr (Ψ l) α m' γ (N l y) 0) := by
    intro m hm α
    have hmK : m ≤ K := by simpa [Nat.lt_succ_iff] using hm
    have hF := arrJetG_fdbArr hR (r := r) (n := m) hΨs (fun b => (hΨj b).mono (by omega)) α m' γ
    exact JetRepG.comp hR hN0 (fun l => hF.2 l) hNs hF.1 hNj
  have hFs : ∀ m (α : DerivativeWord2 m) l,
      ContDiff ℝ r (fun y => fdbArr (Ψ l) α m' γ (N l y) 0) := by
    intro m α l
    have := arrSlowSmooth_fdbArr (hΨs l) r α m' γ 0
    exact this.comp (hNs l)
  have hterm : ∀ k, ∀ m ∈ Finset.range (K + 1), ∀ α : DerivativeWord2 m,
      JetRepG R r (fun l y => A l k m α (N l y) 0 * fdbArr (Ψ l) α m' γ (N l y) 0) :=
    fun k m hm α => JetRepG.mul hR (hAs k m α) (hFs m α) (hAc k m α) (hFc m hm α)
  have hts : ∀ k m (α : DerivativeWord2 m) l,
      ContDiff ℝ r (fun y => A l k m α (N l y) 0 * fdbArr (Ψ l) α m' γ (N l y) 0) :=
    fun k m α l => (hAs k m α l).mul (hFs m α l)
  have hinner : ∀ k, JetRepG R r (fun l y => ∑ m ∈ Finset.range (K + 1), ∑ α : DerivativeWord2 m,
      A l k m α (N l y) 0 * fdbArr (Ψ l) α m' γ (N l y) 0) := fun k =>
    JetRepG.finsetSum hR _ (fun m _ l => ContDiff.sum fun α _ => hts k m α l) fun m hm =>
      JetRepG.finsetSum hR _ (fun α _ l => hts k m α l) fun α _ => hterm k m hm α
  have hins : ∀ k l, ContDiff ℝ r (fun y => ∑ m ∈ Finset.range (K + 1), ∑ α : DerivativeWord2 m,
      A l k m α (N l y) 0 * fdbArr (Ψ l) α m' γ (N l y) 0) := fun k l =>
    ContDiff.sum fun m _ => ContDiff.sum fun α _ => hts k m α l
  refine ⟨?_, fun l => ?_⟩
  · refine (JetRepG.finsetSum hR (r := r) Finset.univ
      (F := fun k l y => M l y c k * ∑ m ∈ Finset.range (K + 1), ∑ α : DerivativeWord2 m,
        A l k m α (N l y) 0 * fdbArr (Ψ l) α m' γ (N l y) 0)
      (fun k _ l => (hMs c k l).mul (hins k l)) fun k _ =>
        JetRepG.mul hR (hMs c k) (hins k) (hMj c k) (hinner k)).congr_germ fun l =>
      Filter.Eventually.of_forall fun y => rfl
  · show ContDiff ℝ r (fun y => ∑ k : Fin 2, M l y c k * ∑ m ∈ Finset.range (K + 1),
      ∑ α : DerivativeWord2 m, A l k m α (N l y) 0 * fdbArr (Ψ l) α m' γ (N l y) 0)
    exact ContDiff.sum fun k _ => (hMs c k l).mul (hins k l)
end

/-! **Jets of the pushed and pulled arrays (generic).** The push `pushFlux Ψ Ψinv` has the
matrix `DΨ ∘ Ψinv` (represented by the chain rule from the jets of the components of `Ψ`); for the
pull the entries of `(DΦ)⁻¹` are hypotheses (they are covariant letters in the family instance). -/

section
variable {Λ : Type*} {R : (Λ → ℝ) → Prop}

/-- **Jets of the pushed array.** `Ψ` has jets of order `r + K + 1`, `Ψinv` of order `r`. -/
theorem arrJetG_push (hR : RepAlg R) {r K : ℕ} {Ψ Ψinv : Λ → Vec 2 → Vec 2} {A : Λ → Fin 2 → CArr}
    (hΨs : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (Ψ l)) (hΨj : ∀ b, JetRepG R (r + K + 1) (fun l y => Ψ l y b))
    (hIs : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (Ψinv l)) (hI0 : ∀ l, Ψinv l 0 = 0)
    (hIj : ∀ b, JetRepG R r (fun l y => Ψinv l y b))
    (hA : ∀ k, ArrJetG R r (fun l => A l k)) (c : Fin 2) :
    ArrJetG R r (fun l => chartArr (fun p => jacMatrix (Ψ l) (Ψinv l p)) (Ψinv l) (Ψ l) K (A l) c) := by
  have hIs' : ∀ l, ContDiff ℝ r (Ψinv l) := fun l =>
    (hIs l).of_le (by exact_mod_cast le_top)
  have hJe : ∀ c k, JetRepG R r (fun l w => jacMatrix (Ψ l) w c k) := fun c k =>
    jetRepG_fderiv_entry hΨs (fun b => (hΨj b).mono (by omega)) k c
  have hJs : ∀ c k l, ContDiff ℝ r (fun w => jacMatrix (Ψ l) w c k) := fun c k l =>
    contDiff_fderiv_entry (hΨs l) r k c
  exact arrJetG_chartArr hR hI0 hIs' hIj hΨs (fun b => (hΨj b).mono (by omega))
    (fun c k => JetRepG.comp hR hI0 (hJs c k) hIs' (hJe c k) hIj)
    (fun c k l => (hJs c k l).comp (hIs' l)) hA c

/-- **Jets of the pulled array.** `Φinv` has jets of order `r + K`; the entries of `(DΦ)⁻¹` are
represented and smooth (hypotheses). -/
theorem arrJetG_pull (hR : RepAlg R) {r K : ℕ} {Φ Φinv : Λ → Vec 2 → Vec 2} {B : Λ → Fin 2 → CArr}
    (hΦ0 : ∀ l, Φ l 0 = 0) (hΦs : ∀ l, ContDiff ℝ r (Φ l))
    (hΦj : ∀ b, JetRepG R r (fun l y => Φ l y b))
    (hIs : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (Φinv l)) (hIj : ∀ b, JetRepG R (r + K) (fun l y => Φinv l y b))
    (hMj : ∀ c k, JetRepG R r (fun l p => ((jacMatrix (Φ l) p)⁻¹) c k))
    (hMs : ∀ c k l, ContDiff ℝ r (fun p => ((jacMatrix (Φ l) p)⁻¹) c k))
    (hB : ∀ k, ArrJetG R r (fun l => B l k)) (c : Fin 2) :
    ArrJetG R r (fun l => chartArr (fun p => (jacMatrix (Φ l) p)⁻¹) (Φ l) (Φinv l) K (B l) c) :=
  arrJetG_chartArr hR hΦ0 hΦs hΦj hIs hIj hMj hMs hB c
end

/-! **Push and pull of array operators by the chart pair `(famMap t, famMapInv t)`.**
The family instance (`Λ = W`, `R = famAlg …`). Hypotheses: `IsFastProfile D.ζ`, every chain of
the window `W` well slotted. The pushed/pulled arrays are the explicit `chartArr` (entries: sums of
products of the input entries composed with `famMapInv` / `famMap`, Jacobian entries
`jacMatrix (famMap t) (famMapInv t x)` / inverse Jacobians, and `fdbArr` entries) and all entries
have represented jets at `0`. -/

section
variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {i : ℕ} {p : ℤ}
  {W : Set (ℝ × RealChain)}

theorem famMap_famMapInv (hζ : IsFastProfile D.ζ) (A : RealChain) (t : ℝ) (x : Vec 2) :
    A.famMap D t (A.famMapInv D t x) = x := by
  have hg := isFlowGeom_geom D hζ A
  simp only [RealChain.famMap, RealChain.famMapInv, add_sub_cancel]
  rw [hg.inv]
  abel

theorem famMapInv_famMap (hζ : IsFastProfile D.ζ) (A : RealChain) (t : ℝ) (y : Vec 2) :
    A.famMapInv D t (A.famMap D t y) = y := by
  have hg := isFlowGeom_geom D hζ A
  simp only [RealChain.famMap, RealChain.famMapInv, add_sub_cancel]
  rw [hg.inv]
  abel

/-- The Jacobian matrix of the centered map is the Jacobian of the recentered family. -/
theorem jacMatrix_famMap (hζ : IsFastProfile D.ζ) (A : RealChain) (hA : A.WellSlotted) (t : ℝ)
    (w : Vec 2) : jacMatrix (A.famMap D t) w = (A.recenter D w).famJac D t := by
  ext a b
  simp only [jacMatrix, Matrix.of_apply]
  rw [← fderiv_component ((contDiff_famMap A t).differentiable (by simp) w) a b,
    dLabel_famMap hζ A hA t a b w]

/-- **Jets of the pushed array** by `(famMap t, famMapInv t)`. -/
theorem arrJetG_push_famMap (hζ : IsFastProfile D.ζ) (hW : ∀ q ∈ W, q.2.WellSlotted) {r K : ℕ}
    {A : W → Fin 2 → CArr}
    (hA : ∀ k, ArrJetG (famAlg D bw j₀ 𝒮 i p W) r (fun q => A q k)) (c : Fin 2) :
    ArrJetG (famAlg D bw j₀ 𝒮 i p W) r (fun q : W =>
      chartArr (fun x => jacMatrix (q.1.2.famMap D q.1.1) (q.1.2.famMapInv D q.1.1 x))
        (q.1.2.famMapInv D q.1.1) (q.1.2.famMap D q.1.1) K (A q) c) :=
  arrJetG_push (repAlg_famAlg D bw j₀ 𝒮 i p W) (fun q => contDiff_famMap q.1.2 q.1.1)
    (fun b => jetRep_toG (jetRep_famMap hζ hW (r + K + 1) b))
    (fun q => contDiff_famMapInv q.1.2 q.1.1) (fun q => famMapInv_zero hζ q.1.2 q.1.1)
    (fun b => jetRep_toG (jetRep_famMapInv hζ hW r b)) hA c

/-- **Jets of the pulled array** by `(famMap t, famMapInv t)`. -/
theorem arrJetG_pull_famMap (hζ : IsFastProfile D.ζ) (hW : ∀ q ∈ W, q.2.WellSlotted) {r K : ℕ}
    {B : W → Fin 2 → CArr}
    (hB : ∀ k, ArrJetG (famAlg D bw j₀ 𝒮 i p W) r (fun q => B q k)) (c : Fin 2) :
    ArrJetG (famAlg D bw j₀ 𝒮 i p W) r (fun q : W =>
      chartArr (fun x => (jacMatrix (q.1.2.famMap D q.1.1) x)⁻¹)
        (q.1.2.famMap D q.1.1) (q.1.2.famMapInv D q.1.1) K (B q) c) := by
  have hG : ∀ b j : Fin 2, ∀ r, JetRep D bw j₀ 𝒮 i p W r
      (fun t A w => ((A.recenter D w).famJac D t)⁻¹ b j) := by
    intro b j r
    obtain ⟨hs, hf, f, hd, hv⟩ := famLetter_rep (D := D) (bw := bw) (j₀ := j₀) (𝒮 := 𝒮)
      (i := i) (p := p) (.jacInv b j)
    exact jetRep_covariant hζ r hs hf hd fun q _ w => by rw [hv]; rfl
  have e : ∀ (q : W) (x : Vec 2) (c k : Fin 2),
      (jacMatrix (q.1.2.famMap D q.1.1) x)⁻¹ c k = ((q.1.2.recenter D x).famJac D q.1.1)⁻¹ c k :=
    fun q x c k => by rw [jacMatrix_famMap hζ q.1.2 (hW q.1 q.2) q.1.1 x]
  refine arrJetG_pull (repAlg_famAlg D bw j₀ 𝒮 i p W) (fun q => famMap_zero q.1.2 q.1.1)
    (fun q => (contDiff_famMap q.1.2 q.1.1).of_le (by exact_mod_cast le_top))
    (fun b => jetRep_toG (jetRep_famMap hζ hW r b)) (fun q => contDiff_famMapInv q.1.2 q.1.1)
    (fun b => jetRep_toG (jetRep_famMapInv hζ hW (r + K) b)) (fun c k => ?_) (fun c k q => ?_) hB c
  · simp_rw [e]
    exact jetRep_toG (hG c k r)
  · simp_rw [e]
    exact (contDiff_famJacInv hζ q.1.2 (hW q.1 q.2) q.1.1 c k).of_le (by exact_mod_cast le_top)

/-- **Push by the chart pair** as an array operator (value level). -/
theorem pushFlux_famMap_applyArr (hζ : IsFastProfile D.ζ) (A : RealChain) (t : ℝ) (K : ℕ)
    (B : Fin 2 → CArr) {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2) (c : Fin 2) :
    pushFlux (A.famMap D t) (A.famMapInv D t) (fun g y k => applyArr K (B k) g y 0) f x c =
      applyArr K (chartArr (fun y => jacMatrix (A.famMap D t) (A.famMapInv D t y))
        (A.famMapInv D t) (A.famMap D t) K B c) f x 0 :=
  pushFlux_applyArr (contDiff_famMap A t) (famMap_famMapInv hζ A t) K B hf x c

/-- **Pull by the chart pair** as an array operator (value level). -/
theorem pullFlux_famMap_applyArr (hζ : IsFastProfile D.ζ) (A : RealChain) (t : ℝ) (K : ℕ)
    (B : Fin 2 → CArr) {u : Vec 2 → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (y : Vec 2) (c : Fin 2) :
    pullFlux (A.famMap D t) (A.famMapInv D t) (fun g x k => applyArr K (B k) g x 0) u y c =
      applyArr K (chartArr (fun x => (jacMatrix (A.famMap D t) x)⁻¹)
        (A.famMap D t) (A.famMapInv D t) K B c) u y 0 :=
  pullFlux_applyArr (contDiff_famMapInv A t) (famMapInv_famMap hζ A t) K B hu y c
end

end AVRegularity.Providers.GenSem
end
