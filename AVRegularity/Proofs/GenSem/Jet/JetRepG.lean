-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.GenSem.BoxJoint

@[expose] public noncomputable section

section
open Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.GenSem

/-! **Represented family functions and covariant jets.** `FamRepOn W G`: the family function
`G (t, 𝒜)` agrees on `W` with the denotation of a scheduled, seed-provenanced family expression.
Closure under constants, sums, products and finite sums. A label function that is *covariant*
(its value at the label `w` is a family function at the recentered family `𝒜^{[w]}`) has all its
ordered derivatives at every label represented, by iterated slow family derivatives (K3)(b), with no
regularity assumption (recenterings compose, `fderiv_comp_add_left`). -/

variable (D : OCData) (bw : ℝ) (j₀ : ℕ) (𝒮 : SeedExports) {i : ℕ} {p : ℤ}

/-- The family function `G` is represented on `W` by a family expression. -/
def FamRepOn (W : Set (ℝ × RealChain)) (G : ℝ → RealChain → ℝ) (c : Gen .fam i p) : Prop :=
  Gen.IsScheduled D c ∧ Gen.FromSeed 𝒮 c ∧ ∃ fc : GenSort.Sem .fam, Gen.Denotes D bw j₀ c fc ∧
    ∀ q ∈ W, G q.1 q.2 = fc q.1 q.2

variable {D bw j₀ 𝒮} {W : Set (ℝ × RealChain)}

namespace FamRepOn

theorem congr {G H : ℝ → RealChain → ℝ} {c : Gen .fam i p} (h : FamRepOn D bw j₀ 𝒮 W G c)
    (hGH : ∀ q ∈ W, H q.1 q.2 = G q.1 q.2) : FamRepOn D bw j₀ 𝒮 W H c := by
  obtain ⟨hs, hf, fc, hd, hv⟩ := h
  exact ⟨hs, hf, fc, hd, fun q hq => (hGH q hq).trans (hv q hq)⟩

theorem const (c : ℝ) :
    FamRepOn D bw j₀ 𝒮 W (fun _ _ => c) (Gen.time (s := .fam) (i := i) (p := p) (.const c)) :=
  ⟨.timeConst c, .time _, _, .time _, fun _ _ => rfl⟩

theorem add {G H : ℝ → RealChain → ℝ} {a b : Gen .fam i p} (ha : FamRepOn D bw j₀ 𝒮 W G a)
    (hb : FamRepOn D bw j₀ 𝒮 W H b) :
    FamRepOn D bw j₀ 𝒮 W (fun t A => G t A + H t A) (Gen.add a b) := by
  obtain ⟨sa, fa, f, hf, hG⟩ := ha
  obtain ⟨sb, fb, g, hg, hH⟩ := hb
  exact ⟨.add sa sb, .add fa fb, GenSort.add .fam f g, .add hf hg, fun q hq => by
    show G q.1 q.2 + H q.1 q.2 = f q.1 q.2 + g q.1 q.2
    rw [hG q hq, hH q hq]⟩

theorem mul {G H : ℝ → RealChain → ℝ} {a b : Gen .fam i p} (ha : FamRepOn D bw j₀ 𝒮 W G a)
    (hb : FamRepOn D bw j₀ 𝒮 W H b) :
    FamRepOn D bw j₀ 𝒮 W (fun t A => G t A * H t A) (Gen.mul a b) := by
  obtain ⟨sa, fa, f, hf, hG⟩ := ha
  obtain ⟨sb, fb, g, hg, hH⟩ := hb
  exact ⟨.mul sa sb, .mul fa fb, GenSort.mul .fam f g, .mul hf hg, fun q hq => by
    show G q.1 q.2 * H q.1 q.2 = f q.1 q.2 * g q.1 q.2
    rw [hG q hq, hH q hq]⟩

end FamRepOn

/-- `G` is represented on `W` by some family expression. -/
def IsFamRepOn (D : OCData) (bw : ℝ) (j₀ : ℕ) (𝒮 : SeedExports) (i : ℕ) (p : ℤ)
    (W : Set (ℝ × RealChain)) (G : ℝ → RealChain → ℝ) : Prop :=
  ∃ c : Gen .fam i p, FamRepOn D bw j₀ 𝒮 W G c

namespace IsFamRepOn

theorem congr {G H : ℝ → RealChain → ℝ} (h : IsFamRepOn D bw j₀ 𝒮 i p W G)
    (hGH : ∀ q ∈ W, H q.1 q.2 = G q.1 q.2) : IsFamRepOn D bw j₀ 𝒮 i p W H := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc.congr hGH⟩

theorem const (c : ℝ) : IsFamRepOn D bw j₀ 𝒮 i p W (fun _ _ => c) := ⟨_, FamRepOn.const c⟩

theorem add {G H : ℝ → RealChain → ℝ} (ha : IsFamRepOn D bw j₀ 𝒮 i p W G)
    (hb : IsFamRepOn D bw j₀ 𝒮 i p W H) : IsFamRepOn D bw j₀ 𝒮 i p W (fun t A => G t A + H t A) := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  exact ⟨_, ha.add hb⟩

theorem mul {G H : ℝ → RealChain → ℝ} (ha : IsFamRepOn D bw j₀ 𝒮 i p W G)
    (hb : IsFamRepOn D bw j₀ 𝒮 i p W H) : IsFamRepOn D bw j₀ 𝒮 i p W (fun t A => G t A * H t A) := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  exact ⟨_, ha.mul hb⟩

theorem smul {G : ℝ → RealChain → ℝ} (h : IsFamRepOn D bw j₀ 𝒮 i p W G) (c : ℝ) :
    IsFamRepOn D bw j₀ 𝒮 i p W (fun t A => c * G t A) :=
  (const c).mul h

theorem neg {G : ℝ → RealChain → ℝ} (h : IsFamRepOn D bw j₀ 𝒮 i p W G) :
    IsFamRepOn D bw j₀ 𝒮 i p W (fun t A => -G t A) :=
  (h.smul (-1)).congr fun _ _ => by ring

theorem sub {G H : ℝ → RealChain → ℝ} (ha : IsFamRepOn D bw j₀ 𝒮 i p W G)
    (hb : IsFamRepOn D bw j₀ 𝒮 i p W H) : IsFamRepOn D bw j₀ 𝒮 i p W (fun t A => G t A - H t A) :=
  (ha.add hb.neg).congr fun _ _ => by ring

theorem finsetSum {κ : Type*} (s : Finset κ) {G : κ → ℝ → RealChain → ℝ}
    (h : ∀ k ∈ s, IsFamRepOn D bw j₀ 𝒮 i p W (G k)) :
    IsFamRepOn D bw j₀ 𝒮 i p W (fun t A => ∑ k ∈ s, G k t A) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (const 0).congr fun _ _ => by simp
  | insert a s ha ih =>
    exact ((h a (Finset.mem_insert_self a s)).add
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))).congr fun _ _ => by
        rw [Finset.sum_insert ha]

end IsFamRepOn

end AVRegularity.Providers.GenSem
end

section
open Homogenization AVRegularity AVRegularity.Sobolev Filter Topology
namespace AVRegularity.Providers.GenSem

/-! **Represented jets of label functions.** `JetRep r g`: the value at the label `0` of the
family of label functions `g (t, 𝒜) : Vec 2 → ℝ`, and recursively the jets of order `r - 1` of
its first derivatives, are represented on `W`. Hence every ordered derivative of order `≤ r` at `0`
is represented (`JetRep.orderedDerivative`). Covariant functions have represented jets of every
order (`jetRep_covariant`). Closure: constants, sums, products (Leibniz), germs at `0`, and the
chain rule `g ∘ Ψ` for label maps with `Ψ 0 = 0` (`JetRep.comp`), under differentiability. -/

section
variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {i : ℕ} {p : ℤ}
  {W : Set (ℝ × RealChain)}

/-- The first derivative of a family of label functions in the direction `j`. -/
def dLabel (j : Fin 2) (g : ℝ → RealChain → Vec 2 → ℝ) : ℝ → RealChain → Vec 2 → ℝ :=
  fun t A y => fderiv ℝ (g t A) y (basisVec j)

variable (D bw j₀ 𝒮 i p W) in
/-- Represented jets of order `r` at the label `0`. -/
def JetRep : ℕ → (ℝ → RealChain → Vec 2 → ℝ) → Prop
  | 0, g => IsFamRepOn D bw j₀ 𝒮 i p W (fun t A => g t A 0)
  | r + 1, g => IsFamRepOn D bw j₀ 𝒮 i p W (fun t A => g t A 0) ∧ ∀ j, JetRep r (dLabel j g)

theorem JetRep.value {r : ℕ} {g : ℝ → RealChain → Vec 2 → ℝ}
    (h : JetRep D bw j₀ 𝒮 i p W r g) : IsFamRepOn D bw j₀ 𝒮 i p W (fun t A => g t A 0) := by
  cases r with
  | zero => exact h
  | succ r => exact h.1

theorem JetRep.mono : ∀ {r r' : ℕ}, r' ≤ r → ∀ {g : ℝ → RealChain → Vec 2 → ℝ},
    JetRep D bw j₀ 𝒮 i p W r g → JetRep D bw j₀ 𝒮 i p W r' g
  | _, 0, _, _, h => h.value
  | 0, _ + 1, hr, _, _ => absurd hr (by omega)
  | _ + 1, _ + 1, hr, _, h => ⟨h.1, fun j => JetRep.mono (by omega) (h.2 j)⟩

/-- Jets depend only on the germs at `0`. -/
theorem JetRep.congr_germ : ∀ {r : ℕ} {g h : ℝ → RealChain → Vec 2 → ℝ},
    JetRep D bw j₀ 𝒮 i p W r g → (∀ q ∈ W, g q.1 q.2 =ᶠ[𝓝 0] h q.1 q.2) →
      JetRep D bw j₀ 𝒮 i p W r h
  | 0, _, _, hg, he => hg.congr fun q hq => ((he q hq).eq_of_nhds).symm
  | _ + 1, g, h, hg, he => ⟨hg.1.congr fun q hq => ((he q hq).eq_of_nhds).symm, fun j =>
      JetRep.congr_germ (hg.2 j) fun q hq => by
        have := (he q hq).fderiv (𝕜 := ℝ)
        filter_upwards [this] with y hy
        simp only [dLabel, hy]⟩

/-- Every ordered derivative of order `≤ r` at `0` is represented. -/
theorem JetRep.orderedDerivative : ∀ {r : ℕ} {g : ℝ → RealChain → Vec 2 → ℝ},
    JetRep D bw j₀ 𝒮 i p W r g → ∀ {m : ℕ}, m ≤ r → ∀ α : DerivativeWord2 m,
      IsFamRepOn D bw j₀ 𝒮 i p W (fun t A => AVRegularity.orderedDerivative α (g t A) 0)
  | _, _, h, 0, _, α => by
      have : α = Fin.elim0 := Subsingleton.elim _ _
      subst this
      exact h.value.congr fun q _ => by simp [AVRegularity.orderedDerivative]
  | 0, _, _, _ + 1, hm, _ => absurd hm (by omega)
  | _ + 1, g, h, m + 1, hm, α => by
      have := JetRep.orderedDerivative (h.2 (α 0)) (m := m) (by omega) (fun i => α i.succ)
      exact this.congr fun q _ => by rw [orderedDerivative_succ]; rfl

/-- **Covariant label functions have represented jets of every order.** -/
theorem jetRep_covariant (hζ : IsFastProfile D.ζ) : ∀ (r : ℕ) {g : ℝ → RealChain → Vec 2 → ℝ}
    {c : Gen .fam i p} {fc : GenSort.Sem .fam}, Gen.IsScheduled D c → Gen.FromSeed 𝒮 c →
      Gen.Denotes D bw j₀ c fc → (∀ q ∈ W, ∀ w, g q.1 q.2 w = fc q.1 (q.2.recenter D w)) →
      JetRep D bw j₀ 𝒮 i p W r g
  | 0, g, c, fc, hs, hf, hd, hg => ⟨c, hs, hf, fc, hd, fun q hq => by
      show g q.1 q.2 0 = fc q.1 q.2
      rw [hg q hq, recenter_zero D hζ]⟩
  | r + 1, g, c, fc, hs, hf, hd, hg => by
      refine ⟨⟨c, hs, hf, fc, hd, fun q hq => by
        show g q.1 q.2 0 = fc q.1 q.2
        rw [hg q hq, recenter_zero D hζ]⟩, fun j => ?_⟩
      refine jetRep_covariant hζ r (c := Gen.dSlowFam j c) (.dSlowFam j hs) (.dSlowFam j hf)
        (.dSlowFam j hd) fun q hq w => ?_
      obtain ⟨t, A⟩ := q
      have e : g t A = fun w' => fc t (A.recenter D w') := funext (hg (t, A) hq)
      simp only [dLabel, e]
      have e2 : (fun h => fc t ((A.recenter D w).recenter D h)) =
          fun h => (fun w' => fc t (A.recenter D w')) (w + h) := by
        funext h; rw [recenter_recenter D hζ]
      show fderiv ℝ (fun w' => fc t (A.recenter D w')) w (basisVec j) =
        fderiv ℝ (fun h => fc t ((A.recenter D w).recenter D h)) 0 (basisVec j)
      rw [e2]
      set F : Vec 2 → ℝ := fun w' => fc t (A.recenter D w')
      show fderiv ℝ F w _ = fderiv ℝ (fun h => F (w + h)) 0 _
      rw [fderiv_comp_add_left, add_zero]

/-- Sums, for families differentiable near `0`. -/
theorem JetRep.add : ∀ {r : ℕ} {g h : ℝ → RealChain → Vec 2 → ℝ},
    (∀ q ∈ W, ContDiff ℝ r (g q.1 q.2)) → (∀ q ∈ W, ContDiff ℝ r (h q.1 q.2)) →
    JetRep D bw j₀ 𝒮 i p W r g → JetRep D bw j₀ 𝒮 i p W r h →
      JetRep D bw j₀ 𝒮 i p W r (fun t A y => g t A y + h t A y)
  | 0, _, _, _, _, hg, hh => IsFamRepOn.add hg hh
  | r + 1, g, h, cg, ch, hg, hh => ⟨IsFamRepOn.add hg.1 hh.1, fun j => by
      refine (JetRep.add (r := r) (g := dLabel j g) (h := dLabel j h) (fun q hq => ?_)
        (fun q hq => ?_) (hg.2 j) (hh.2 j)).congr_germ fun q hq =>
          Filter.Eventually.of_forall fun y => ?_
      · exact ((cg q hq).fderiv_right (m := r) (by norm_cast)).clm_apply contDiff_const
      · exact ((ch q hq).fderiv_right (m := r) (by norm_cast)).clm_apply contDiff_const
      · simp only [dLabel]
        rw [fderiv_fun_add ((cg q hq).differentiable (by norm_cast) y)
          ((ch q hq).differentiable (by norm_cast) y)]
        rfl⟩

theorem contDiff_dLabel {r : ℕ} {g : Vec 2 → ℝ} (hg : ContDiff ℝ (r + 1 : ℕ) g) (j : Fin 2) :
    ContDiff ℝ r (fun y => fderiv ℝ g y (basisVec j)) :=
  (hg.fderiv_right (m := r) (by norm_cast)).clm_apply contDiff_const

/-- Products (Leibniz), for families of class `C^r`. -/
theorem JetRep.mul : ∀ {r : ℕ} {g h : ℝ → RealChain → Vec 2 → ℝ},
    (∀ q ∈ W, ContDiff ℝ r (g q.1 q.2)) → (∀ q ∈ W, ContDiff ℝ r (h q.1 q.2)) →
    JetRep D bw j₀ 𝒮 i p W r g → JetRep D bw j₀ 𝒮 i p W r h →
      JetRep D bw j₀ 𝒮 i p W r (fun t A y => g t A y * h t A y)
  | 0, _, _, _, _, hg, hh => IsFamRepOn.mul hg hh
  | r + 1, g, h, cg, ch, hg, hh => ⟨IsFamRepOn.mul hg.1 hh.1, fun j => by
      have cg' : ∀ q ∈ W, ContDiff ℝ r (g q.1 q.2) := fun q hq => (cg q hq).of_le (by norm_cast; omega)
      have ch' : ∀ q ∈ W, ContDiff ℝ r (h q.1 q.2) := fun q hq => (ch q hq).of_le (by norm_cast; omega)
      have cdg : ∀ q ∈ W, ContDiff ℝ r (dLabel j g q.1 q.2) := fun q hq => contDiff_dLabel (cg q hq) j
      have cdh : ∀ q ∈ W, ContDiff ℝ r (dLabel j h q.1 q.2) := fun q hq => contDiff_dLabel (ch q hq) j
      have h1 := JetRep.mul cdg ch' (hg.2 j) (hh.mono (by omega))
      have h2 := JetRep.mul cg' cdh (hg.mono (by omega)) (hh.2 j)
      refine (JetRep.add (fun q hq => (cdg q hq).mul (ch' q hq)) (fun q hq => (cg' q hq).mul
        (cdh q hq)) h1 h2).congr_germ fun q hq => Filter.Eventually.of_forall fun y => ?_
      simp only [dLabel]
      rw [fderiv_fun_mul ((cg q hq).differentiable (by norm_cast) y)
        ((ch q hq).differentiable (by norm_cast) y)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring⟩

/-- The derivative of a component of a differentiable label map. -/
theorem fderiv_component {Ψ : Vec 2 → Vec 2} {y : Vec 2} (hΨ : DifferentiableAt ℝ Ψ y)
    (b j : Fin 2) : fderiv ℝ (fun y' => Ψ y' b) y (basisVec j) = fderiv ℝ Ψ y (basisVec j) b := by
  have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) b).hasFDerivAt).comp y
    hΨ.hasFDerivAt
  have e : (fun y' => Ψ y' b) =
      ⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) b) ∘ Ψ := rfl
  rw [e, h.fderiv]
  rfl

/-- The chain rule in one direction. -/
theorem fderiv_comp_label {g : Vec 2 → ℝ} {Ψ : Vec 2 → Vec 2} {y : Vec 2}
    (hg : DifferentiableAt ℝ g (Ψ y)) (hΨ : DifferentiableAt ℝ Ψ y) (j : Fin 2) :
    fderiv ℝ (fun y' => g (Ψ y')) y (basisVec j) =
      ∑ b : Fin 2, fderiv ℝ g (Ψ y) (basisVec b) * fderiv ℝ (fun y' => Ψ y' b) y (basisVec j) := by
  rw [show (fun y' => g (Ψ y')) = g ∘ Ψ from rfl, fderiv_comp y hg hΨ]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  conv_lhs => rw [show fderiv ℝ Ψ y (basisVec j) = ∑ b : Fin 2, (fderiv ℝ Ψ y (basisVec j) b) •
    basisVec b by
      funext a
      simp [Finset.sum_apply, basisVec, Pi.single_apply]]
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm, fderiv_component hΨ b j]

/-- **The chain rule for jets**: `g ∘ Ψ` for label maps with `Ψ 0 = 0`. -/
theorem JetRep.comp : ∀ {r : ℕ} {g : ℝ → RealChain → Vec 2 → ℝ}
    {Ψ : ℝ → RealChain → Vec 2 → Vec 2},
    (∀ q ∈ W, Ψ q.1 q.2 0 = 0) → (∀ q ∈ W, ContDiff ℝ r (g q.1 q.2)) →
    (∀ q ∈ W, ContDiff ℝ r (Ψ q.1 q.2)) → JetRep D bw j₀ 𝒮 i p W r g →
    (∀ b, JetRep D bw j₀ 𝒮 i p W r (fun t A y => Ψ t A y b)) →
      JetRep D bw j₀ 𝒮 i p W r (fun t A y => g t A (Ψ t A y))
  | 0, g, Ψ, h0, _, _, hg, _ => IsFamRepOn.congr hg fun q hq => by
      show g q.1 q.2 (Ψ q.1 q.2 0) = g q.1 q.2 0
      rw [h0 q hq]
  | r + 1, g, Ψ, h0, cg, cΨ, hg, hΨ => ⟨IsFamRepOn.congr hg.1 fun q hq => by
      show g q.1 q.2 (Ψ q.1 q.2 0) = g q.1 q.2 0
      rw [h0 q hq], fun j => by
      have cΨ' : ∀ q ∈ W, ContDiff ℝ r (Ψ q.1 q.2) := fun q hq => (cΨ q hq).of_le (by norm_cast; omega)
      have cΨb : ∀ b, ∀ q ∈ W, ContDiff ℝ (r + 1 : ℕ) (fun y => Ψ q.1 q.2 y b) := fun b q hq =>
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) b).contDiff.comp (cΨ q hq)
      have hterm : ∀ b, JetRep D bw j₀ 𝒮 i p W r
          (fun t A y => dLabel b g t A (Ψ t A y) * dLabel j (fun t A y => Ψ t A y b) t A y) := by
        intro b
        have h1 := JetRep.comp h0 (fun q hq => contDiff_dLabel (cg q hq) b) cΨ' (hg.2 b)
          (fun b' => (hΨ b').mono (by omega))
        refine JetRep.mul (fun q hq => (contDiff_dLabel (cg q hq) b).comp (cΨ' q hq))
          (fun q hq => contDiff_dLabel (cΨb b q hq) j) h1 ((hΨ b).2 j)
      have hsum := JetRep.add (fun q hq => ((contDiff_dLabel (cg q hq) 0).comp (cΨ' q hq)).mul
          (contDiff_dLabel (cΨb 0 q hq) j))
        (fun q hq => ((contDiff_dLabel (cg q hq) 1).comp (cΨ' q hq)).mul
          (contDiff_dLabel (cΨb 1 q hq) j)) (hterm 0) (hterm 1)
      refine hsum.congr_germ fun q hq => Filter.Eventually.of_forall fun y => ?_
      simp only [dLabel]
      rw [fderiv_comp_label ((cg q hq).differentiable (by norm_cast) _)
        ((cΨ q hq).differentiable (by norm_cast) y) j, Fin.sum_univ_two]⟩

/-- **Covariant jets on an open neighbourhood.** If `g w = fc t (𝒜^{[w]})` for the labels `w` of an
open set containing `0`, the jets of every order at `0` are represented. -/
theorem jetRep_covariant_on (hζ : IsFastProfile D.ζ) : ∀ (r : ℕ) {g : ℝ → RealChain → Vec 2 → ℝ}
    {c : Gen .fam i p} {fc : GenSort.Sem .fam} {U : ℝ → RealChain → Set (Vec 2)},
      (∀ q ∈ W, IsOpen (U q.1 q.2)) → (∀ q ∈ W, (0 : Vec 2) ∈ U q.1 q.2) →
      Gen.IsScheduled D c → Gen.FromSeed 𝒮 c → Gen.Denotes D bw j₀ c fc →
      (∀ q ∈ W, ∀ w ∈ U q.1 q.2, g q.1 q.2 w = fc q.1 (q.2.recenter D w)) →
      JetRep D bw j₀ 𝒮 i p W r g := by
  intro r
  induction r with
  | zero =>
    intro g c fc U _ h0 hs hf hd hg
    exact ⟨c, hs, hf, fc, hd, fun q hq => by
      show g q.1 q.2 0 = fc q.1 q.2
      rw [hg q hq 0 (h0 q hq), recenter_zero D hζ]⟩
  | succ r ih =>
    intro g c fc U hU h0 hs hf hd hg
    refine ⟨⟨c, hs, hf, fc, hd, fun q hq => by
      show g q.1 q.2 0 = fc q.1 q.2
      rw [hg q hq 0 (h0 q hq), recenter_zero D hζ]⟩, fun j => ?_⟩
    refine ih (c := Gen.dSlowFam j c) (U := U) hU h0 (.dSlowFam j hs) (.dSlowFam j hf)
      (.dSlowFam j hd) fun q hq w hw => ?_
    obtain ⟨t, A⟩ := q
    have hev : g t A =ᶠ[nhds w] fun w' => fc t (A.recenter D w') := by
      filter_upwards [(hU (t, A) hq).mem_nhds hw] with w' hw'
      exact hg (t, A) hq w' hw'
    simp only [dLabel]
    rw [hev.fderiv_eq]
    have e2 : (fun h => fc t ((A.recenter D w).recenter D h)) =
        fun h => (fun w' => fc t (A.recenter D w')) (w + h) := by
      funext h; rw [recenter_recenter D hζ]
    show fderiv ℝ (fun w' => fc t (A.recenter D w')) w (basisVec j) =
      fderiv ℝ (fun h => fc t ((A.recenter D w).recenter D h)) 0 (basisVec j)
    rw [e2]
    set F : Vec 2 → ℝ := fun w' => fc t (A.recenter D w')
    show fderiv ℝ F w _ = fderiv ℝ (fun h => F (w + h)) 0 _
    rw [fderiv_comp_add_left, add_zero]
end

/-! **Represented jets over an abstract algebra of represented scalars (generic form).** For an
index type `Λ` and a predicate `R` on scalar functions of the index closed under constants, sums
and products (`RepAlg R`), `JetRepG R r g` says that the value at the label `0` of the label
functions `g λ`, and recursively the jets of order `r - 1` of their first derivatives, satisfy `R`.
Closure: germs, orders, ordered derivatives, constants, sums, products and the chain rule. The
family instance (`famAlg`, Λ = the window as a subtype) recovers `JetRep` (`jetRep_toG`); a
context instance is obtained in the same way from context expressions. -/

section
/-- An algebra of represented scalar functions of the index. -/
structure RepAlg {Λ : Type*} (R : (Λ → ℝ) → Prop) : Prop where
  const : ∀ c : ℝ, R (fun _ => c)
  add : ∀ {F G : Λ → ℝ}, R F → R G → R (fun l => F l + G l)
  mul : ∀ {F G : Λ → ℝ}, R F → R G → R (fun l => F l * G l)

namespace RepAlg

variable {Λ : Type*} {R : (Λ → ℝ) → Prop} (hR : RepAlg R)
include hR

theorem smul {F : Λ → ℝ} (h : R F) (c : ℝ) : R (fun l => c * F l) := hR.mul (hR.const c) h

theorem neg {F : Λ → ℝ} (h : R F) : R (fun l => -F l) := by
  have := hR.smul h (-1); simpa using this

theorem sub {F G : Λ → ℝ} (hF : R F) (hG : R G) : R (fun l => F l - G l) := by
  have := hR.add hF (hR.neg hG); simpa [sub_eq_add_neg] using this

theorem finsetSum {κ : Type*} (s : Finset κ) {F : κ → Λ → ℝ} (h : ∀ k ∈ s, R (F k)) :
    R (fun l => ∑ k ∈ s, F k l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hR.const 0
  | insert a s ha ih =>
    have := hR.add (h a (Finset.mem_insert_self a s)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))
    simpa [Finset.sum_insert ha] using this

end RepAlg

variable {Λ : Type*} {R : (Λ → ℝ) → Prop}

/-- The first derivative of a family of label functions. -/
def dLabelG (j : Fin 2) (g : Λ → Vec 2 → ℝ) : Λ → Vec 2 → ℝ :=
  fun l y => fderiv ℝ (g l) y (basisVec j)

variable (R) in
/-- Represented jets of order `r` at the label `0`. -/
def JetRepG : ℕ → (Λ → Vec 2 → ℝ) → Prop
  | 0, g => R (fun l => g l 0)
  | r + 1, g => R (fun l => g l 0) ∧ ∀ j, JetRepG r (dLabelG j g)

theorem JetRepG.value {r : ℕ} {g : Λ → Vec 2 → ℝ} (h : JetRepG R r g) : R (fun l => g l 0) := by
  cases r with
  | zero => exact h
  | succ r => exact h.1

theorem JetRepG.mono : ∀ {r r' : ℕ}, r' ≤ r → ∀ {g : Λ → Vec 2 → ℝ},
    JetRepG R r g → JetRepG R r' g
  | _, 0, _, _, h => h.value
  | 0, _ + 1, hr, _, _ => absurd hr (by omega)
  | _ + 1, _ + 1, hr, _, h => ⟨h.1, fun j => JetRepG.mono (by omega) (h.2 j)⟩

theorem JetRepG.congr_germ : ∀ {r : ℕ} {g h : Λ → Vec 2 → ℝ},
    JetRepG R r g → (∀ l, g l =ᶠ[𝓝 0] h l) → JetRepG R r h
  | 0, g, h, hg, he => by
      have e : (fun l => h l 0) = fun l => g l 0 := funext fun l => ((he l).eq_of_nhds).symm
      show R (fun l => h l 0); rw [e]; exact hg
  | _ + 1, g, h, hg, he => ⟨by
      have e : (fun l => h l 0) = fun l => g l 0 := funext fun l => ((he l).eq_of_nhds).symm
      rw [e]; exact hg.1, fun j =>
      JetRepG.congr_germ (hg.2 j) fun l => by
        have := (he l).fderiv (𝕜 := ℝ)
        filter_upwards [this] with y hy
        simp only [dLabelG, hy]⟩

theorem JetRepG.orderedDerivative : ∀ {r : ℕ} {g : Λ → Vec 2 → ℝ},
    JetRepG R r g → ∀ {m : ℕ}, m ≤ r → ∀ α : DerivativeWord2 m,
      R (fun l => AVRegularity.orderedDerivative α (g l) 0)
  | _, g, h, 0, _, α => by
      have : α = Fin.elim0 := Subsingleton.elim _ _
      subst this
      have e : (fun l => AVRegularity.orderedDerivative (Fin.elim0 : DerivativeWord2 0) (g l) 0) =
          fun l => g l 0 := funext fun l => by simp [AVRegularity.orderedDerivative]
      rw [e]; exact h.value
  | 0, _, _, _ + 1, hm, _ => absurd hm (by omega)
  | _ + 1, g, h, m + 1, hm, α => by
      have := JetRepG.orderedDerivative (h.2 (α 0)) (m := m) (by omega) (fun i => α i.succ)
      have e : (fun l => AVRegularity.orderedDerivative α (g l) 0) =
          fun l => AVRegularity.orderedDerivative (fun i => α i.succ) (dLabelG (α 0) g l) 0 :=
        funext fun l => by rw [orderedDerivative_succ]; rfl
      rw [e]; exact this

theorem jetRepG_const (hR : RepAlg R) : ∀ (r : ℕ) (c : ℝ), JetRepG R r (fun (_ : Λ) _ => c)
  | 0, c => hR.const c
  | r + 1, c => ⟨hR.const c, fun j => (jetRepG_const hR r 0).congr_germ fun _ =>
      Filter.Eventually.of_forall fun y => by simp [dLabelG]⟩

theorem JetRepG.add (hR : RepAlg R) : ∀ {r : ℕ} {g h : Λ → Vec 2 → ℝ},
    (∀ l, ContDiff ℝ r (g l)) → (∀ l, ContDiff ℝ r (h l)) →
    JetRepG R r g → JetRepG R r h → JetRepG R r (fun l y => g l y + h l y)
  | 0, _, _, _, _, hg, hh => hR.add hg hh
  | r + 1, g, h, cg, ch, hg, hh => ⟨hR.add hg.1 hh.1, fun j => by
      refine (JetRepG.add hR (r := r) (g := dLabelG j g) (h := dLabelG j h)
        (fun l => contDiff_dLabel (cg l) j) (fun l => contDiff_dLabel (ch l) j)
        (hg.2 j) (hh.2 j)).congr_germ fun l => Filter.Eventually.of_forall fun y => ?_
      simp only [dLabelG]
      rw [fderiv_fun_add ((cg l).differentiable (by norm_cast) y)
        ((ch l).differentiable (by norm_cast) y)]
      rfl⟩

theorem JetRepG.mul (hR : RepAlg R) : ∀ {r : ℕ} {g h : Λ → Vec 2 → ℝ},
    (∀ l, ContDiff ℝ r (g l)) → (∀ l, ContDiff ℝ r (h l)) →
    JetRepG R r g → JetRepG R r h → JetRepG R r (fun l y => g l y * h l y)
  | 0, _, _, _, _, hg, hh => hR.mul hg hh
  | r + 1, g, h, cg, ch, hg, hh => ⟨hR.mul hg.1 hh.1, fun j => by
      have cg' : ∀ l, ContDiff ℝ r (g l) := fun l => (cg l).of_le (by norm_cast; omega)
      have ch' : ∀ l, ContDiff ℝ r (h l) := fun l => (ch l).of_le (by norm_cast; omega)
      have cdg : ∀ l, ContDiff ℝ r (dLabelG j g l) := fun l => contDiff_dLabel (cg l) j
      have cdh : ∀ l, ContDiff ℝ r (dLabelG j h l) := fun l => contDiff_dLabel (ch l) j
      have h1 := JetRepG.mul hR cdg ch' (hg.2 j) (hh.mono (by omega))
      have h2 := JetRepG.mul hR cg' cdh (hg.mono (by omega)) (hh.2 j)
      refine (JetRepG.add hR (fun l => (cdg l).mul (ch' l)) (fun l => (cg' l).mul (cdh l)) h1 h2
        ).congr_germ fun l => Filter.Eventually.of_forall fun y => ?_
      simp only [dLabelG]
      rw [fderiv_fun_mul ((cg l).differentiable (by norm_cast) y)
        ((ch l).differentiable (by norm_cast) y)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring⟩

/-- **The chain rule for jets**: `g ∘ Ψ` for label maps with `Ψ 0 = 0`. -/
theorem JetRepG.comp (hR : RepAlg R) : ∀ {r : ℕ} {g : Λ → Vec 2 → ℝ} {Ψ : Λ → Vec 2 → Vec 2},
    (∀ l, Ψ l 0 = 0) → (∀ l, ContDiff ℝ r (g l)) → (∀ l, ContDiff ℝ r (Ψ l)) →
    JetRepG R r g → (∀ b, JetRepG R r (fun l y => Ψ l y b)) →
      JetRepG R r (fun l y => g l (Ψ l y))
  | 0, g, Ψ, h0, _, _, hg, _ => by
      have e : (fun l => g l (Ψ l 0)) = fun l => g l 0 := funext fun l => by rw [h0 l]
      show R (fun l => g l (Ψ l 0)); rw [e]; exact hg
  | r + 1, g, Ψ, h0, cg, cΨ, hg, hΨ => ⟨by
      have e : (fun l => g l (Ψ l 0)) = fun l => g l 0 := funext fun l => by rw [h0 l]
      rw [e]; exact hg.1, fun j => by
      have cΨ' : ∀ l, ContDiff ℝ r (Ψ l) := fun l => (cΨ l).of_le (by norm_cast; omega)
      have cΨb : ∀ b l, ContDiff ℝ (r + 1 : ℕ) (fun y => Ψ l y b) := fun b l =>
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) b).contDiff.comp (cΨ l)
      have hterm : ∀ b, JetRepG R r
          (fun l y => dLabelG b g l (Ψ l y) * dLabelG j (fun l y => Ψ l y b) l y) := by
        intro b
        have h1 := JetRepG.comp hR h0 (fun l => contDiff_dLabel (cg l) b) cΨ' (hg.2 b)
          (fun b' => (hΨ b').mono (by omega))
        exact JetRepG.mul hR (fun l => (contDiff_dLabel (cg l) b).comp (cΨ' l))
          (fun l => contDiff_dLabel (cΨb b l) j) h1 ((hΨ b).2 j)
      have hsum := JetRepG.add hR (fun l => ((contDiff_dLabel (cg l) 0).comp (cΨ' l)).mul
          (contDiff_dLabel (cΨb 0 l) j))
        (fun l => ((contDiff_dLabel (cg l) 1).comp (cΨ' l)).mul
          (contDiff_dLabel (cΨb 1 l) j)) (hterm 0) (hterm 1)
      refine hsum.congr_germ fun l => Filter.Eventually.of_forall fun y => ?_
      simp only [dLabelG]
      rw [fderiv_comp_label ((cg l).differentiable (by norm_cast) _)
        ((cΨ l).differentiable (by norm_cast) y) j, Fin.sum_univ_two]
      rfl⟩

/-! ### The family instance -/

/-- The family algebra on the window `W`: functions of the index that agree with a represented
family function. -/
def famAlg (D : OCData) (bw : ℝ) (j₀ : ℕ) (𝒮 : SeedExports) (i : ℕ) (p : ℤ)
    (W : Set (ℝ × RealChain)) : (W → ℝ) → Prop :=
  fun F => ∃ G : ℝ → RealChain → ℝ, (∀ q : W, F q = G q.1.1 q.1.2) ∧ IsFamRepOn D bw j₀ 𝒮 i p W G

theorem repAlg_famAlg (D : OCData) (bw : ℝ) (j₀ : ℕ) (𝒮 : SeedExports) (i : ℕ) (p : ℤ)
    (W : Set (ℝ × RealChain)) : RepAlg (famAlg D bw j₀ 𝒮 i p W) where
  const c := ⟨fun _ _ => c, fun _ => rfl, IsFamRepOn.const c⟩
  add := by
    rintro F G ⟨F', hF, hF'⟩ ⟨G', hG, hG'⟩
    exact ⟨_, fun q => by show F q + G q = _; rw [hF, hG], hF'.add hG'⟩
  mul := by
    rintro F G ⟨F', hF, hF'⟩ ⟨G', hG, hG'⟩
    exact ⟨_, fun q => by show F q * G q = _; rw [hF, hG], hF'.mul hG'⟩

variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {i : ℕ} {p : ℤ}
  {W : Set (ℝ × RealChain)}

/-- `JetRep` is the family instance of `JetRepG`. -/
theorem jetRep_toG : ∀ {r : ℕ} {g : ℝ → RealChain → Vec 2 → ℝ},
    JetRep D bw j₀ 𝒮 i p W r g →
      JetRepG (famAlg D bw j₀ 𝒮 i p W) r (fun q : W => g q.1.1 q.1.2)
  | 0, _, h => ⟨_, fun _ => rfl, h⟩
  | _ + 1, _, h => ⟨⟨_, fun _ => rfl, h.1⟩, fun j => jetRep_toG (h.2 j)⟩

/-- Represented family jets give represented family functions. -/
theorem famAlg_toFam {G : ℝ → RealChain → ℝ}
    (h : famAlg D bw j₀ 𝒮 i p W (fun q : W => G q.1.1 q.1.2)) : IsFamRepOn D bw j₀ 𝒮 i p W G := by
  obtain ⟨G', hG, hG'⟩ := h
  exact hG'.congr fun q hq => hG ⟨q, hq⟩
end

end AVRegularity.Providers.GenSem
end
