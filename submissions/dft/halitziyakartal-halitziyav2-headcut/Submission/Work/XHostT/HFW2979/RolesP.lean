import Submission.Work.XHostT.TRoles
import Submission.Work.Block.Split

/-!
# (key: heads-first, three head kinds) The head roles of the A2, A3 and A4 bins

The role-level pieces of the heads-first certificate (`hroleT`, `headsL`, `hdHF`, `hdrop`, `sum_hdrop` of
Work/XHostT/HF/ToHF.lean), for the head bins of any of the three first-touch host kinds: A2 (host kind 0, data pair 2,
rank 16), A3 (host kind 2, data pair 3, rank 32) and A4 (host kind 4, data pair 4, rank 48).  The data pair is the
parameter `p` (2, 3 or 4); everything is the A4 file's, with `4` replaced by `p`.
-- changed for the head-cut extension (1959540039/1000000000000); see Submission.lean
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace OAI
namespace PowerSaving
namespace XHostT
open Binary Matrix Finset RAM SS CB RF BR GF GX XHost
noncomputable section

section RoleP
variable {Γ T : Type} {nb nR : ℕ}

/-- the head role of host bin `(ρ, j = (side, class))` of the head kind with data pair `p`, in gauge `g`. -/
def hroleP (p : ℕ) (ρ : Fin nR) (g : Γ) (j : Bool × T) : BLiveT Γ T nb nR := Sum.inl (ρ, dD p j.1 (g, j.2))

lemma hroleP_inj {p : ℕ} (hp : 1 ≤ p ∧ p ≤ 4) {ρ ρ' : Fin nR} {g g' : Γ} {j j' : Bool × T}
    (h : (hroleP p ρ g j : BLiveT Γ T nb nR) = hroleP p ρ' g' j') : ρ = ρ' ∧ g = g' ∧ j = j' := by
  simp only [hroleP, Sum.inl.injEq, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨-, hs, hk⟩ := dD_inj hp hp h2
  obtain ⟨hg, ht⟩ := Prod.mk.inj hk
  exact ⟨h1, hg, Prod.ext hs ht⟩

/-- head roles of different data pairs are different. -/
lemma hroleP_ne {p q : ℕ} (hp : 1 ≤ p ∧ p ≤ 4) (hq : 1 ≤ q ∧ q ≤ 4) (hpq : p ≠ q) (ρ ρ' : Fin nR) (g g' : Γ)
    (j j' : Bool × T) : (hroleP p ρ g j : BLiveT Γ T nb nR) ≠ hroleP q ρ' g' j' := by
  intro h
  simp only [hroleP, Sum.inl.injEq, Prod.mk.injEq] at h
  exact hpq (dD_inj hp hq h.2).1

/-- a live data role of pair `q ≠ p` is no head role of pair `p`. -/
lemma hroleP_ne_pair {p q : ℕ} (hp : 1 ≤ p ∧ p ≤ 4) (hq : 1 ≤ q ∧ q ≤ 4) (hpq : q ≠ p) (ρ ρ' : Fin nR) (s : Bool)
    (k : Γ × T) (g : Γ) (j : Bool × T) : (Sum.inl (ρ, dD q s k) : BLiveT Γ T nb nR) ≠ hroleP p ρ' g j := by
  intro h
  simp only [hroleP, Sum.inl.injEq, Prod.mk.injEq] at h
  exact hpq (dD_inj hq hp h.2).1

/-- a bank role is no head role. -/
lemma hroleP_ne_bank (p : ℕ) (gb : Γ × Fin nb) (ρ' : Fin nR) (g : Γ) (j : Bool × T) :
    (Sum.inr gb : BLiveT Γ T nb nR) ≠ hroleP p ρ' g j := by
  intro h
  simp [hroleP] at h

variable [Fintype Γ] [DecidableEq Γ] [DecidableEq T]

/-- the head roles of the bins `hb` of pair `p`, every gauge. -/
def headsFP (p : ℕ) (hb : Finset (Fin nR × Bool × T)) : Finset (BLiveT Γ T nb nR) :=
  (hb ×ˢ (Finset.univ : Finset Γ)).image (fun x => (hroleP p x.1.1 x.2 x.1.2 : BLiveT Γ T nb nR))

/-- the head list of pair `p` (duplicate free; one entry per head bin and gauge). -/
def headsLP (p : ℕ) (hb : Finset (Fin nR × Bool × T)) : List (BLiveT Γ T nb nR) := (headsFP p hb).toList

lemma headsLP_nodup (p : ℕ) (hb : Finset (Fin nR × Bool × T)) : (headsLP (Γ := Γ) (nb := nb) p hb).Nodup :=
  Finset.nodup_toList _

lemma mem_headsLP (p : ℕ) (hb : Finset (Fin nR × Bool × T)) (l : BLiveT Γ T nb nR) :
    l ∈ headsLP p hb ↔ ∃ x ∈ hb, ∃ g, hroleP p x.1 g x.2 = l := by
  simp only [headsLP, headsFP, Finset.mem_toList, Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨⟨x, g⟩, hx, e⟩
    exact ⟨x, hx, g, e⟩
  · rintro ⟨x, hx, g, e⟩
    exact ⟨⟨x, g⟩, hx, e⟩

lemma mem_headsLP_iff {p : ℕ} (hp : 1 ≤ p ∧ p ≤ 4) (hb : Finset (Fin nR × Bool × T)) (ρ : Fin nR) (g : Γ)
    (j : Bool × T) : (hroleP p ρ g j : BLiveT Γ T nb nR) ∈ headsLP p hb ↔ (ρ, j) ∈ hb := by
  rw [mem_headsLP]
  constructor
  · rintro ⟨x, hx, g', e⟩
    obtain ⟨h1, -, h3⟩ := hroleP_inj hp e
    rw [← h1, ← h3]
    exact hx
  · intro h
    exact ⟨(ρ, j), h, g, rfl⟩

lemma headsLP_length {p : ℕ} (hp : 1 ≤ p ∧ p ≤ 4) (hb : Finset (Fin nR × Bool × T)) :
    (headsLP (Γ := Γ) (nb := nb) p hb).length = hb.card * Fintype.card Γ := by
  rw [headsLP, Finset.length_toList, headsFP, Finset.card_image_of_injective, Finset.card_product, Finset.card_univ]
  rintro ⟨⟨ρ, j⟩, g⟩ ⟨⟨ρ', j'⟩, g'⟩ e
  obtain ⟨h1, h2, h3⟩ := hroleP_inj hp e
  simp only at h1 h2 h3
  rw [h1, h2, h3]

/-- head lists of different pairs are disjoint. -/
lemma headsLP_disj {p q : ℕ} (hp : 1 ≤ p ∧ p ≤ 4) (hq : 1 ≤ q ∧ q ≤ 4) (hpq : p ≠ q)
    (hb hb' : Finset (Fin nR × Bool × T)) :
    ∀ a ∈ headsLP (Γ := Γ) (nb := nb) p hb, ∀ b ∈ headsLP (Γ := Γ) (nb := nb) q hb', a ≠ b := by
  intro a ha b hb2 e
  obtain ⟨x, -, g, rfl⟩ := (mem_headsLP p hb a).1 ha
  obtain ⟨x', -, g', rfl⟩ := (mem_headsLP q hb' b).1 hb2
  exact hroleP_ne hp hq hpq _ _ _ _ _ _ e

/-- every role of the head list of pair `p` is the data role of pair `p` of its replica. -/
lemma headsLP_pair {p : ℕ} (hb : Finset (Fin nR × Bool × T)) (l : BLiveT Γ T nb nR)
    (hl : l ∈ headsLP p hb) : ∃ ρ s k, l = Sum.inl (ρ, dD p s k) := by
  obtain ⟨x, -, g, rfl⟩ := (mem_headsLP p hb l).1 hl
  exact ⟨x.1, x.2.1, (g, x.2.2), rfl⟩

variable {α : Type} [Fintype α] [DecidableEq α]

/-- the head pre-factor of pair `p`: the head block on head bins, `1` elsewhere. -/
def hdHFP (p : ℕ) (hb : Finset (Fin nR × Bool × T)) {n : ℕ} (z : BLiveT Γ T nb nR → Fin n → Space α)
    (ρ : Fin nR) (g : Γ) (j : Bool × T) : CMat α :=
  if (ρ, j) ∈ hb then blockMat (z (hroleP p ρ g j)) else 1

/-- the price dropped from the climbs of replica `ρ` of a head kind of rank `r`: one `φ r` per head bin of `ρ`. -/
def hdropR [Fintype T] (r : ℕ) (hb : Finset (Fin nR × Bool × T)) (ρ : Fin nR) (φ : ℕ → ℝ) : ℝ :=
  ∑ t : T, ((if (ρ, (false, t)) ∈ hb then φ r else 0) + (if (ρ, (true, t)) ∈ hb then φ r else 0))

lemma sum_hdropR [Fintype T] (r : ℕ) (hb : Finset (Fin nR × Bool × T)) (φ : ℕ → ℝ) :
    ∑ ρ : Fin nR, hdropR r hb ρ φ = (hb.card : ℝ) * φ r := by
  have e : ∑ ρ : Fin nR, hdropR r hb ρ φ = ∑ x : Fin nR × Bool × T, (if x ∈ hb then φ r else 0) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro ρ _
    rw [Fintype.sum_prod_type, Fintype.sum_bool, hdropR, Finset.sum_add_distrib, add_comm]
  rw [e, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

end RoleP
end
end XHostT
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.XHostT.headsLP_length
#print axioms OAI.PowerSaving.XHostT.sum_hdropR
