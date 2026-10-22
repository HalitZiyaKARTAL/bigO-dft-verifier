import Submission.Work.Mixed.HeadM1

/-!
# The full cut of heads in three groups (one rank per group)

`cut_heads_full3`: the head lemma (`GLiveKernelM.of_heads`, applied three times) and the cut target
(`cut_target_of`, `GLiveKernelM.cut_finish`) for a word `heads1 ++ (heads2 ++ (heads3 ++ body))` whose three head
groups sit on disjoint lists of live roles, each group with its own rank.  Every head is the block of the lines
`S l` of a frame `A l`; the body followed by one free shift per head role realises the block of the remaining
lines `(S l)ᶜ` on every head role and the kernel elsewhere, at every column count.
-- changed for the head-cut extension (1959540039/1000000000000); see Submission.lean
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.MX
open Binary GF Matrix Finset
noncomputable section

section Cut3
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] [DecidableEq σ]

/-- **Full cut, three head groups.** -/
theorem cut_heads_full3 {e : σ → ρ} (he : Function.Injective e)
    (L1 L2 L3 : List σ) (hL : (L1 ++ L2 ++ L3).Nodup) {r1 r2 r3 : ℕ}
    (z1 : σ → Fin r1 → Space α) (z2 : σ → Fin r2 → Space α) (z3 : σ → Fin r3 → Space α)
    (ind1 : ∀ l, LinearIndependent F (z1 l)) (ind2 : ∀ l, LinearIndependent F (z2 l))
    (ind3 : ∀ l, LinearIndependent F (z3 l)) (A : σ → OBase α) (S : σ → Finset α)
    (hz1 : ∀ l ∈ L1, ∀ x, bph (z1 l) x = bph ((A l).fam (S l)) x)
    (hz2 : ∀ l ∈ L2, ∀ x, bph (z2 l) x = bph ((A l).fam (S l)) x)
    (hz3 : ∀ l ∈ L3, ∀ x, bph (z3 l) x = bph ((A l).fam (S l)) x) (body : GWord α ρ)
    (hk : GLiveKernel e (headWord e L1 (fun _ => r1) z1 ind1 ++ (headWord e L2 (fun _ => r2) z2 ind2
      ++ (headWord e L3 (fun _ => r3) z3 ind3 ++ body)))) :
    GLiveKernelM e (fun l => blockMat (cutTgt (L1 ++ L2 ++ L3) A S l).2)
      (body ++ shiftWord e (L1 ++ L2 ++ L3) (cutShift A S)) := by
  obtain ⟨h12, h3n, d123⟩ := List.nodup_append.mp hL
  obtain ⟨h1n, h2n, d12⟩ := List.nodup_append.mp h12
  have n12 : ∀ l, l ∈ L1 → l ∉ L2 := fun l h1 h2 => d12 l h1 l h2 rfl
  have n13 : ∀ l, l ∈ L1 → l ∉ L3 := fun l h1 h3 => d123 l (List.mem_append_left _ h1) l h3 rfl
  have n23 : ∀ l, l ∈ L2 → l ∉ L3 := fun l h2 h3 => d123 l (List.mem_append_right _ h2) l h3 rfl
  have k1 := GLiveKernel.of_heads he L1 h1n (fun _ => r1) z1 ind1 _ hk
  have k2 := GLiveKernelM.of_heads he L2 h2n (fun _ => r2) z2 ind2 _ k1
  have k3 := GLiveKernelM.of_heads he L3 h3n (fun _ => r3) z3 ind3 body k2
  let U : σ → CMat α := fun l =>
    if l ∈ L1 then unblock (z1 l) else if l ∈ L2 then unblock (z2 l) else unblock (z3 l)
  have k4 : GLiveKernelM e (fun l => if l ∈ L1 ++ L2 ++ L3 then kernel α * U l else kernel α) body := by
    refine k3.congr (fun l => ?_)
    by_cases h1 : l ∈ L1
    · have h2 : l ∉ L2 := n12 l h1
      have h3 : l ∉ L3 := n13 l h1
      have hm : l ∈ L1 ++ L2 ++ L3 := List.mem_append_left _ (List.mem_append_left _ h1)
      simp only [U, if_pos h1, if_neg h2, if_neg h3, if_pos hm]
    · by_cases h2 : l ∈ L2
      · have h3 : l ∉ L3 := n23 l h2
        have hm : l ∈ L1 ++ L2 ++ L3 := List.mem_append_left _ (List.mem_append_right _ h2)
        simp only [U, if_neg h1, if_pos h2, if_neg h3, if_pos hm]
      · by_cases h3 : l ∈ L3
        · have hm : l ∈ L1 ++ L2 ++ L3 := List.mem_append_right _ h3
          simp only [U, if_neg h1, if_neg h2, if_pos h3, if_pos hm]
        · have hm : l ∉ L1 ++ L2 ++ L3 := by
            intro h
            rcases List.mem_append.mp h with h' | h'
            · rcases List.mem_append.mp h' with h'' | h''
              · exact h1 h''
              · exact h2 h''
            · exact h3 h'
          simp only [if_neg h1, if_neg h2, if_neg h3, if_neg hm]
  refine GLiveKernelM.cut_finish he (L1 ++ L2 ++ L3) hL A S U body (fun l hl => ?_) k4
  by_cases h1 : l ∈ L1
  · simp only [U, if_pos h1]
    exact cut_target_of (z1 l) (A l) (S l) (hz1 l h1)
  · by_cases h2 : l ∈ L2
    · simp only [U, if_neg h1, if_pos h2]
      exact cut_target_of (z2 l) (A l) (S l) (hz2 l h2)
    · have h3 : l ∈ L3 := by
        rcases List.mem_append.mp hl with h' | h'
        · rcases List.mem_append.mp h' with h'' | h''
          · exact absurd h'' h1
          · exact absurd h'' h2
        · exact h'
      simp only [U, if_neg h1, if_neg h2]
      exact cut_target_of (z3 l) (A l) (S l) (hz3 l h3)

end Cut3

/-! ## Histograms and properness of a word of three head groups -/

section Hist3
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

lemma proper_headWord3 (u : ℕ) (e : σ → ρ) (L1 L2 L3 : List σ) {r1 r2 r3 : ℕ}
    (z1 : σ → Fin r1 → Space α) (z2 : σ → Fin r2 → Space α) (z3 : σ → Fin r3 → Space α)
    (ind1 : ∀ l, LinearIndependent F (z1 l)) (ind2 : ∀ l, LinearIndependent F (z2 l))
    (ind3 : ∀ l, LinearIndependent F (z3 l)) (h1 : 1 ≤ r1) (h2 : 1 ≤ r2) (h3 : 1 ≤ r3)
    (hu1 : r1 < u) (hu2 : r2 < u) (hu3 : r3 < u) (body : GWord α ρ) (hP : body.Proper u) :
    GWord.Proper u (headWord e L1 (fun _ => r1) z1 ind1 ++ (headWord e L2 (fun _ => r2) z2 ind2
      ++ (headWord e L3 (fun _ => r3) z3 ind3 ++ body))) :=
  (proper_headWord u e L1 r1 z1 ind1 h1 hu1).append
    ((proper_headWord u e L2 r2 z2 ind2 h2 hu2).append ((proper_headWord u e L3 r3 z3 ind3 h3 hu3).append hP))

end Hist3

end
end PowerSaving.MX
end OAI

#print axioms OAI.PowerSaving.MX.cut_heads_full3
