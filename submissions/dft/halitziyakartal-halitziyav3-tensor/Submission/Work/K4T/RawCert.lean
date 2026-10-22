import Submission.Work.K4T.Hole
import Submission.Work.P4L.LFRaw
-- changed for the tensor-power extension (26159999/10000000000); see Submission.lean

/-!
# Route B: the RAW certificate with `G` copies exists (closes hole H2)

p3-port's `OAI.PowerSaving.P4L.LF.rawCert_exists` (module P4L/LFRaw; every helper ends on its residual rank, no pad, no split; targets
`TrawLF`, paid `PrawLF` per gauge copy) is `PB.K4T.RawCertG` up to its extra conjunct `∀ l, 1 ≤ tr l ∧ tr l ≤ 73` and
the names of the two lists (`TrawLF = rawTgtB`, `PrawLF = rawPaidB`, the same literals).
-/

namespace OAI
namespace PowerSaving
namespace PB
namespace K4T

lemma rawTgtB_eq_TrawLF : rawTgtB = P4L.LF.TrawLF := rfl
lemma rawPaidB_eq_PrawLF : rawPaidB = P4L.LF.PrawLF := rfl

/-- **Hole H2, proved.** -/
theorem rawCertG_ex : ∃ (α ρ σ : Type) (_ : Fintype α) (_ : DecidableEq α) (_ : Fintype ρ) (_ : DecidableEq ρ)
    (_ : Fintype σ) (_ : DecidableEq σ), RawCertG α ρ σ := by
  obtain ⟨α, ρ, σ, i1, i2, i3, i4, i5, i6, e, tr, tz, wd, G, he, hind, hP, hw, hG, hα, -, hcnt, hhist⟩ :=
    P4L.LF.rawCert_exists
  refine ⟨α, ρ, σ, i1, i2, i3, i4, i5, i6, ?_⟩
  unfold RawCertG
  refine ⟨e, tr, tz, wd, G, he, hind, hP, hw, hG, hα, fun r => ?_, fun r => ?_⟩
  · rw [rawTgtB_eq_TrawLF]; exact hcnt r
  · rw [rawPaidB_eq_PrawLF]; exact hhist r

end K4T
end PB
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.PB.K4T.rawCertG_ex
